// residual proof checker
// catalog: leaf extensions > center encodings > exact shape sets
// records: edge sets > placements > earlier children > complete roots
#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <limits.h>
#include <math.h>
#include <poll.h>
#include <signal.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

enum { MAX_ORDER = 13, CODE_SIZE = 2 * MAX_ORDER + 1,
       INPUT_SIZE = 1 << 20, NODE_BLOCK_BITS = 16,
       NODE_BLOCK_SIZE = 1 << NODE_BLOCK_BITS, NODE_BLOCK_COUNT = 1 << 16 };

typedef struct {
    uint64_t lower;
    uint16_t upper;
} EdgeSet;

typedef struct {
    uint64_t lower;
    uint16_t upper;
    uint8_t level;
} VerifiedNode;

typedef struct {
    uint8_t parents[MAX_ORDER - 1];
    uint8_t maximum_degree;
    char shape[CODE_SIZE];
    uint32_t seen_node;
    bool assigned_root;
    bool seen_root;
} Tree;

typedef struct {
    Tree *trees;
    size_t count;
} Catalog;

typedef struct {
    int descriptor;
    unsigned char buffer[INPUT_SIZE];
    size_t cursor;
    size_t available;
    uint64_t loaded;
    uint64_t consumed;
    uint64_t byte_limit;
    bool eof;
} Reader;

typedef struct {
    Reader input;
    Catalog catalogs[MAX_ORDER + 1];
    VerifiedNode *node_blocks[NODE_BLOCK_COUNT];
    EdgeSet edge_masks[MAX_ORDER][MAX_ORDER];
    uint8_t edge_first[MAX_ORDER * (MAX_ORDER - 1) / 2];
    uint8_t edge_second[MAX_ORDER * (MAX_ORDER - 1) / 2];
    EdgeSet complete;
    uint64_t nodes;
    uint64_t placements;
    unsigned order;
    unsigned first_top;
    unsigned last_top;
    unsigned roots;
} Checker;

static volatile sig_atomic_t interrupted;
static bool deadline_enabled;
static double deadline;
static uint32_t deadline_steps;

static _Noreturn void fail(const char *format, ...) {
    va_list arguments;
    fputs("check_proof_independent: ", stderr);
    va_start(arguments, format);
    vfprintf(stderr, format, arguments);
    va_end(arguments);
    fputc('\n', stderr);
    exit(EXIT_FAILURE);
}

static double monotonic_seconds(void) {
    struct timespec now;
    if (clock_gettime(CLOCK_MONOTONIC, &now) != 0)
        fail("cannot read monotonic clock: %s", strerror(errno));
    return (double)now.tv_sec + (double)now.tv_nsec / 1000000000.0;
}

static void check_limits(void) {
    if (interrupted)
        fail("interrupted by signal %d", (int)interrupted);
    if (deadline_enabled && monotonic_seconds() >= deadline)
        fail("time limit exceeded");
}

static void placement_limits(void) {
    if (interrupted)
        fail("interrupted by signal %d", (int)interrupted);
    if ((++deadline_steps & 65535u) == 0)
        check_limits();
}

static void interrupt_handler(int signal_number) {
    interrupted = signal_number;
}

static void install_signals(void) {
    struct sigaction action;
    memset(&action, 0, sizeof(action));
    action.sa_handler = interrupt_handler;
    if (sigemptyset(&action.sa_mask) != 0 ||
        sigaction(SIGINT, &action, NULL) != 0 ||
        sigaction(SIGTERM, &action, NULL) != 0 ||
        sigaction(SIGHUP, &action, NULL) != 0)
        fail("cannot install signal handlers: %s", strerror(errno));
}

static void *allocate(size_t count, size_t size) {
    if (size != 0 && count > SIZE_MAX / size)
        fail("allocation size overflow");
    void *memory = calloc(count, size);
    if (!memory)
        fail("cannot allocate %zu bytes", count * size);
    return memory;
}

static void wait_for_input(int descriptor) {
    if (!deadline_enabled)
        return;
    for (;;) {
        check_limits();
        double remaining = deadline - monotonic_seconds();
        int milliseconds = remaining >= 1.0 ? 1000 :
            (remaining <= 0.0 ? 0 : (int)(remaining * 1000.0) + 1);
        struct pollfd event = { descriptor, POLLIN, 0 };
        int result = poll(&event, 1, milliseconds);
        if (result > 0) {
            if (event.revents & POLLNVAL)
                fail("invalid input descriptor");
            return;
        }
        if (result < 0 && errno != EINTR)
            fail("cannot wait for input: %s", strerror(errno));
    }
}

static bool fill_input(Reader *input, size_t needed) {
    size_t remaining = input->available - input->cursor;
    if (remaining >= needed)
        return true;
    if (input->cursor != 0 && remaining != 0)
        memmove(input->buffer, input->buffer + input->cursor, remaining);
    input->cursor = 0;
    input->available = remaining;
    while (input->available < needed && !input->eof) {
        check_limits();
        wait_for_input(input->descriptor);
        size_t capacity = INPUT_SIZE - input->available;
        uint64_t allowance = input->byte_limit - input->loaded;
        if (allowance < capacity)
            capacity = (size_t)allowance + 1;
        ssize_t received = read(input->descriptor,
                                input->buffer + input->available, capacity);
        if (received < 0) {
            if (errno == EINTR)
                continue;
            fail("input read failed: %s", strerror(errno));
        }
        if (received == 0) {
            input->eof = true;
            break;
        }
        if ((uint64_t)received > input->byte_limit - input->loaded)
            fail("proof byte limit exceeded");
        input->loaded += (uint64_t)received;
        input->available += (size_t)received;
    }
    return input->available >= needed;
}

static const unsigned char *take_bytes(Reader *input, size_t count) {
    if (input->available - input->cursor < count && !fill_input(input, count))
        fail("truncated proof at byte %" PRIu64, input->consumed);
    const unsigned char *result = input->buffer + input->cursor;
    input->cursor += count;
    input->consumed += count;
    return result;
}

static unsigned decode_u16(const unsigned char *bytes) {
    return (unsigned)bytes[0] | (unsigned)bytes[1] << 8;
}

static uint32_t decode_u32(const unsigned char *bytes) {
    return (uint32_t)bytes[0] | (uint32_t)bytes[1] << 8 |
        (uint32_t)bytes[2] << 16 | (uint32_t)bytes[3] << 24;
}

static uint64_t decode_u64(const unsigned char *bytes) {
    return (uint64_t)decode_u32(bytes) | (uint64_t)decode_u32(bytes + 4) << 32;
}

static unsigned read_u16(Reader *input) {
    return decode_u16(take_bytes(input, 2));
}

static int compare_codes(const void *left, const void *right) {
    return strcmp((const char *)left, (const char *)right);
}

static size_t rooted_code(unsigned vertex, unsigned parent,
                          const uint16_t *neighbors, char *result) {
    char children[MAX_ORDER][CODE_SIZE];
    size_t child_count = 0;
    uint16_t pending = neighbors[vertex];
    if (parent < MAX_ORDER)
        pending &= (uint16_t)~(1u << parent);
    while (pending != 0) {
        unsigned child = (unsigned)__builtin_ctz((unsigned)pending);
        pending &= (uint16_t)(pending - 1);
        rooted_code(child, vertex, neighbors, children[child_count++]);
    }
    qsort(children, child_count, sizeof(children[0]), compare_codes);
    size_t position = 0;
    result[position++] = '(';
    for (size_t index = 0; index < child_count; ++index) {
        size_t length = strlen(children[index]);
        memcpy(result + position, children[index], length);
        position += length;
    }
    result[position++] = ')';
    result[position] = '\0';
    return position;
}

static void describe_tree(Tree *tree, unsigned order) {
    uint16_t neighbors[MAX_ORDER] = { 0 };
    unsigned degrees[MAX_ORDER] = { 0 };
    for (unsigned vertex = 1; vertex < order; ++vertex) {
        unsigned parent = tree->parents[vertex - 1];
        neighbors[vertex] |= (uint16_t)(1u << parent);
        neighbors[parent] |= (uint16_t)(1u << vertex);
        ++degrees[vertex];
        ++degrees[parent];
    }
    tree->maximum_degree = 0;
    for (unsigned vertex = 0; vertex < order; ++vertex)
        if (degrees[vertex] > tree->maximum_degree)
            tree->maximum_degree = (uint8_t)degrees[vertex];
    uint16_t active = (uint16_t)((1u << order) - 1);
    unsigned remaining = order;
    while (remaining > 2) {
        uint16_t leaves = 0;
        for (unsigned vertex = 0; vertex < order; ++vertex)
            if ((active & (1u << vertex)) && degrees[vertex] == 1)
                leaves |= (uint16_t)(1u << vertex);
        active &= (uint16_t)~leaves;
        remaining -= (unsigned)__builtin_popcount((unsigned)leaves);
        while (leaves != 0) {
            unsigned leaf = (unsigned)__builtin_ctz((unsigned)leaves);
            leaves &= (uint16_t)(leaves - 1);
            uint16_t adjacent = neighbors[leaf] & active;
            while (adjacent != 0) {
                unsigned vertex = (unsigned)__builtin_ctz((unsigned)adjacent);
                adjacent &= (uint16_t)(adjacent - 1);
                --degrees[vertex];
            }
        }
    }
    unsigned center = (unsigned)__builtin_ctz((unsigned)active);
    rooted_code(center, MAX_ORDER, neighbors, tree->shape);
    active &= (uint16_t)(active - 1);
    if (active != 0) {
        char alternative[CODE_SIZE];
        center = (unsigned)__builtin_ctz((unsigned)active);
        rooted_code(center, MAX_ORDER, neighbors, alternative);
        if (strcmp(alternative, tree->shape) < 0)
            strcpy(tree->shape, alternative);
    }
}

static int compare_trees(const void *left, const void *right) {
    const Tree *first = left;
    const Tree *second = right;
    return strcmp(first->shape, second->shape);
}

static Catalog extend_catalog(const Catalog *previous, unsigned order) {
    Catalog result = { NULL, previous->count * (order - 1) };
    result.trees = allocate(result.count, sizeof(Tree));
    size_t position = 0;
    for (size_t index = 0; index < previous->count; ++index) {
        for (unsigned parent = 0; parent < order - 1; ++parent) {
            Tree *tree = &result.trees[position++];
            memcpy(tree->parents, previous->trees[index].parents, order - 2);
            tree->parents[order - 2] = (uint8_t)parent;
            describe_tree(tree, order);
        }
        if ((index & 63u) == 0)
            check_limits();
    }
    qsort(result.trees, result.count, sizeof(Tree), compare_trees);
    size_t distinct = 0;
    for (size_t index = 0; index < result.count; ++index) {
        if (distinct == 0 || strcmp(result.trees[index].shape,
                                    result.trees[distinct - 1].shape) != 0)
            result.trees[distinct++] = result.trees[index];
    }
    result.count = distinct;
    return result;
}

static void read_catalog(Checker *checker, const Catalog *expected, unsigned order) {
    Catalog *catalog = &checker->catalogs[order];
    catalog->count = read_u16(&checker->input);
    if (catalog->count != expected->count)
        fail("incomplete tree catalog at order %u: got %zu, expected %zu",
             order, catalog->count, expected->count);
    catalog->trees = allocate(catalog->count, sizeof(Tree));
    bool *seen = allocate(expected->count, sizeof(bool));
    for (size_t index = 0; index < catalog->count; ++index) {
        Tree *tree = &catalog->trees[index];
        const unsigned char *parents = take_bytes(&checker->input, order - 1);
        for (unsigned vertex = 1; vertex < order; ++vertex) {
            if (parents[vertex - 1] >= vertex)
                fail("invalid parent in order-%u tree %zu", order, index);
            tree->parents[vertex - 1] = parents[vertex - 1];
        }
        describe_tree(tree, order);
        Tree *match = bsearch(tree, expected->trees, expected->count,
                              sizeof(Tree), compare_trees);
        if (!match)
            fail("unknown tree shape at order %u", order);
        size_t shape_index = (size_t)(match - expected->trees);
        if (seen[shape_index])
            fail("duplicate tree shape at order %u", order);
        seen[shape_index] = true;
    }
    free(seen);
}

static void read_header(Checker *checker) {
    if (memcmp(take_bytes(&checker->input, 8), "TPCRDP01", 8) != 0)
        fail("invalid proof magic");
    checker->order = take_bytes(&checker->input, 1)[0];
    if (checker->order < 2 || checker->order > MAX_ORDER)
        fail("host order outside 2..13");
    checker->first_top = read_u16(&checker->input);
    checker->last_top = read_u16(&checker->input);
    if (checker->first_top >= checker->last_top)
        fail("empty or reversed top range");
    Catalog expected = { allocate(1, sizeof(Tree)), 1 };
    describe_tree(expected.trees, 1);
    for (unsigned order = 2; order <= checker->order; ++order) {
        Catalog next = extend_catalog(&expected, order);
        free(expected.trees);
        expected = next;
        read_catalog(checker, &expected, order);
    }
    free(expected.trees);
    Catalog *top = &checker->catalogs[checker->order];
    if (checker->last_top > top->count)
        fail("top range exceeds catalog");
    unsigned position = 0;
    for (unsigned degree = checker->order - 1; degree > 0; --degree) {
        for (size_t index = 0; index < top->count; ++index) {
            if (top->trees[index].maximum_degree != degree)
                continue;
            if (position >= checker->first_top && position < checker->last_top) {
                if (read_u16(&checker->input) != index)
                    fail("incorrect top ordering at position %u", position);
                top->trees[index].assigned_root = true;
            }
            ++position;
        }
    }
    unsigned edge = 0;
    for (unsigned first = 0; first < checker->order; ++first) {
        for (unsigned second = first + 1; second < checker->order; ++second) {
            EdgeSet mask = { 0, 0 };
            if (edge < 64)
                mask.lower = UINT64_C(1) << edge;
            else
                mask.upper = (uint16_t)(1u << (edge - 64));
            checker->edge_masks[first][second] = mask;
            checker->edge_masks[second][first] = mask;
            checker->edge_first[edge] = (uint8_t)first;
            checker->edge_second[edge] = (uint8_t)second;
            checker->complete.lower |= mask.lower;
            checker->complete.upper |= mask.upper;
            ++edge;
        }
    }
}

static const VerifiedNode *find_node(const Checker *checker, uint32_t identifier) {
    uint32_t position = identifier - 1;
    return &checker->node_blocks[position >> NODE_BLOCK_BITS]
        [position & (NODE_BLOCK_SIZE - 1)];
}

static void store_node(Checker *checker, EdgeSet edges, unsigned level) {
    uint64_t position = checker->nodes;
    size_t block = (size_t)(position >> NODE_BLOCK_BITS);
    size_t offset = (size_t)(position & (NODE_BLOCK_SIZE - 1));
    if (offset == 0)
        checker->node_blocks[block] = allocate(NODE_BLOCK_SIZE, sizeof(VerifiedNode));
    VerifiedNode *node = &checker->node_blocks[block][offset];
    node->lower = edges.lower;
    node->upper = edges.upper;
    node->level = (uint8_t)level;
    ++checker->nodes;
}

static void verify_placement(Checker *checker, unsigned level, EdgeSet host,
                             uint32_t node_stamp) {
    placement_limits();
    const unsigned char *record = take_bytes(&checker->input, level + checker->order + 6);
    unsigned tree_index = decode_u16(record);
    Catalog *catalog = &checker->catalogs[level];
    if (tree_index >= catalog->count)
        fail("tree index outside order-%u catalog", level);
    Tree *tree = &catalog->trees[tree_index];
    if (node_stamp != 0) {
        if (tree->seen_node == node_stamp)
            fail("duplicate tree obligation in node %" PRIu32, node_stamp);
        tree->seen_node = node_stamp;
    } else {
        if (!tree->assigned_root || tree->seen_root)
            fail("unassigned or duplicate root tree %u", tree_index);
        tree->seen_root = true;
    }
    const unsigned char *images = record + 2;
    uint32_t child_identifier = decode_u32(images + level);
    const unsigned char *labels = images + level + 4;
    unsigned seen_images = 0;
    for (unsigned vertex = 0; vertex < level; ++vertex) {
        unsigned image = images[vertex];
        if (image >= checker->order || (seen_images & (1u << image)))
            fail("invalid or repeated image vertex");
        seen_images |= 1u << image;
    }
    EdgeSet removed = { 0, 0 };
    for (unsigned vertex = 1; vertex < level; ++vertex) {
        EdgeSet edge = checker->edge_masks[images[vertex]][images[tree->parents[vertex - 1]]];
        removed.lower |= edge.lower;
        removed.upper |= edge.upper;
    }
    if ((removed.lower & host.lower) != removed.lower ||
        (removed.upper & host.upper) != removed.upper)
        fail("tree placement uses an absent edge");
    EdgeSet remainder = { host.lower ^ removed.lower,
                          (uint16_t)(host.upper ^ removed.upper) };
    unsigned seen_labels = 0;
    for (unsigned vertex = 0; vertex < checker->order; ++vertex) {
        unsigned label = labels[vertex];
        if (label >= checker->order || (seen_labels & (1u << label)))
            fail("child labels are not a permutation");
        seen_labels |= 1u << label;
    }
    if (child_identifier == 0) {
        if (level > 3)
            fail("nonterminal placement has zero child");
    } else {
        if (level <= 3 || child_identifier > checker->nodes)
            fail("child does not reference an earlier verified node");
        const VerifiedNode *child = find_node(checker, child_identifier);
        if (child->level != level - 1)
            fail("child has incorrect level");
        EdgeSet mapped = { 0, 0 };
        uint64_t lower = child->lower;
        while (lower != 0) {
            unsigned edge_index = (unsigned)__builtin_ctzll(lower);
            lower &= lower - 1;
            EdgeSet edge = checker->edge_masks[labels[checker->edge_first[edge_index]]]
                                              [labels[checker->edge_second[edge_index]]];
            mapped.lower |= edge.lower;
            mapped.upper |= edge.upper;
        }
        unsigned upper = child->upper;
        while (upper != 0) {
            unsigned edge_index = 64u + (unsigned)__builtin_ctz(upper);
            upper &= upper - 1;
            EdgeSet edge = checker->edge_masks[labels[checker->edge_first[edge_index]]]
                                              [labels[checker->edge_second[edge_index]]];
            mapped.lower |= edge.lower;
            mapped.upper |= edge.upper;
        }
        if (mapped.lower != remainder.lower || mapped.upper != remainder.upper)
            fail("relabelled child differs from exact remainder");
    }
    ++checker->placements;
}

static void verify_records(Checker *checker) {
    for (;;) {
        unsigned kind = take_bytes(&checker->input, 1)[0];
        if (kind == 1) {
            if (checker->nodes == UINT32_MAX)
                fail("node identifier limit exceeded");
            const unsigned char *record = take_bytes(&checker->input, 11);
            unsigned level = record[0];
            if (level < 3 || level >= checker->order)
                fail("invalid node level %u", level);
            EdgeSet edges = { decode_u64(record + 1), (uint16_t)decode_u16(record + 9) };
            if ((edges.lower & ~checker->complete.lower) != 0 ||
                (edges.upper & ~checker->complete.upper) != 0)
                fail("node has unused edge bits set");
            unsigned edge_count = (unsigned)__builtin_popcountll(edges.lower) +
                (unsigned)__builtin_popcount((unsigned)edges.upper);
            if (edge_count != level * (level - 1) / 2)
                fail("incorrect node edge count");
            uint32_t node_stamp = (uint32_t)(checker->nodes + 1);
            for (size_t index = 0; index < checker->catalogs[level].count; ++index)
                verify_placement(checker, level, edges, node_stamp);
            store_node(checker, edges, level);
        } else if (kind == 2) {
            verify_placement(checker, checker->order, checker->complete, 0);
            ++checker->roots;
        } else if (kind == 3) {
            unsigned declared_roots = read_u16(&checker->input);
            if (declared_roots != checker->roots ||
                checker->roots != checker->last_top - checker->first_top)
                fail("incomplete root coverage or incorrect footer count");
            Catalog *top = &checker->catalogs[checker->order];
            for (size_t index = 0; index < top->count; ++index)
                if (top->trees[index].assigned_root != top->trees[index].seen_root)
                    fail("incomplete root coverage");
            if (fill_input(&checker->input, 1))
                fail("trailing bytes after footer");
            check_limits();
            return;
        } else {
            fail("invalid record kind %u", kind);
        }
    }
}

static double positive_number(const char *text, const char *option) {
    char *end = NULL;
    errno = 0;
    double value = strtod(text, &end);
    if (errno != 0 || end == text || *end != '\0' || !isfinite(value) || value <= 0)
        fail("%s requires a finite positive number", option);
    return value;
}

int main(int argument_count, char **arguments) {
    double started = monotonic_seconds();
    if (argument_count < 2)
        fail("usage: %s FILE [--seconds POSITIVE] [--max-mib POSITIVE]", arguments[0]);
    Checker *checker = allocate(1, sizeof(Checker));
    checker->input.byte_limit = UINT64_MAX;
    bool byte_limit_set = false;
    for (int index = 2; index < argument_count; index += 2) {
        if (index + 1 >= argument_count)
            fail("missing value for %s", arguments[index]);
        double value = positive_number(arguments[index + 1], arguments[index]);
        if (strcmp(arguments[index], "--seconds") == 0) {
            if (deadline_enabled || !isfinite(started + value))
                fail("duplicate or excessive time limit");
            deadline_enabled = true;
            deadline = started + value;
        } else if (strcmp(arguments[index], "--max-mib") == 0) {
            double bytes = value * 1048576.0;
            if (byte_limit_set || !isfinite(bytes) || bytes < 1.0 || bytes >= 18446744073709551616.0)
                fail("duplicate or excessive proof byte limit");
            checker->input.byte_limit = (uint64_t)bytes;
            byte_limit_set = true;
        } else {
            fail("unknown option %s", arguments[index]);
        }
    }
    install_signals();
    check_limits();
    checker->input.descriptor = open(arguments[1], O_RDONLY | O_NONBLOCK);
    if (checker->input.descriptor < 0)
        fail("cannot open proof: %s", strerror(errno));
    int flags = fcntl(checker->input.descriptor, F_GETFL);
    if (flags < 0 || fcntl(checker->input.descriptor, F_SETFL, flags & ~O_NONBLOCK) != 0)
        fail("cannot configure proof input: %s", strerror(errno));
    read_header(checker);
    verify_records(checker);
    if (close(checker->input.descriptor) != 0)
        fail("cannot close proof input: %s", strerror(errno));
    printf("{\"status\":\"verified\",\"n\":%u,\"top_first\":%u,\"top_last\":%u,"
           "\"roots\":%u,\"nodes\":%" PRIu64 ",\"placements\":%" PRIu64
           ",\"proof_bytes\":%" PRIu64 "}\n",
           checker->order, checker->first_top, checker->last_top,
           checker->roots, checker->nodes, checker->placements, checker->input.consumed);
    if (fflush(stdout) != 0)
        fail("cannot write verdict: %s", strerror(errno));
    for (size_t index = 0; index < NODE_BLOCK_COUNT; ++index)
        free(checker->node_blocks[index]);
    for (unsigned order = 2; order <= checker->order; ++order)
        free(checker->catalogs[order].trees);
    free(checker);
    return EXIT_SUCCESS;
}
