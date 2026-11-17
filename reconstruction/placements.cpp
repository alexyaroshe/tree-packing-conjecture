// placement-only codec
// stored tree embedding > residual > canonical child lookup > ordinary proof
// original graph/header/order preservation > two unchanged checkers
#define _POSIX_C_SOURCE 200809L

#include <nauty.h>
#include <algorithm>
#include <array>
#include <cerrno>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fcntl.h>
#include <limits>
#include <memory>
#include <poll.h>
#include <signal.h>
#include <stdexcept>
#include <string>
#include <time.h>
#include <unistd.h>
#include <unordered_map>
#include <vector>

namespace {

constexpr unsigned maximum_order = 12;
constexpr size_t buffer_size = 1u << 20;
constexpr char compact_magic[] = "TPCEPC01";
constexpr char proof_magic[] = "TPCRDP01";

volatile sig_atomic_t interrupted = 0;
bool deadline_enabled = false;
double deadline = 0;
uint32_t placement_steps = 0;

[[noreturn]] void fail(const std::string &message) {
    throw std::runtime_error(message);
}

[[noreturn]] void system_failure(const char *operation) {
    fail(std::string(operation) + ": " + std::strerror(errno));
}

double monotonic_seconds() {
    timespec now{};
    if (clock_gettime(CLOCK_MONOTONIC, &now) != 0)
        system_failure("monotonic clock");
    return static_cast<double>(now.tv_sec) + static_cast<double>(now.tv_nsec) / 1e9;
}

void check_limits() {
    if (interrupted)
        fail("interrupted by signal " + std::to_string(interrupted));
    if (deadline_enabled && monotonic_seconds() >= deadline)
        fail("time limit exceeded");
}

void placement_limits() {
    if (interrupted)
        fail("interrupted by signal " + std::to_string(interrupted));
    if ((++placement_steps & 65535u) == 0)
        check_limits();
}

void handle_signal(int signal_number) {
    interrupted = signal_number;
}

void install_signals() {
    struct sigaction action{};
    action.sa_handler = handle_signal;
    if (sigemptyset(&action.sa_mask) != 0 ||
        sigaction(SIGINT, &action, nullptr) != 0 ||
        sigaction(SIGTERM, &action, nullptr) != 0 ||
        sigaction(SIGHUP, &action, nullptr) != 0)
        system_failure("install signal handlers");
    action.sa_handler = SIG_IGN;
    if (sigaction(SIGPIPE, &action, nullptr) != 0)
        system_failure("ignore broken pipe signal");
}

void wait_descriptor(int descriptor, short events) {
    for (;;) {
        check_limits();
        int milliseconds = -1;
        if (deadline_enabled) {
            double remaining = deadline - monotonic_seconds();
            milliseconds = remaining >= 1.0 ? 1000 :
                (remaining <= 0.0 ? 0 : static_cast<int>(remaining * 1000.0) + 1);
        }
        pollfd event{descriptor, events, 0};
        int result = poll(&event, 1, milliseconds);
        if (result > 0) {
            if (event.revents & POLLNVAL)
                fail("invalid file descriptor");
            return;
        }
        if (result < 0 && errno != EINTR)
            system_failure("wait for input or output");
    }
}

class Reader {
    int descriptor_;
    std::vector<uint8_t> buffer_ = std::vector<uint8_t>(buffer_size);
    size_t cursor_ = 0;
    size_t available_ = 0;
    uint64_t consumed_ = 0;
    bool eof_ = false;

    bool fill(size_t needed) {
        size_t remaining = available_ - cursor_;
        if (remaining >= needed)
            return true;
        if (cursor_ && remaining)
            std::memmove(buffer_.data(), buffer_.data() + cursor_, remaining);
        cursor_ = 0;
        available_ = remaining;
        while (available_ < needed && !eof_) {
            check_limits();
            if (deadline_enabled)
                wait_descriptor(descriptor_, POLLIN);
            ssize_t count = read(descriptor_, buffer_.data() + available_, buffer_size - available_);
            if (count < 0) {
                if (errno == EINTR)
                    continue;
                if (errno == EAGAIN || errno == EWOULDBLOCK) {
                    wait_descriptor(descriptor_, POLLIN);
                    continue;
                }
                system_failure("read input");
            }
            if (count == 0) {
                eof_ = true;
                break;
            }
            available_ += static_cast<size_t>(count);
        }
        return available_ >= needed;
    }

public:
    explicit Reader(const char *path) : descriptor_(open(path, O_RDONLY | O_NONBLOCK)) {
        if (descriptor_ < 0)
            system_failure("open input");
    }

    ~Reader() { close(descriptor_); }

    const uint8_t *take(size_t count) {
        if (available_ - cursor_ < count && !fill(count))
            fail("truncated input at byte " + std::to_string(consumed_));
        const uint8_t *result = buffer_.data() + cursor_;
        cursor_ += count;
        consumed_ += count;
        return result;
    }

    uint8_t byte() { return *take(1); }
    uint64_t consumed() const { return consumed_; }

    void require_eof() {
        if (fill(1))
            fail("trailing input bytes");
        check_limits();
    }
};

class OutputFile {
    std::string path_;
    bool committed_ = false;

public:
    int descriptor;

    explicit OutputFile(const char *path) : path_(path),
        descriptor(open(path, O_WRONLY | O_CREAT | O_EXCL, 0666)) {
        if (descriptor < 0)
            system_failure("create exclusive output");
    }

    ~OutputFile() {
        if (descriptor >= 0)
            close(descriptor);
        if (!committed_)
            unlink(path_.c_str());
    }

    void commit() {
        if (close(descriptor) != 0) {
            descriptor = -1;
            system_failure("close output");
        }
        descriptor = -1;
        committed_ = true;
    }
};

class Writer {
    int descriptor_;
    int original_flags_;
    std::vector<uint8_t> buffer_ = std::vector<uint8_t>(buffer_size);
    size_t used_ = 0;
    uint64_t produced_ = 0;
    uint64_t limit_;

public:
    Writer(int descriptor, uint64_t limit) : descriptor_(descriptor),
        original_flags_(fcntl(descriptor, F_GETFL)), limit_(limit) {
        if (original_flags_ < 0 || fcntl(descriptor_, F_SETFL, original_flags_ | O_NONBLOCK) != 0)
            system_failure("configure output");
    }

    ~Writer() { fcntl(descriptor_, F_SETFL, original_flags_); }

    void flush() {
        size_t position = 0;
        while (position < used_) {
            check_limits();
            ssize_t count = write(descriptor_, buffer_.data() + position, used_ - position);
            if (count < 0) {
                if (errno == EINTR)
                    continue;
                if (errno == EAGAIN || errno == EWOULDBLOCK) {
                    wait_descriptor(descriptor_, POLLOUT);
                    continue;
                }
                system_failure("write output");
            }
            if (count == 0)
                fail("zero-length output write");
            position += static_cast<size_t>(count);
        }
        used_ = 0;
    }

    void append(const uint8_t *bytes, size_t count) {
        if (count > limit_ - produced_)
            fail("output byte limit exceeded");
        produced_ += count;
        while (count) {
            if (used_ == buffer_size)
                flush();
            size_t portion = std::min(count, buffer_size - used_);
            std::memcpy(buffer_.data() + used_, bytes, portion);
            used_ += portion;
            bytes += portion;
            count -= portion;
        }
    }

    void byte(uint8_t value) {
        if (produced_ == limit_)
            fail("output byte limit exceeded");
        if (used_ == buffer_size)
            flush();
        buffer_[used_++] = value;
        ++produced_;
    }

    void finish() { flush(); check_limits(); }
    uint64_t produced() const { return produced_; }
};

class BitWriter {
    Writer &output_;
    uint64_t pending_ = 0;
    unsigned width_ = 0;

public:
    explicit BitWriter(Writer &output) : output_(output) {}

    void put(uint32_t value, unsigned width) {
        pending_ |= static_cast<uint64_t>(value) << width_;
        width_ += width;
        while (width_ >= 8) {
            output_.byte(static_cast<uint8_t>(pending_));
            pending_ >>= 8;
            width_ -= 8;
        }
    }

    void finish() {
        if (width_)
            output_.byte(static_cast<uint8_t>(pending_));
        width_ = 0;
        pending_ = 0;
    }
};

class BitReader {
    Reader &input_;
    uint64_t pending_ = 0;
    unsigned width_ = 0;

public:
    explicit BitReader(Reader &input) : input_(input) {}

    uint32_t get(unsigned width) {
        while (width_ < width) {
            pending_ |= static_cast<uint64_t>(input_.byte()) << width_;
            width_ += 8;
        }
        uint64_t mask = (uint64_t{1} << width) - 1;
        uint32_t result = static_cast<uint32_t>(pending_ & mask);
        pending_ >>= width;
        width_ -= width;
        return result;
    }

    void finish() {
        if (pending_ != 0)
            fail("nonzero final padding bits");
        input_.require_eof();
    }
};

unsigned u16(const uint8_t *bytes) {
    return static_cast<unsigned>(bytes[0]) | static_cast<unsigned>(bytes[1]) << 8;
}

uint32_t u32(const uint8_t *bytes) {
    return static_cast<uint32_t>(bytes[0]) | static_cast<uint32_t>(bytes[1]) << 8 |
        static_cast<uint32_t>(bytes[2]) << 16 | static_cast<uint32_t>(bytes[3]) << 24;
}

uint64_t u64(const uint8_t *bytes) {
    return u32(bytes) | static_cast<uint64_t>(u32(bytes + 4)) << 32;
}

void store_u16(uint8_t *bytes, unsigned value) {
    bytes[0] = static_cast<uint8_t>(value);
    bytes[1] = static_cast<uint8_t>(value >> 8);
}

void store_u32(uint8_t *bytes, uint32_t value) {
    for (unsigned index = 0; index < 4; ++index)
        bytes[index] = static_cast<uint8_t>(value >> (8 * index));
}

void store_u64(uint8_t *bytes, uint64_t value) {
    store_u32(bytes, static_cast<uint32_t>(value));
    store_u32(bytes + 4, static_cast<uint32_t>(value >> 32));
}

unsigned field_width(uint64_t possibilities) {
    unsigned result = 0;
    for (uint64_t value = possibilities - 1; value; value >>= 1)
        ++result;
    return result;
}

using Adjacency = std::array<uint16_t, maximum_order>;

struct Graph {
    Adjacency adjacency;
    std::array<uint8_t, maximum_order> degree;
    std::array<uint8_t, maximum_order> vertex_order;
    uint8_t active_count;
    uint8_t level;
};
static_assert(sizeof(Graph) <= 52, "bounded stored graphs");

Graph make_graph(uint64_t lower, unsigned upper, unsigned order, unsigned level) {
    Graph graph{};
    graph.level = static_cast<uint8_t>(level);
    unsigned bit = 0;
    for (unsigned first = 0; first < order; ++first)
        for (unsigned second = first + 1; second < order; ++second, ++bit) {
            bool edge = bit < 64 ? ((lower >> bit) & 1u) : ((upper >> (bit - 64)) & 1u);
            if (edge) {
                graph.adjacency[first] |= 1u << second;
                graph.adjacency[second] |= 1u << first;
                ++graph.degree[first];
                ++graph.degree[second];
            }
        }
    unsigned active = 0;
    for (unsigned vertex = 0; vertex < order; ++vertex)
        if (graph.degree[vertex])
            active |= 1u << vertex;
    unsigned selected = 0;
    while (active != selected) {
        unsigned best = maximum_order, best_links = 0, best_degree = 0;
        for (unsigned vertex = 0; vertex < order; ++vertex) {
            if (!(active & (1u << vertex)) || (selected & (1u << vertex)))
                continue;
            unsigned links = static_cast<unsigned>(__builtin_popcount(graph.adjacency[vertex] & selected));
            if (best == maximum_order || links > best_links ||
                (links == best_links && graph.degree[vertex] > best_degree)) {
                best = vertex;
                best_links = links;
                best_degree = graph.degree[vertex];
            }
        }
        graph.vertex_order[graph.active_count++] = static_cast<uint8_t>(best);
        selected |= 1u << best;
    }
    return graph;
}

std::array<uint16_t, maximum_order + 1> degree_masks(const Graph &host, unsigned order) {
    std::array<uint16_t, maximum_order + 1> result{};
    for (unsigned vertex = 0; vertex < order; ++vertex)
        result[host.degree[vertex]] |= 1u << vertex;
    for (unsigned degree = order - 1; degree > 0; --degree)
        result[degree - 1] |= result[degree];
    return result;
}

class NodeStore {
    static constexpr uint32_t block_bits = 16;
    static constexpr uint32_t block_size = 1u << block_bits;
    std::vector<std::unique_ptr<Graph[]>> blocks_;
    uint32_t count_ = 0;

public:
    uint32_t size() const { return count_; }
    const Graph &at(uint32_t identifier) const {
        if (!identifier || identifier > count_)
            fail("child is not an earlier node");
        --identifier;
        return blocks_[identifier >> block_bits][identifier & (block_size - 1)];
    }
    void append(const Graph &graph) {
        if (count_ >= UINT32_MAX - 1)
            fail("node identifier limit exceeded");
        if ((count_ & (block_size - 1)) == 0)
            blocks_.emplace_back(new Graph[block_size]);
        blocks_[count_ >> block_bits][count_ & (block_size - 1)] = graph;
        ++count_;
    }
};

struct Tree {
    std::array<uint8_t, maximum_order> parents{};
    Graph graph;
};

struct Catalog {
    std::vector<uint16_t> tree_order;
    std::vector<Tree> trees;
};

struct Header {
    unsigned order = 0;
    unsigned first_top = 0;
    unsigned last_top = 0;
    std::array<Catalog, maximum_order + 1> catalogs;
    std::vector<uint16_t> root_order;
};

Header copy_header(Reader &input, Writer &output) {
    auto transfer = [&](size_t count) {
        const uint8_t *bytes = input.take(count);
        output.append(bytes, count);
        return bytes;
    };
    if (std::memcmp(transfer(8), proof_magic, 8) != 0)
        fail("invalid original proof magic");
    Header header;
    header.order = *transfer(1);
    if (header.order < 2 || header.order > maximum_order)
        fail("host order outside 2..12");
    header.first_top = u16(transfer(2));
    header.last_top = u16(transfer(2));
    if (header.first_top >= header.last_top)
        fail("empty or reversed top range");
    for (unsigned level = 2; level <= header.order; ++level) {
        unsigned count = u16(transfer(2));
        if (count == 0)
            fail("empty tree catalog");
        std::vector<unsigned> maximum_degrees(count);
        auto &tree_order = header.catalogs[level].tree_order;
        tree_order.resize(count);
        header.catalogs[level].trees.resize(count);
        for (unsigned index = 0; index < count; ++index) {
            std::array<unsigned, maximum_order> degrees{};
            Adjacency adjacency{};
            Tree &tree = header.catalogs[level].trees[index];
            const uint8_t *parents = transfer(level - 1);
            for (unsigned vertex = 1; vertex < level; ++vertex) {
                if (parents[vertex - 1] >= vertex)
                    fail("invalid catalog parent");
                ++degrees[vertex];
                ++degrees[parents[vertex - 1]];
                tree.parents[vertex] = parents[vertex - 1];
                adjacency[vertex] |= 1u << parents[vertex - 1];
                adjacency[parents[vertex - 1]] |= 1u << vertex;
            }
            uint64_t lower = 0;
            unsigned upper = 0, bit = 0;
            for (unsigned first = 0; first < header.order; ++first)
                for (unsigned second = first + 1; second < header.order; ++second, ++bit)
                    if (adjacency[first] & (1u << second)) {
                        if (bit < 64) lower |= uint64_t{1} << bit;
                        else upper |= 1u << (bit - 64);
                    }
            tree.graph = make_graph(lower, upper, header.order, level);
            maximum_degrees[index] = *std::max_element(degrees.begin(), degrees.end());
            tree_order[index] = static_cast<uint16_t>(index);
        }
        std::sort(tree_order.begin(), tree_order.end(), [&](uint16_t left, uint16_t right) {
            if (maximum_degrees[left] != maximum_degrees[right])
                return maximum_degrees[left] > maximum_degrees[right];
            return left < right;
        });
        check_limits();
    }
    const auto &top_order = header.catalogs[header.order].tree_order;
    if (header.last_top > top_order.size())
        fail("top range exceeds catalog");
    for (unsigned position = header.first_top; position < header.last_top; ++position) {
        unsigned index = u16(transfer(2));
        if (index != top_order[position])
            fail("incorrect assigned top ordering");
        header.root_order.push_back(static_cast<uint16_t>(index));
    }
    return header;
}

class RankTables {
    unsigned order_;
    std::vector<std::array<uint8_t, maximum_order>> selections_;

public:
    std::array<uint32_t, maximum_order + 1> possibilities{};
    std::array<unsigned, maximum_order + 1> widths{};

    explicit RankTables(unsigned order) : order_(order), selections_(1u << order) {
        possibilities[0] = 1;
        for (unsigned count = 1; count <= order; ++count) {
            possibilities[count] = possibilities[count - 1] * (order - count + 1);
            widths[count] = field_width(possibilities[count]);
        }
        for (unsigned mask = 0; mask < (1u << order); ++mask) {
            unsigned position = 0;
            for (unsigned vertex = 0; vertex < order; ++vertex)
                if (mask & (1u << vertex))
                    selections_[mask][position++] = static_cast<uint8_t>(vertex);
        }
    }

    unsigned select(unsigned mask, unsigned rank) const {
        if (rank >= static_cast<unsigned>(__builtin_popcount(mask)))
            fail("label choice outside candidate set");
        return selections_[mask][rank];
    }

    uint32_t rank(const uint8_t *vertices, unsigned count) const {
        unsigned remaining = (1u << order_) - 1;
        uint32_t result = 0;
        for (unsigned position = 0; position < count; ++position) {
            unsigned vertex = vertices[position];
            if (vertex >= order_ || !(remaining & (1u << vertex)))
                fail("invalid or repeated vertex in ranked field");
            unsigned earlier = static_cast<unsigned>(__builtin_popcount(remaining & ((1u << vertex) - 1)));
            result = result * (order_ - position) + earlier;
            remaining &= ~(1u << vertex);
        }
        return result;
    }

    void unrank(uint32_t rank, unsigned count, uint8_t *vertices) const {
        if (rank >= possibilities[count])
            fail("rank exceeds injective field range");
        std::array<uint8_t, maximum_order> digits{};
        for (unsigned position = count; position > 0; --position) {
            unsigned radix = order_ - position + 1;
            digits[position - 1] = static_cast<uint8_t>(rank % radix);
            rank /= radix;
        }
        unsigned remaining = (1u << order_) - 1;
        for (unsigned position = 0; position < count; ++position) {
            unsigned vertex = selections_[remaining][digits[position]];
            vertices[position] = static_cast<uint8_t>(vertex);
            remaining &= ~(1u << vertex);
        }
    }
};

struct GraphKey {
    uint64_t lower = 0;
    uint16_t upper = 0;
    bool operator==(const GraphKey &other) const {
        return lower == other.lower && upper == other.upper;
    }
};

GraphKey graph_key(const Adjacency &adjacency, unsigned order) {
    GraphKey key;
    unsigned bit = 0;
    for (unsigned first = 0; first < order; ++first)
        for (unsigned second = first + 1; second < order; ++second, ++bit)
            if (adjacency[first] & (1u << second)) {
                if (bit < 64) key.lower |= uint64_t{1} << bit;
                else key.upper |= 1u << (bit - 64);
            }
    return key;
}

struct GraphHash {
    size_t operator()(const GraphKey &key) const {
        uint64_t value = key.lower ^ (uint64_t{key.upper} * UINT64_C(0x9e3779b97f4a7c15));
        value ^= value >> 30;
        value *= UINT64_C(0xbf58476d1ce4e5b9);
        value ^= value >> 27;
        value *= UINT64_C(0x94d049bb133111eb);
        return static_cast<size_t>(value ^ (value >> 31));
    }
};

uint64_t reverse_bits(uint64_t value) {
    value = ((value & UINT64_C(0x5555555555555555)) << 1) | ((value >> 1) & UINT64_C(0x5555555555555555));
    value = ((value & UINT64_C(0x3333333333333333)) << 2) | ((value >> 2) & UINT64_C(0x3333333333333333));
    value = ((value & UINT64_C(0x0f0f0f0f0f0f0f0f)) << 4) | ((value >> 4) & UINT64_C(0x0f0f0f0f0f0f0f0f));
    value = ((value & UINT64_C(0x00ff00ff00ff00ff)) << 8) | ((value >> 8) & UINT64_C(0x00ff00ff00ff00ff));
    value = ((value & UINT64_C(0x0000ffff0000ffff)) << 16) | ((value >> 16) & UINT64_C(0x0000ffff0000ffff));
    return (value << 32) | (value >> 32);
}

struct CanonicalGraph {
    GraphKey key;
    std::array<uint8_t, maximum_order> original_labels{};
};

CanonicalGraph canonicalize(const Adjacency &adjacency, unsigned order) {
    std::array<uint8_t, maximum_order> active_labels{}, compact_labels{}, isolated_labels{};
    unsigned active = 0, isolated = 0;
    for (unsigned vertex = 0; vertex < order; ++vertex) {
        if (adjacency[vertex]) {
            compact_labels[vertex] = static_cast<uint8_t>(active);
            active_labels[active++] = static_cast<uint8_t>(vertex);
        } else isolated_labels[isolated++] = static_cast<uint8_t>(vertex);
    }
    CanonicalGraph result;
    for (unsigned vertex = 0; vertex < isolated; ++vertex)
        result.original_labels[vertex] = isolated_labels[vertex];
    if (!active) return result;
    graph input[maximum_order]{}, canonical[maximum_order]{};
    int labels[maximum_order], partition[maximum_order], orbits[maximum_order];
    static_assert(WORDSIZE == 32 || WORDSIZE == 64, "supported nauty word sizes");
    for (unsigned vertex = 0; vertex < active; ++vertex) {
        unsigned remaining = adjacency[active_labels[vertex]], row = 0;
        while (remaining) {
            unsigned neighbor = static_cast<unsigned>(__builtin_ctz(remaining));
            remaining &= remaining - 1;
            row |= 1u << compact_labels[neighbor];
        }
        input[vertex] = static_cast<setword>(reverse_bits(row) >> (64 - WORDSIZE));
    }
    DEFAULTOPTIONS_GRAPH(options);
    options.getcanon = TRUE;
    statsblk statistics{};
    densenauty(input, labels, partition, orbits, &options, &statistics, 1,
              static_cast<int>(active), canonical);
    if (statistics.errstatus) fail("nauty canonicalization failed");
    Adjacency normalized{};
    for (unsigned vertex = 0; vertex < active; ++vertex) {
        result.original_labels[vertex + isolated] = active_labels[labels[vertex]];
        normalized[vertex + isolated] = static_cast<uint16_t>(
            (reverse_bits(canonical[vertex]) >> (64 - WORDSIZE)) << isolated);
    }
    result.key = graph_key(normalized, order);
    return result;
}

struct ChildReference {
    uint32_t identifier;
    std::array<uint8_t, maximum_order> canonical_labels;
};

struct Counters {
    NodeStore nodes;
    std::unordered_map<GraphKey, ChildReference, GraphHash> canonical_nodes;
    uint64_t placements = 0;
    uint64_t canonical_calls = 0;
    uint64_t embedding_choice_bits = 0;
    uint64_t forced_embedding_choices = 0;
    unsigned roots = 0;
};

const Graph *check_child(uint32_t child, unsigned level, const Counters &counts) {
    if (child == 0) {
        if (level > 3)
            fail("zero child at a nonterminal level");
        return nullptr;
    }
    if (level <= 3)
        fail("nonzero terminal child");
    const Graph &graph = counts.nodes.at(child);
    if (graph.level != level - 1)
        fail("incorrect child level");
    return &graph;
}

void check_node(unsigned level, uint64_t lower, unsigned upper, unsigned order,
                const Counters &counts) {
    if (level < 3 || level >= order)
        fail("invalid node level");
    if (counts.nodes.size() >= UINT32_MAX - 1)
        fail("node identifier limit exceeded");
    unsigned edges = order * (order - 1) / 2;
    uint64_t lower_mask = edges >= 64 ? UINT64_MAX : (uint64_t{1} << edges) - 1;
    unsigned upper_mask = edges > 64 ? (1u << (edges - 64)) - 1 : 0;
    if ((lower & ~lower_mask) || (upper & ~upper_mask))
        fail("unused graph bits are set");
    unsigned edge_count = static_cast<unsigned>(__builtin_popcountll(lower)) +
        static_cast<unsigned>(__builtin_popcount(upper));
    if (edge_count != level * (level - 1) / 2)
        fail("incorrect node edge count");
}

Adjacency removed_tree(const Graph &host, const Graph &child, const uint8_t *labels) {
    Adjacency result = host.adjacency;
    for (unsigned position = 0; position < child.active_count; ++position) {
        unsigned vertex = child.vertex_order[position];
        unsigned image = labels[vertex], mapped_edges = 0;
        unsigned neighbors = child.adjacency[vertex];
        while (neighbors) {
            unsigned neighbor = static_cast<unsigned>(__builtin_ctz(neighbors));
            neighbors &= neighbors - 1;
            mapped_edges |= 1u << labels[neighbor];
        }
        if (mapped_edges & ~result[image])
            fail("mapped child is not a subgraph of its parent");
        result[image] &= static_cast<uint16_t>(~mapped_edges);
    }
    return result;
}

Adjacency embedding_edges(const Tree &tree, const uint8_t *images, unsigned level) {
    Adjacency result{};
    for (unsigned vertex = 1; vertex < level; ++vertex) {
        unsigned first = images[vertex], second = images[tree.parents[vertex]];
        result[first] |= 1u << second;
        result[second] |= 1u << first;
    }
    return result;
}

void validate_terminal(const Graph &host, const Adjacency &edges, unsigned order) {
    for (unsigned vertex = 0; vertex < order; ++vertex)
        if (edges[vertex] & ~host.adjacency[vertex])
            fail("terminal tree edge is missing from its host");
}

unsigned embedding_candidates(const Tree &tree, unsigned vertex, const Graph &host,
                              const std::array<uint16_t, maximum_order + 1> &degrees,
                              unsigned mapped, unsigned unused, const uint8_t *images) {
    unsigned candidates = degrees[tree.graph.degree[vertex]] & unused;
    unsigned neighbors = tree.graph.adjacency[vertex] & mapped;
    while (neighbors) {
        unsigned neighbor = static_cast<unsigned>(__builtin_ctz(neighbors));
        neighbors &= neighbors - 1;
        candidates &= host.adjacency[images[neighbor]];
    }
    if (!candidates) fail("empty embedding candidate set");
    return candidates;
}

void encode_embedding(BitWriter &bits, const Tree &tree, const Graph &host,
                      const std::array<uint16_t, maximum_order + 1> &degrees,
                      unsigned order, const uint8_t *images, Counters &counts) {
    unsigned mapped = 0, unused = (1u << order) - 1;
    for (unsigned position = 0; position < tree.graph.active_count; ++position) {
        unsigned vertex = tree.graph.vertex_order[position];
        unsigned candidates = embedding_candidates(tree, vertex, host, degrees, mapped, unused, images);
        unsigned image = images[vertex];
        if (!(candidates & (1u << image))) fail("input embedding violates graph constraints");
        unsigned width = field_width(static_cast<unsigned>(__builtin_popcount(candidates)));
        unsigned rank = static_cast<unsigned>(__builtin_popcount(candidates & ((1u << image) - 1)));
        bits.put(rank, width);
        counts.embedding_choice_bits += width;
        counts.forced_embedding_choices += width == 0;
        unused &= ~(1u << image);
        mapped |= 1u << vertex;
    }
}

void decode_embedding(BitReader &bits, const Tree &tree, const Graph &host,
                      const std::array<uint16_t, maximum_order + 1> &degrees,
                      const RankTables &ranks, unsigned order, uint8_t *images, Counters &counts) {
    unsigned mapped = 0, unused = (1u << order) - 1;
    for (unsigned position = 0; position < tree.graph.active_count; ++position) {
        unsigned vertex = tree.graph.vertex_order[position];
        unsigned candidates = embedding_candidates(tree, vertex, host, degrees, mapped, unused, images);
        unsigned width = field_width(static_cast<unsigned>(__builtin_popcount(candidates)));
        unsigned image = ranks.select(candidates, bits.get(width));
        images[vertex] = static_cast<uint8_t>(image);
        counts.embedding_choice_bits += width;
        counts.forced_embedding_choices += width == 0;
        unused &= ~(1u << image);
        mapped |= 1u << vertex;
    }
}

void encode_placement(Reader &input, BitWriter &bits, const Header &header,
                      const RankTables &ranks, Counters &counts, unsigned level,
                      uint16_t expected_tree, const Graph &host,
                      const std::array<uint16_t, maximum_order + 1> &degree_sets) {
    placement_limits();
    const uint8_t *record = input.take(level + header.order + 6);
    if (u16(record) != expected_tree) fail("placement tree order cannot be omitted");
    ranks.rank(record + 2, level);
    uint32_t child = u32(record + 2 + level);
    const Graph *child_graph = check_child(child, level, counts);
    const uint8_t *labels = record + 6 + level;
    ranks.rank(labels, header.order);
    const Tree &tree = header.catalogs[level].trees[expected_tree];
    Adjacency edges = embedding_edges(tree, record + 2, level);
    if (!child_graph) validate_terminal(host, edges, header.order);
    else if (removed_tree(host, *child_graph, labels) != edges)
        fail("input embedding differs from parent minus mapped child");
    encode_embedding(bits, tree, host, degree_sets, header.order, record + 2, counts);
    ++counts.placements;
}

void decode_placement(BitReader &bits, Writer &output, const Header &header,
                      const RankTables &ranks, Counters &counts, unsigned level,
                      uint16_t expected_tree, const Graph &host,
                      const std::array<uint16_t, maximum_order + 1> &degree_sets) {
    placement_limits();
    std::array<uint8_t, 2 * maximum_order + 6> record{};
    store_u16(record.data(), expected_tree);
    uint8_t *images = record.data() + 2, *labels = record.data() + 6 + level;
    const Tree &tree = header.catalogs[level].trees[expected_tree];
    decode_embedding(bits, tree, host, degree_sets, ranks, header.order, images, counts);
    Adjacency edges = embedding_edges(tree, images, level);
    validate_terminal(host, edges, header.order);
    uint32_t child = 0;
    if (level <= 3) {
        for (unsigned vertex = 0; vertex < header.order; ++vertex)
            labels[vertex] = static_cast<uint8_t>(vertex);
    } else {
        Adjacency residual = host.adjacency;
        for (unsigned vertex = 0; vertex < header.order; ++vertex)
            residual[vertex] &= static_cast<uint16_t>(~edges[vertex]);
        ++counts.canonical_calls;
        CanonicalGraph canonical = canonicalize(residual, header.order);
        auto found = counts.canonical_nodes.find(canonical.key);
        if (found == counts.canonical_nodes.end()) fail("residual has no earlier canonical child");
        child = found->second.identifier;
        const Graph *child_graph = check_child(child, level, counts);
        for (unsigned vertex = 0; vertex < header.order; ++vertex)
            labels[found->second.canonical_labels[vertex]] = canonical.original_labels[vertex];
        if (removed_tree(host, *child_graph, labels) != edges)
            fail("canonical child relabelling differs from residual");
    }
    store_u32(record.data() + 2 + level, child);
    output.append(record.data(), level + header.order + 6);
    ++counts.placements;
}

void check_footer(unsigned roots, const Header &header, const Counters &counts) {
    if (roots != counts.roots || roots != header.root_order.size())
        fail("incomplete root coverage or incorrect footer count");
}

Counters encode(Reader &input, Writer &output, const Header &header) {
    RankTables ranks(header.order);
    BitWriter bits(output);
    Counters counts;
    unsigned graph_width = header.order * (header.order - 1) / 2;
    Graph complete = make_graph(graph_width >= 64 ? UINT64_MAX : (uint64_t{1} << graph_width) - 1,
                                graph_width > 64 ? (1u << (graph_width - 64)) - 1 : 0, header.order, header.order);
    auto complete_degrees = degree_masks(complete, header.order);
    for (;;) {
        unsigned kind = input.byte();
        if (kind < 1 || kind > 3)
            fail("invalid raw record kind");
        bits.put(kind, 2);
        if (kind == 1) {
            const uint8_t *record = input.take(11);
            unsigned level = record[0];
            uint64_t lower = u64(record + 1);
            unsigned upper = u16(record + 9);
            check_node(level, lower, upper, header.order, counts);
            bits.put(level, 4);
            unsigned first_width = std::min(graph_width, 32u);
            bits.put(static_cast<uint32_t>(lower), first_width);
            if (graph_width > 32)
                bits.put(static_cast<uint32_t>(lower >> 32), std::min(graph_width - 32, 32u));
            if (graph_width > 64)
                bits.put(upper, graph_width - 64);
            Graph host = make_graph(lower, upper, header.order, level);
            auto degrees = degree_masks(host, header.order);
            for (uint16_t tree : header.catalogs[level].tree_order)
                encode_placement(input, bits, header, ranks, counts, level, tree, host, degrees);
            counts.nodes.append(host);
        } else if (kind == 2) {
            if (counts.roots == header.root_order.size())
                fail("too many roots");
            encode_placement(input, bits, header, ranks, counts, header.order,
                             header.root_order[counts.roots], complete, complete_degrees);
            ++counts.roots;
        } else {
            unsigned roots = u16(input.take(2));
            check_footer(roots, header, counts);
            input.require_eof();
            bits.put(roots, 16);
            bits.finish();
            return counts;
        }
    }
}

Counters decode(Reader &input, Writer &output, const Header &header) {
    RankTables ranks(header.order);
    BitReader bits(input);
    Counters counts;
    unsigned graph_width = header.order * (header.order - 1) / 2;
    Graph complete = make_graph(graph_width >= 64 ? UINT64_MAX : (uint64_t{1} << graph_width) - 1,
                                graph_width > 64 ? (1u << (graph_width - 64)) - 1 : 0, header.order, header.order);
    auto complete_degrees = degree_masks(complete, header.order);
    for (;;) {
        unsigned kind = bits.get(2);
        if (kind < 1 || kind > 3)
            fail("invalid compact record kind");
        output.byte(static_cast<uint8_t>(kind));
        if (kind == 1) {
            unsigned level = bits.get(4);
            uint64_t lower = bits.get(std::min(graph_width, 32u));
            if (graph_width > 32)
                lower |= static_cast<uint64_t>(bits.get(std::min(graph_width - 32, 32u))) << 32;
            unsigned upper = graph_width > 64 ? bits.get(graph_width - 64) : 0;
            check_node(level, lower, upper, header.order, counts);
            std::array<uint8_t, 11> record{};
            record[0] = static_cast<uint8_t>(level);
            store_u64(record.data() + 1, lower);
            store_u16(record.data() + 9, upper);
            output.append(record.data(), record.size());
            Graph host = make_graph(lower, upper, header.order, level);
            auto degrees = degree_masks(host, header.order);
            for (uint16_t tree : header.catalogs[level].tree_order)
                decode_placement(bits, output, header, ranks, counts, level, tree, host, degrees);
            counts.nodes.append(host);
            ++counts.canonical_calls;
            CanonicalGraph canonical = canonicalize(host.adjacency, header.order);
            counts.canonical_nodes.emplace(canonical.key, ChildReference{counts.nodes.size(), canonical.original_labels});
        } else if (kind == 2) {
            if (counts.roots == header.root_order.size())
                fail("too many roots");
            decode_placement(bits, output, header, ranks, counts, header.order,
                             header.root_order[counts.roots], complete, complete_degrees);
            ++counts.roots;
        } else {
            unsigned roots = bits.get(16);
            check_footer(roots, header, counts);
            std::array<uint8_t, 2> record{};
            store_u16(record.data(), roots);
            output.append(record.data(), record.size());
            bits.finish();
            return counts;
        }
    }
}

long double positive_number(const char *text, const char *option) {
    char *end = nullptr;
    errno = 0;
    long double value = std::strtold(text, &end);
    if (errno || end == text || *end || !std::isfinite(value) || value <= 0)
        fail(std::string(option) + " requires a finite positive number");
    return value;
}

void print_statistics(const char *status, const Header &header, const Counters &counts,
                      const Reader &input, const Writer &output) {
    if (std::fprintf(stderr,
        "{\"status\":\"%s\",\"input_bytes\":%llu,\"output_bytes\":%llu,"
        "\"n\":%u,\"nodes\":%llu,\"placements\":%llu,\"canonical_calls\":%llu,\"embedding_choice_bits\":%llu,\"forced_embedding_choices\":%llu}\n",
        status, static_cast<unsigned long long>(input.consumed()),
        static_cast<unsigned long long>(output.produced()), header.order,
        static_cast<unsigned long long>(counts.nodes.size()),
        static_cast<unsigned long long>(counts.placements),
        static_cast<unsigned long long>(counts.canonical_calls),
        static_cast<unsigned long long>(counts.embedding_choice_bits),
        static_cast<unsigned long long>(counts.forced_embedding_choices)) < 0)
        system_failure("write statistics");
}

}

int main(int argument_count, char **arguments) {
    try {
        double started = monotonic_seconds();
        if (argument_count < 3)
            fail("usage: placement_codec encode INPUT OUTPUT [--seconds N] [--max-output-mib N] | decode INPUT [--seconds N] [--max-output-mib N]");
        bool encoding = std::strcmp(arguments[1], "encode") == 0;
        if (!encoding && std::strcmp(arguments[1], "decode") != 0)
            fail("expected encode or decode");
        if (encoding && argument_count < 4)
            fail("encode requires an output path");
        uint64_t output_limit = UINT64_MAX;
        bool output_limit_set = false;
        for (int index = encoding ? 4 : 3; index < argument_count; index += 2) {
            if (index + 1 == argument_count)
                fail(std::string("missing value for ") + arguments[index]);
            long double value = positive_number(arguments[index + 1], arguments[index]);
            if (std::strcmp(arguments[index], "--seconds") == 0) {
                if (deadline_enabled || !std::isfinite(started + static_cast<double>(value)))
                    fail("duplicate or excessive time limit");
                deadline_enabled = true;
                deadline = started + static_cast<double>(value);
            } else if (std::strcmp(arguments[index], "--max-output-mib") == 0) {
                long double bytes = value * 1048576.0L;
                if (output_limit_set || !std::isfinite(bytes) || bytes < 1 ||
                    bytes >= 18446744073709551616.0L)
                    fail("duplicate or excessive output byte limit");
                output_limit = static_cast<uint64_t>(bytes);
                output_limit_set = true;
            } else {
                fail(std::string("unknown option ") + arguments[index]);
            }
        }
        install_signals();
        check_limits();
        Reader input(arguments[2]);
        if (encoding) {
            OutputFile file(arguments[3]);
            Writer output(file.descriptor, output_limit);
            output.append(reinterpret_cast<const uint8_t *>(compact_magic), 8);
            Header header = copy_header(input, output);
            nauty_check(WORDSIZE, 1, static_cast<int>(header.order), NAUTYVERSIONID);
            Counters counts = encode(input, output, header);
            output.finish();
            file.commit();
            print_statistics("encoded", header, counts, input, output);
        } else {
            if (std::memcmp(input.take(8), compact_magic, 8) != 0)
                fail("invalid compact placement magic");
            Writer output(STDOUT_FILENO, output_limit);
            Header header = copy_header(input, output);
            nauty_check(WORDSIZE, 1, static_cast<int>(header.order), NAUTYVERSIONID);
            Counters counts = decode(input, output, header);
            output.finish();
            print_statistics("decoded", header, counts, input, output);
        }
        return EXIT_SUCCESS;
    } catch (const std::exception &error) {
        std::fprintf(stderr, "placement_codec: %s\n", error.what());
        return EXIT_FAILURE;
    }
}
