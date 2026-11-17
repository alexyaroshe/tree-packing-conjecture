// residual-graph solver
// trees > rooted embeddings > canonical residuals > exact memo
// good states > placements & child labels > compressed proof
// limits > incomplete; all top trees good > complete
#include <nauty.h>
#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <csignal>
#include <cstdint>
#include <ctime>
#include <fstream>
#include <filesystem>
#include <functional>
#include <iomanip>
#include <iostream>
#include <limits>
#include <memory>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <sys/resource.h>
#include <vector>

constexpr int maximum_vertices = 13;
constexpr std::array<int, 14> tree_counts{0, 1, 1, 1, 2, 3, 6, 11, 23, 47, 106, 235, 551, 1301};
using Adjacency = std::array<uint16_t, maximum_vertices>;
volatile std::sig_atomic_t interrupted = 0;
void handle_signal(int) { interrupted = 1; }
int population(unsigned value) { return __builtin_popcount(value); }
int first_vertex(unsigned value) { return __builtin_ctz(value); }

struct GraphKey {
    uint64_t lower = 0;
    uint16_t upper = 0;
    bool operator==(const GraphKey& other) const { return lower == other.lower && upper == other.upper; }
};

GraphKey encode_graph(const Adjacency& adjacency, int vertices) {
    GraphKey key;
    int offset = 0;
    for (int vertex = 0; vertex < vertices - 1; ++vertex) {
        uint64_t row = adjacency[vertex] >> (vertex + 1);
        int length = vertices - vertex - 1;
        if (offset < 64) {
            key.lower |= row << offset;
            if (offset + length > 64) key.upper |= static_cast<uint16_t>(row >> (64 - offset));
        } else key.upper |= static_cast<uint16_t>(row << (offset - 64));
        offset += length;
    }
    return key;
}

uint64_t reverse_bits(uint64_t value) {
    value = ((value & UINT64_C(0x5555555555555555)) << 1) | ((value >> 1) & UINT64_C(0x5555555555555555));
    value = ((value & UINT64_C(0x3333333333333333)) << 2) | ((value >> 2) & UINT64_C(0x3333333333333333));
    value = ((value & UINT64_C(0x0f0f0f0f0f0f0f0f)) << 4) | ((value >> 4) & UINT64_C(0x0f0f0f0f0f0f0f0f));
    value = ((value & UINT64_C(0x00ff00ff00ff00ff)) << 8) | ((value >> 8) & UINT64_C(0x00ff00ff00ff00ff));
    value = ((value & UINT64_C(0x0000ffff0000ffff)) << 16) | ((value >> 16) & UINT64_C(0x0000ffff0000ffff));
    return (value << 32) | (value >> 32);
}

Adjacency decode_graph(GraphKey key, int vertices) {
    Adjacency adjacency{};
    int edge = 0;
    for (int left = 0; left < vertices; ++left)
        for (int right = left + 1; right < vertices; ++right, ++edge)
            if (edge < 64 ? ((key.lower >> edge) & 1u) : ((key.upper >> (edge - 64)) & 1u)) {
                adjacency[left] |= 1u << right;
                adjacency[right] |= 1u << left;
            }
    return adjacency;
}

uint64_t hash_key(GraphKey key) {
    uint64_t value = key.lower ^ (uint64_t{key.upper} * UINT64_C(0x9e3779b97f4a7c15));
    value ^= value >> 30;
    value *= UINT64_C(0xbf58476d1ce4e5b9);
    value ^= value >> 27;
    value *= UINT64_C(0x94d049bb133111eb);
    return value ^ (value >> 31);
}

struct CanonicalGraph {
    GraphKey key;
    Adjacency adjacency{};
    std::array<uint8_t, maximum_vertices> original_labels{};
    uint16_t root_representatives = 0;
};

CanonicalGraph canonicalize(const Adjacency& adjacency, int vertices) {
    std::array<uint8_t, maximum_vertices> active_labels{}, compact_labels{}, isolated_labels{};
    int active = 0, isolated = 0;
    for (int vertex = 0; vertex < vertices; ++vertex) {
        if (adjacency[vertex]) {
            compact_labels[vertex] = static_cast<uint8_t>(active);
            active_labels[active++] = static_cast<uint8_t>(vertex);
        } else isolated_labels[isolated++] = static_cast<uint8_t>(vertex);
    }
    CanonicalGraph result;
    for (int vertex = 0; vertex < isolated; ++vertex) result.original_labels[vertex] = isolated_labels[vertex];
    if (isolated) result.root_representatives = 1;
    if (!active) return result;
    graph input[maximum_vertices]{};
    graph canonical[maximum_vertices]{};
    int labels[maximum_vertices], partition[maximum_vertices], orbits[maximum_vertices];
    static_assert(WORDSIZE == 32 || WORDSIZE == 64, "supported nauty word sizes");
    for (int vertex = 0; vertex < active; ++vertex) {
        uint16_t row = adjacency[active_labels[vertex]];
        if (isolated) {
            unsigned remaining = row;
            row = 0;
            while (remaining) {
                int neighbor = first_vertex(remaining);
                remaining &= remaining - 1;
                row |= 1u << compact_labels[neighbor];
            }
        }
        input[vertex] = static_cast<setword>(reverse_bits(row) >> (64 - WORDSIZE));
    }
    DEFAULTOPTIONS_GRAPH(options);
    options.getcanon = TRUE;
    statsblk statistics{};
    densenauty(input, labels, partition, orbits, &options, &statistics, 1, active, canonical);
    if (statistics.errstatus) throw std::runtime_error("nauty failed");
    unsigned seen_orbits = 0;
    for (int vertex = 0; vertex < active; ++vertex) {
        result.original_labels[vertex + isolated] = active_labels[labels[vertex]];
        unsigned orbit = 1u << orbits[labels[vertex]];
        if (!(seen_orbits & orbit)) result.root_representatives |= 1u << (vertex + isolated);
        seen_orbits |= orbit;
        result.adjacency[vertex + isolated] = static_cast<uint16_t>((reverse_bits(canonical[vertex]) >> (64 - WORDSIZE)) << isolated);
    }
    result.key = encode_graph(result.adjacency, vertices);
    return result;
}

struct Tree {
    int size = 0, index = 0, maximum_degree = 0;
    Adjacency adjacency{};
    std::array<uint8_t, maximum_vertices> parents{};
    std::array<uint8_t, maximum_vertices> order{};
    std::array<int8_t, maximum_vertices> parent_positions{}, previous_siblings{};
    std::array<uint8_t, maximum_vertices> degrees{};
    std::array<uint8_t, maximum_vertices> descending_degrees{};
};
using Catalog = std::array<std::vector<Tree>, maximum_vertices + 1>;

std::string rooted_shape(const Adjacency& adjacency, int vertex, int parent) {
    std::vector<std::string> children;
    unsigned neighbors = adjacency[vertex] & ~(parent < 0 ? 0u : (1u << parent));
    while (neighbors) {
        int neighbor = first_vertex(neighbors);
        neighbors &= neighbors - 1;
        children.push_back(rooted_shape(adjacency, neighbor, vertex));
    }
    std::sort(children.begin(), children.end());
    std::string result = "(";
    for (const auto& child : children) result += child;
    return result + ")";
}

void order_tree(Tree& tree, int vertex, int parent, int parent_position, int previous_sibling, int& position) {
    int current = position++;
    tree.order[current] = static_cast<uint8_t>(vertex);
    tree.parent_positions[current] = static_cast<int8_t>(parent_position);
    tree.previous_siblings[current] = static_cast<int8_t>(previous_sibling);
    tree.degrees[current] = static_cast<uint8_t>(population(tree.adjacency[vertex]));
    std::vector<std::pair<std::string, int>> children;
    unsigned neighbors = tree.adjacency[vertex] & ~(parent < 0 ? 0u : (1u << parent));
    while (neighbors) {
        int neighbor = first_vertex(neighbors);
        neighbors &= neighbors - 1;
        children.emplace_back(rooted_shape(tree.adjacency, neighbor, vertex), neighbor);
    }
    std::sort(children.begin(), children.end());
    std::string previous_shape;
    int previous_position = -1;
    for (const auto& child : children) {
        int child_position = position;
        order_tree(tree, child.second, vertex, current,
                   child.first == previous_shape ? previous_position : -1, position);
        previous_shape = child.first;
        previous_position = child_position;
    }
}

void prepare_tree(Tree& tree) {
    unsigned remaining = (1u << tree.size) - 1;
    while (population(remaining) > 2) {
        unsigned leaves = 0;
        for (int vertex = 0; vertex < tree.size; ++vertex)
            if ((remaining & (1u << vertex)) && population(tree.adjacency[vertex] & remaining) == 1)
                leaves |= 1u << vertex;
        if (!leaves) throw std::runtime_error("catalog entry is not a tree");
        remaining &= ~leaves;
    }
    int root = first_vertex(remaining);
    for (int vertex = root + 1; vertex < tree.size; ++vertex)
        if ((remaining & (1u << vertex)) && population(tree.adjacency[vertex]) > population(tree.adjacency[root])) root = vertex;
    int position = 0;
    order_tree(tree, root, -1, -1, -1, position);
    for (int vertex = 0; vertex < tree.size; ++vertex) {
        int degree = population(tree.adjacency[vertex]);
        tree.maximum_degree = std::max(tree.maximum_degree, degree);
        tree.descending_degrees[vertex] = static_cast<uint8_t>(degree);
    }
    std::sort(tree.descending_degrees.begin(), tree.descending_degrees.begin() + tree.size, std::greater<uint8_t>());
}

Catalog read_catalog(const std::string& path, int maximum_size) {
    std::ifstream input(path);
    if (!input) throw std::runtime_error("cannot open tree catalog");
    Catalog catalog;
    std::array<std::set<std::string>, maximum_vertices + 1> shapes;
    int size = 0;
    std::set<int> sections;
    std::string line;
    while (std::getline(input, line)) {
        if (line.empty()) throw std::runtime_error("empty catalog line");
        std::istringstream values(line);
        if (line[0] == '#') {
            char marker;
            std::string trailing;
            if (!(values >> marker >> size) || size < 2 || size > maximum_vertices || (values >> trailing) || !sections.insert(size).second)
                throw std::runtime_error("invalid catalog section");
            continue;
        }
        if (!size) throw std::runtime_error("missing catalog section");
        Tree tree;
        tree.size = size;
        tree.index = static_cast<int>(catalog[size].size());
        int root;
        if (!(values >> root) || root != 0) throw std::runtime_error("invalid tree root");
        for (int vertex = 1; vertex < size; ++vertex) {
            int parent;
            if (!(values >> parent) || parent < 1 || parent > vertex) throw std::runtime_error("invalid tree parent");
            --parent;
            tree.parents[vertex] = static_cast<uint8_t>(parent);
            tree.adjacency[vertex] |= 1u << parent;
            tree.adjacency[parent] |= 1u << vertex;
        }
        std::string trailing;
        if (values >> trailing) throw std::runtime_error("trailing tree data");
        std::string shape;
        for (int vertex = 0; vertex < size; ++vertex) {
            auto candidate = rooted_shape(tree.adjacency, vertex, -1);
            if (shape.empty() || candidate < shape) shape = candidate;
        }
        if (!shapes[size].insert(shape).second) throw std::runtime_error("duplicate tree shape");
        prepare_tree(tree);
        catalog[size].push_back(tree);
    }
    for (int level = 2; level <= maximum_size; ++level) {
        if (static_cast<int>(catalog[level].size()) != tree_counts[level]) throw std::runtime_error("wrong tree count");
        std::stable_sort(catalog[level].begin(), catalog[level].end(), [](const Tree& left, const Tree& right) {
            return left.maximum_degree > right.maximum_degree;
        });
    }
    return catalog;
}

struct SearchLimit : std::runtime_error { using std::runtime_error::runtime_error; };
struct Budget {
    std::chrono::steady_clock::time_point started = std::chrono::steady_clock::now();
    double seconds = 60;
    uint64_t memory_bytes = uint64_t{1024} * 1024 * 1024;
    uint64_t table_bytes = 0, maximum_states = std::numeric_limits<uint64_t>::max(), stored_states = 0;
    uint64_t polls = 0;
    std::function<void()> report_progress;
    std::chrono::steady_clock::time_point next_progress = started;
    void check(bool force = false) {
        if (!force && (++polls & 1023u)) return;
        if (interrupted) throw SearchLimit("signal");
        auto now = std::chrono::steady_clock::now();
        if (std::chrono::duration<double>(now - started).count() >= seconds) throw SearchLimit("time");
        struct rusage usage{};
        if (getrusage(RUSAGE_SELF, &usage)) throw std::runtime_error("resource accounting failed");
#ifdef __APPLE__
        uint64_t peak_bytes = static_cast<uint64_t>(usage.ru_maxrss);
#else
        uint64_t peak_bytes = static_cast<uint64_t>(usage.ru_maxrss) * 1024;
#endif
        if (peak_bytes > memory_bytes) throw SearchLimit("memory");
        if (report_progress && now >= next_progress) {
            report_progress();
            next_progress = now + std::chrono::seconds(30);
        }
    }
    void allocate(uint64_t bytes) {
        check(true);
        if (bytes > memory_bytes || table_bytes > memory_bytes - bytes) throw SearchLimit("memory");
        table_bytes += bytes;
    }
};

struct MemoEntry {
    uint64_t lower = 0;
    uint16_t upper = 0;
    uint8_t outcome = 0;
    uint8_t reserved = 0;
    uint32_t proof_id = 0;
};
static_assert(sizeof(MemoEntry) == 16, "memo entries must occupy 16 bytes");
struct Answer { bool good = false; uint32_t proof_id = 0; };

class MemoTable {
    std::unique_ptr<MemoEntry[]> entries;
    size_t capacity = 0, count = 0;
    void grow(Budget& budget) {
        size_t next_capacity = capacity ? capacity * 2 : 1024;
        uint64_t bytes = next_capacity * sizeof(MemoEntry);
        budget.allocate(bytes);
        auto replacement = std::make_unique<MemoEntry[]>(next_capacity);
        for (size_t index = 0; index < capacity; ++index) {
            const auto& entry = entries[index];
            if (!entry.outcome) continue;
            size_t slot = hash_key({entry.lower, entry.upper}) & (next_capacity - 1);
            while (replacement[slot].outcome) slot = (slot + 1) & (next_capacity - 1);
            replacement[slot] = entry;
        }
        budget.table_bytes -= capacity * sizeof(MemoEntry);
        entries = std::move(replacement);
        capacity = next_capacity;
    }
public:
    bool lookup(GraphKey key, Answer& answer) const {
        if (!capacity) return false;
        size_t slot = hash_key(key) & (capacity - 1);
        while (entries[slot].outcome) {
            const auto& entry = entries[slot];
            if (entry.lower == key.lower && entry.upper == key.upper) {
                answer = {entry.outcome == 1, entry.proof_id};
                return true;
            }
            slot = (slot + 1) & (capacity - 1);
        }
        return false;
    }
    void insert(GraphKey key, Answer answer, Budget& budget) {
        if (budget.stored_states >= budget.maximum_states) throw SearchLimit("states");
        if (!capacity || (count + 1) * 10 > capacity * 7) grow(budget);
        size_t slot = hash_key(key) & (capacity - 1);
        while (entries[slot].outcome) slot = (slot + 1) & (capacity - 1);
        entries[slot] = {key.lower, key.upper, static_cast<uint8_t>(answer.good ? 1 : 2), 0, answer.proof_id};
        ++count;
        ++budget.stored_states;
    }
};

struct Placement {
    uint16_t tree_index = 0;
    std::array<uint8_t, maximum_vertices> images{}, child_labels{};
    uint32_t child_id = 0;
};

class ProofWriter {
    std::ofstream output;
    uint64_t maximum_bytes;
    uint32_t nodes = 0;
public:
    uint64_t bytes = 0;
    explicit ProofWriter(const std::string& path, uint64_t limit) : maximum_bytes(limit) {
        if (!path.empty()) {
            std::ifstream existing(path);
            if (existing) throw std::runtime_error("proof path already exists");
            output.open(path, std::ios::binary);
            if (!output) throw std::runtime_error("cannot create proof");
        }
    }
    bool enabled() const { return output.is_open(); }
    void integer(uint64_t value, unsigned width) {
        if (!enabled()) return;
        if (bytes + width > maximum_bytes) throw SearchLimit("proof-size");
        for (unsigned index = 0; index < width; ++index) output.put(static_cast<char>(value >> (8 * index)));
        bytes += width;
        if (!output) throw std::runtime_error("proof write failed");
    }
    void header(int vertices, int first_top, int last_top, const Catalog& catalog) {
        if (!enabled()) return;
        for (char byte : std::string("TPCRDP01")) integer(static_cast<unsigned char>(byte), 1);
        integer(vertices, 1); integer(first_top, 2); integer(last_top, 2);
        for (int level = 2; level <= vertices; ++level) {
            integer(catalog[level].size(), 2);
            std::vector<const Tree*> original(catalog[level].size());
            for (const auto& tree : catalog[level]) original[tree.index] = &tree;
            for (const auto* tree : original)
                for (int vertex = 1; vertex < level; ++vertex) integer(tree->parents[vertex], 1);
        }
        for (int top = first_top; top < last_top; ++top) integer(catalog[vertices][top].index, 2);
    }
    void placement(const Placement& choice, int level, int vertices) {
        integer(choice.tree_index, 2);
        for (int vertex = 0; vertex < level; ++vertex) integer(choice.images[vertex], 1);
        integer(choice.child_id, 4);
        for (int vertex = 0; vertex < vertices; ++vertex) integer(choice.child_labels[vertex], 1);
    }
    uint32_t node(GraphKey key, int level, int vertices, const std::vector<Placement>& choices) {
        if (!enabled()) return 0;
        if (nodes == std::numeric_limits<uint32_t>::max()) throw SearchLimit("proof-nodes");
        integer(1, 1); integer(level, 1); integer(key.lower, 8); integer(key.upper, 2);
        for (const auto& choice : choices) placement(choice, level, vertices);
        return ++nodes;
    }
    void root(const Placement& choice, int vertices) { integer(2, 1); placement(choice, vertices, vertices); }
    void finish(int roots) {
        integer(3, 1); integer(roots, 2);
        if (enabled()) { output.flush(); if (!output) throw std::runtime_error("proof flush failed"); }
    }
};

struct Statistics {
    uint64_t canonical_calls = 0, embeddings = 0, memo_hits = 0, good_states = 0, bad_states = 0;
    uint64_t degree_rejections = 0, raw_cache_hits = 0;
    std::array<uint64_t, maximum_vertices + 1> states_by_level{};
};

struct RawCacheEntry {
    uint64_t lower = 0;
    uint16_t upper = 0;
    uint8_t outcome = 0;
    uint8_t reserved = 0;
    uint32_t proof_id = 0;
    std::array<uint8_t, maximum_vertices> labels{};
};
static_assert(sizeof(RawCacheEntry) == 32, "raw cache entries must occupy 32 bytes");

class Solver {
    int vertices;
    const Catalog& catalog;
    Budget& budget;
    ProofWriter& proof;
    std::array<MemoTable, maximum_vertices + 1> memo;
    bool use_orbits, order_siblings;
    unsigned cache_bits;
    std::unique_ptr<RawCacheEntry[]> raw_cache;

    bool try_embedding(const Tree& tree, const CanonicalGraph& host, int position, unsigned used,
                       std::array<uint8_t, maximum_vertices>& images, Placement& winner) {
        budget.check();
        if (position == tree.size) {
            ++statistics.embeddings;
            Adjacency residual = host.adjacency;
            for (int child = 1; child < tree.size; ++child) {
                int left = images[tree.parent_positions[child]], right = images[child];
                residual[left] &= ~(1u << right);
                residual[right] &= ~(1u << left);
            }
            winner.tree_index = static_cast<uint16_t>(tree.index);
            for (int current = 0; current < tree.size; ++current) winner.images[tree.order[current]] = images[current];
            if (tree.size <= 3) {
                for (int vertex = 0; vertex < vertices; ++vertex) winner.child_labels[vertex] = static_cast<uint8_t>(vertex);
                winner.child_id = 0;
                return true;
            }
            int greatest_degree = 0;
            for (int vertex = 0; vertex < vertices; ++vertex)
                greatest_degree = std::max(greatest_degree, population(residual[vertex]));
            if (greatest_degree < tree.size - 2) { ++statistics.degree_rejections; return false; }
            GraphKey raw_key = encode_graph(residual, vertices);
            size_t raw_slot = 0;
            if (cache_bits) {
                if (!raw_cache) {
                    budget.allocate((size_t{1} << cache_bits) * sizeof(RawCacheEntry));
                    raw_cache = std::make_unique<RawCacheEntry[]>(size_t{1} << cache_bits);
                }
                raw_slot = hash_key(raw_key) & ((size_t{1} << cache_bits) - 1);
                const auto& cached = raw_cache[raw_slot];
                if (cached.outcome && cached.lower == raw_key.lower && cached.upper == raw_key.upper) {
                    ++statistics.raw_cache_hits;
                    if (cached.outcome != 1) return false;
                    winner.child_labels = cached.labels;
                    winner.child_id = cached.proof_id;
                    return true;
                }
            }
            ++statistics.canonical_calls;
            auto canonical = canonicalize(residual, vertices);
            auto child_answer = evaluate(canonical, tree.size - 1);
            if (raw_cache) raw_cache[raw_slot] = {raw_key.lower, raw_key.upper, static_cast<uint8_t>(child_answer.good ? 1 : 2),
                                                0, child_answer.proof_id, canonical.original_labels};
            if (!child_answer.good) return false;
            winner.child_labels = canonical.original_labels;
            winner.child_id = child_answer.proof_id;
            return true;
        }
        int parent = tree.parent_positions[position];
        unsigned candidates = parent < 0 ? (use_orbits ? host.root_representatives : ((1u << vertices) - 1))
                                         : (host.adjacency[images[parent]] & ~used);
        int sibling = tree.previous_siblings[position];
        if (order_siblings && sibling >= 0) candidates &= ~((1u << (images[sibling] + 1)) - 1);
        int children_needed = tree.degrees[position] - (parent >= 0 ? 1 : 0);
        while (candidates) {
            int candidate = first_vertex(candidates);
            candidates &= candidates - 1;
            if (population(host.adjacency[candidate] & ~used) < children_needed) continue;
            images[position] = static_cast<uint8_t>(candidate);
            if (try_embedding(tree, host, position + 1, used | (1u << candidate), images, winner)) return true;
        }
        return false;
    }
public:
    Statistics statistics;
    Solver(int order, const Catalog& trees, Budget& limits, ProofWriter& writer, bool orbits, bool siblings, unsigned raw_cache_bits)
        : vertices(order), catalog(trees), budget(limits), proof(writer), use_orbits(orbits), order_siblings(siblings), cache_bits(raw_cache_bits) {}

    uint64_t cache_bytes() const { return raw_cache ? (size_t{1} << cache_bits) * sizeof(RawCacheEntry) : 0; }

    Answer evaluate(const CanonicalGraph& host, int level) {
        budget.check();
        if (level <= 2) return {true, 0};
        Answer cached;
        if (memo[level].lookup(host.key, cached)) { ++statistics.memo_hits; return cached; }
        ++statistics.states_by_level[level];
        std::array<uint8_t, maximum_vertices> host_degrees{};
        for (int vertex = 0; vertex < vertices; ++vertex) host_degrees[vertex] = static_cast<uint8_t>(population(host.adjacency[vertex]));
        std::sort(host_degrees.begin(), host_degrees.begin() + vertices, std::greater<uint8_t>());
        std::vector<Placement> choices;
        if (proof.enabled()) choices.reserve(catalog[level].size());
        for (const auto& tree : catalog[level]) {
            bool feasible = true;
            for (int index = 0; index < level; ++index)
                if (tree.descending_degrees[index] > host_degrees[index]) { feasible = false; break; }
            Placement winner;
            std::array<uint8_t, maximum_vertices> images{};
            if (!feasible || !try_embedding(tree, host, 0, 0, images, winner)) {
                memo[level].insert(host.key, {false, 0}, budget);
                ++statistics.bad_states;
                return {false, 0};
            }
            if (proof.enabled()) choices.push_back(winner);
        }
        Answer answer{true, proof.node(host.key, level, vertices, choices)};
        memo[level].insert(host.key, answer, budget);
        ++statistics.good_states;
        return answer;
    }

    CanonicalGraph normalize(const Adjacency& adjacency) {
        budget.check(true);
        ++statistics.canonical_calls;
        return canonicalize(adjacency, vertices);
    }
};

uint64_t unsigned_number(const std::string& text, int base = 10) {
    if (text.empty() || text[0] == '-' || text[0] == '+' || text[0] == ' ') throw std::runtime_error("invalid unsigned integer");
    size_t used = 0;
    auto value = std::stoull(text, &used, base);
    if (used != text.size()) throw std::runtime_error("invalid unsigned integer");
    return value;
}

struct Options {
    int vertices = 0, first_top = 0, last_top = -1;
    std::string catalog, proof, graph_file, canonical_file, progress;
    double seconds = 60;
    uint64_t memory_mib = 1024, proof_mib = 256, maximum_states = std::numeric_limits<uint64_t>::max();
    bool orbits = true, siblings = true;
    unsigned cache_bits = 18;
};

Options parse_options(int count, char** arguments) {
    Options options;
    for (int index = 1; index < count; ++index) {
        std::string name = arguments[index];
        if (name == "--no-orbits") { options.orbits = false; continue; }
        if (name == "--no-sibling-order") { options.siblings = false; continue; }
        if (index + 1 >= count) throw std::runtime_error("missing option value");
        std::string value = arguments[++index];
        if (name == "--n") {
            auto order = unsigned_number(value);
            if (order < 2 || order > maximum_vertices) throw std::runtime_error("n must be 2..13");
            options.vertices = static_cast<int>(order);
        } else if (name == "--trees") options.catalog = value;
        else if (name == "--proof") options.proof = value;
        else if (name == "--progress") options.progress = value;
        else if (name == "--graphs") options.graph_file = value;
        else if (name == "--canonical-graphs") options.canonical_file = value;
        else if (name == "--seconds") {
            size_t used;
            options.seconds = std::stod(value, &used);
            if (used != value.size() || !std::isfinite(options.seconds) || options.seconds <= 0) throw std::runtime_error("invalid time limit");
        } else if (name == "--memory-mib") options.memory_mib = unsigned_number(value);
        else if (name == "--proof-mib") options.proof_mib = unsigned_number(value);
        else if (name == "--max-states") options.maximum_states = unsigned_number(value);
        else if (name == "--cache-bits") {
            auto bits = unsigned_number(value);
            if (bits && (bits < 10 || bits > 24)) throw std::runtime_error("cache bits must be 0 or 10..24");
            options.cache_bits = static_cast<unsigned>(bits);
        }
        else if (name == "--top") {
            size_t colon = value.find(':');
            if (colon == std::string::npos) throw std::runtime_error("top must be first:last");
            uint64_t first = unsigned_number(value.substr(0, colon)), last = unsigned_number(value.substr(colon + 1));
            if (first > 1301 || last > 1301 || first >= last) throw std::runtime_error("invalid top range");
            options.first_top = static_cast<int>(first); options.last_top = static_cast<int>(last);
        } else throw std::runtime_error("unknown option: " + name);
    }
    constexpr uint64_t largest_mib = std::numeric_limits<uint64_t>::max() / (1024 * 1024);
    if (!options.vertices || options.catalog.empty() || !options.memory_mib || !options.proof_mib ||
        options.memory_mib > largest_mib || options.proof_mib > largest_mib) throw std::runtime_error("missing or invalid required option");
    if (!options.graph_file.empty() && !options.canonical_file.empty()) throw std::runtime_error("conflicting graph modes");
    if ((!options.graph_file.empty() || !options.canonical_file.empty()) && !options.proof.empty()) throw std::runtime_error("graph modes cannot emit a campaign proof");
    if (options.last_top < 0) options.last_top = tree_counts[options.vertices];
    if (options.first_top >= options.last_top || options.last_top > tree_counts[options.vertices]) throw std::runtime_error("top range exceeds catalog");
    return options;
}

void validate_graph(GraphKey key, int vertices, int level, bool check_level = true) {
    int edges = vertices * (vertices - 1) / 2;
    if ((edges < 64 && (key.lower >> edges)) || (edges <= 64 && key.upper) || (edges > 64 && (key.upper >> (edges - 64))))
        throw std::runtime_error("graph has out-of-range edges");
    if (check_level && (level < 1 || level > vertices || __builtin_popcountll(key.lower) + population(key.upper) != level * (level - 1) / 2))
        throw std::runtime_error("graph edge count does not match level");
}

int main(int argument_count, char** arguments) {
    std::signal(SIGINT, handle_signal); std::signal(SIGTERM, handle_signal);
    const auto started = std::chrono::steady_clock::now();
    const auto cpu_started = std::clock();
    try {
        auto options = parse_options(argument_count, arguments);
        nauty_check(WORDSIZE, 1, options.vertices, NAUTYVERSIONID);
        Budget budget;
        budget.started = started;
        budget.seconds = options.seconds;
        budget.memory_bytes = options.memory_mib * 1024 * 1024;
        budget.maximum_states = options.maximum_states;
        auto catalog = read_catalog(options.catalog, options.vertices);
        ProofWriter proof(options.proof, options.proof_mib * 1024 * 1024);
        Solver solver(options.vertices, catalog, budget, proof, options.orbits, options.siblings, options.cache_bits);
        int completed = 0;
        int current_top = options.first_top;
        bool good = true;
        std::string stop_reason;
        auto write_progress = [&](const char* status) {
            if (options.progress.empty()) return;
            const auto temporary = options.progress + ".tmp";
            std::ofstream output(temporary);
            if (!output) throw std::runtime_error("cannot create progress snapshot");
            output << std::setprecision(10) << "{\"status\":\"" << status << "\",\"n\":" << options.vertices
                   << ",\"top\":" << current_top << ",\"completed\":" << completed
                   << ",\"wall_seconds\":" << std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count()
                   << ",\"cpu_seconds\":" << static_cast<double>(std::clock() - cpu_started) / CLOCKS_PER_SEC
                   << ",\"stored_states\":" << budget.stored_states << ",\"allocated_memory_bytes\":" << budget.table_bytes
                   << ",\"proof_bytes\":" << proof.bytes << ",\"states_by_level\":{";
            bool first = true;
            for (int level = 3; level < options.vertices; ++level) {
                if (!first) output << ',';
                first = false;
                output << '\"' << level << "\":" << solver.statistics.states_by_level[level];
            }
            output << "}}\n";
            output.flush();
            if (!output) throw std::runtime_error("progress snapshot write failed");
            output.close();
            std::filesystem::rename(temporary, options.progress);
        };
        if (!options.progress.empty()) {
            if (std::filesystem::exists(options.progress) || std::filesystem::exists(options.progress + ".tmp"))
                throw std::runtime_error("progress path already exists");
            budget.report_progress = [&] { write_progress("running"); };
        }
        try {
            if (!options.graph_file.empty() || !options.canonical_file.empty()) {
                std::ifstream input(options.graph_file.empty() ? options.canonical_file : options.graph_file);
                if (!input) throw std::runtime_error("cannot open graph file");
                std::string line;
                while (std::getline(input, line)) {
                    std::istringstream values(line);
                    std::string lower, upper, trailing;
                    int level;
                    if (!(values >> level >> lower >> upper) || (values >> trailing)) throw std::runtime_error("invalid graph record");
                    auto high = unsigned_number(upper, 16);
                    if (high > UINT16_MAX) throw std::runtime_error("invalid high graph word");
                    GraphKey key{unsigned_number(lower, 16), static_cast<uint16_t>(high)};
                    validate_graph(key, options.vertices, level, !options.graph_file.empty());
                    auto canonical = solver.normalize(decode_graph(key, options.vertices));
                    if (!options.canonical_file.empty()) {
                        std::cout << std::hex << canonical.key.lower << ' ' << canonical.key.upper << std::dec << '\n';
                    } else {
                        auto answer = solver.evaluate(canonical, level);
                        std::cout << "{\"graph\":" << completed << ",\"good\":" << (answer.good ? "true" : "false") << "}\n";
                    }
                    ++completed;
                }
            } else {
                proof.header(options.vertices, options.first_top, options.last_top, catalog);
                Adjacency complete{};
                for (int vertex = 0; vertex < options.vertices; ++vertex) complete[vertex] = ((1u << options.vertices) - 1) ^ (1u << vertex);
                for (int top = options.first_top; top < options.last_top; ++top) {
                    current_top = top;
                    budget.check(true);
                    const auto& tree = catalog[options.vertices][top];
                    Adjacency residual = complete;
                    for (int vertex = 0; vertex < options.vertices; ++vertex) residual[vertex] &= ~tree.adjacency[vertex];
                    auto canonical = solver.normalize(residual);
                    auto answer = solver.evaluate(canonical, options.vertices - 1);
                    if (!answer.good) { good = false; break; }
                    Placement root;
                    root.tree_index = static_cast<uint16_t>(tree.index);
                    for (int vertex = 0; vertex < options.vertices; ++vertex) root.images[vertex] = static_cast<uint8_t>(vertex);
                    root.child_labels = canonical.original_labels;
                    root.child_id = answer.proof_id;
                    proof.root(root, options.vertices);
                    ++completed;
                    std::cerr << "TOP " << top << " catalog=" << tree.index << " good states=" << budget.stored_states << '\n';
                }
                if (good) proof.finish(completed);
            }
        } catch (const SearchLimit& limit) { stop_reason = limit.what(); }
        write_progress(stop_reason.empty() ? (good ? "complete" : "online-false") : "incomplete");
        if (!options.canonical_file.empty() && stop_reason.empty()) return 0;
        struct rusage usage{};
        if (getrusage(RUSAGE_SELF, &usage)) throw std::runtime_error("resource accounting failed");
        uint64_t peak = static_cast<uint64_t>(usage.ru_maxrss);
#ifndef __APPLE__
        peak *= 1024;
#endif
        const auto& statistics = solver.statistics;
        std::cout << std::setprecision(10) << "{\"status\":\"" << (stop_reason.empty() ? (good ? "complete" : "online-false") : "incomplete")
                  << "\",\"stop_reason\":\"" << stop_reason << "\",\"n\":" << options.vertices
                  << ",\"top_first\":" << options.first_top << ",\"top_last\":" << options.last_top << ",\"completed\":" << completed
                  << ",\"cpu_seconds\":" << static_cast<double>(std::clock() - cpu_started) / CLOCKS_PER_SEC
                  << ",\"wall_seconds\":" << std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count()
                  << ",\"peak_memory_bytes\":" << peak << ",\"memo_bytes\":" << budget.table_bytes - solver.cache_bytes()
                  << ",\"raw_cache_bytes\":" << solver.cache_bytes() << ",\"raw_cache_hits\":" << statistics.raw_cache_hits
                  << ",\"degree_rejections\":" << statistics.degree_rejections
                  << ",\"stored_states\":" << budget.stored_states << ",\"good_states\":" << statistics.good_states
                  << ",\"bad_states\":" << statistics.bad_states << ",\"memo_hits\":" << statistics.memo_hits
                  << ",\"canonical_calls\":" << statistics.canonical_calls << ",\"embeddings\":" << statistics.embeddings
                  << ",\"proof_bytes\":" << proof.bytes << ",\"states_by_level\":{";
        bool first = true;
        for (int level = 3; level < options.vertices; ++level) {
            if (!first) std::cout << ',';
            first = false;
            std::cout << '\"' << level << "\":" << statistics.states_by_level[level];
        }
        std::cout << "}}\n";
        return stop_reason.empty() ? (good ? 0 : 2) : 3;
    } catch (const std::exception& error) {
        std::cerr << "ERROR: " << error.what() << '\n';
        return 1;
    }
}
