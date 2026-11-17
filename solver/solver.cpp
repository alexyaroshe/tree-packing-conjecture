// parallel state solver
// root workers > private DFS & raw caches > shared sharded completed memo
// resume: validated shard counts > final table capacities > validated restore
// coordinator pause > completed memo & root prefix > TPCMEM01 > resume
// all roots good > sorted winning states > TPCGST01
#include <nauty.h>
#include <algorithm>
#include <atomic>
#include <condition_variable>
#include <exception>
#include <mutex>
#include <thread>
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
#include <cerrno>
#include <cstring>
#include <fcntl.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <unistd.h>

constexpr int maximum_vertices = 13;
constexpr std::array<int, 14> tree_counts{0, 1, 1, 1, 2, 3, 6, 11, 23, 47, 106, 235, 551, 1301};
using Adjacency = std::array<uint16_t, maximum_vertices>;
std::atomic<bool> interrupted{false};
static_assert(std::atomic<bool>::is_always_lock_free, "signal flag must be lock-free");
void handle_signal(int) { interrupted.store(true, std::memory_order_relaxed); }
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
thread_local bool worker_thread = false;

class WorkerControl {
    std::mutex mutex;
    std::condition_variable changed;
    std::atomic<bool> pause_requested{false}, stopping{false};
    size_t live = 0, paused = 0;
    std::string limit;
    std::exception_ptr failure;
    bool rejected_root = false;
public:
    void register_workers(size_t count) { std::lock_guard<std::mutex> lock(mutex); live = count; }
    void finished(size_t count = 1) {
        std::lock_guard<std::mutex> lock(mutex);
        if (count > live) std::terminate();
        live -= count;
        changed.notify_all();
    }
    size_t active() { std::lock_guard<std::mutex> lock(mutex); return live; }
    bool stopped() const { return stopping.load(std::memory_order_acquire); }
    void safe_point() {
        if (!pause_requested.load(std::memory_order_acquire)) return;
        std::unique_lock<std::mutex> lock(mutex);
        if (!pause_requested.load(std::memory_order_relaxed)) return;
        ++paused;
        changed.notify_all();
        changed.wait(lock, [&] { return !pause_requested.load(std::memory_order_relaxed); });
        --paused;
    }
    void pause() {
        std::unique_lock<std::mutex> lock(mutex);
        pause_requested.store(true, std::memory_order_release);
        changed.wait(lock, [&] { return paused == live; });
    }
    void resume() {
        std::lock_guard<std::mutex> lock(mutex);
        pause_requested.store(false, std::memory_order_release);
        changed.notify_all();
    }
    void stop_limit(const std::string& reason) {
        std::lock_guard<std::mutex> lock(mutex);
        if (limit.empty() && reason != "cancelled") limit = reason;
        stopping.store(true, std::memory_order_release);
        changed.notify_all();
    }
    void stop_failure(std::exception_ptr error) {
        std::lock_guard<std::mutex> lock(mutex);
        if (!failure) failure = error;
        stopping.store(true, std::memory_order_release);
        changed.notify_all();
    }
    void stop_rejected_root() {
        std::lock_guard<std::mutex> lock(mutex);
        rejected_root = true;
        stopping.store(true, std::memory_order_release);
        changed.notify_all();
    }
    void wait() {
        std::unique_lock<std::mutex> lock(mutex);
        changed.wait_for(lock, std::chrono::milliseconds(10), [&] { return live == 0 || stopping.load(); });
    }
    std::string stop_reason() { std::lock_guard<std::mutex> lock(mutex); return limit; }
    bool root_failed() { std::lock_guard<std::mutex> lock(mutex); return rejected_root; }
    void rethrow_failure() {
        std::lock_guard<std::mutex> lock(mutex);
        if (failure) std::rethrow_exception(failure);
    }
};

struct Budget {
    std::chrono::steady_clock::time_point started = std::chrono::steady_clock::now();
    double seconds = 60;
    uint64_t memory_bytes = uint64_t{1024} * 1024 * 1024;
    std::atomic<uint64_t> table_bytes{0}, stored_states{0};
    uint64_t maximum_states = std::numeric_limits<uint64_t>::max();
    WorkerControl* workers = nullptr;
    void check(bool force = false) {
        thread_local uint64_t polls = 0;
        if (!force && (++polls & 1023u)) return;
        if (worker_thread && workers) {
            workers->safe_point();
            if (workers->stopped()) throw SearchLimit("cancelled");
        }
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
    }
    void allocate(uint64_t bytes) {
        uint64_t current = table_bytes.load(std::memory_order_relaxed);
        do {
            if (bytes > memory_bytes || current > memory_bytes - bytes) throw SearchLimit("memory");
        } while (!table_bytes.compare_exchange_weak(current, current + bytes, std::memory_order_relaxed));
    }
    void release(uint64_t bytes) { table_bytes.fetch_sub(bytes, std::memory_order_relaxed); }
    void reserve_state() {
        uint64_t current = stored_states.load(std::memory_order_relaxed);
        do {
            if (current >= maximum_states) throw SearchLimit("states");
        } while (!stored_states.compare_exchange_weak(current, current + 1, std::memory_order_relaxed));
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
        std::unique_ptr<MemoEntry[]> replacement;
        try { replacement = std::make_unique<MemoEntry[]>(next_capacity); }
        catch (const std::bad_alloc&) { budget.release(bytes); throw SearchLimit("memory"); }
        for (size_t index = 0; index < capacity; ++index) {
            const auto& entry = entries[index];
            if (!entry.outcome) continue;
            size_t slot = hash_key({entry.lower, entry.upper}) & (next_capacity - 1);
            while (replacement[slot].outcome) slot = (slot + 1) & (next_capacity - 1);
            replacement[slot] = entry;
        }
        budget.release(capacity * sizeof(MemoEntry));
        entries = std::move(replacement);
        capacity = next_capacity;
    }
public:
    static uint64_t reserved_bytes(uint64_t entries_count) {
        if (!entries_count) return 0;
        size_t reserved_capacity = 1024;
        constexpr size_t largest_capacity = std::numeric_limits<size_t>::max() / sizeof(MemoEntry);
        while (entries_count > (reserved_capacity * uint64_t{7}) / 10) {
            if (reserved_capacity > largest_capacity / 2) throw SearchLimit("memory");
            reserved_capacity *= 2;
        }
        return reserved_capacity * sizeof(MemoEntry);
    }
    void reserve_empty(uint64_t entries_count, Budget& budget) {
        if (capacity || count) throw std::runtime_error("checkpoint reservation requires an empty memo");
        uint64_t bytes = reserved_bytes(entries_count);
        if (!bytes) return;
        budget.check(true);
        budget.allocate(bytes);
        std::unique_ptr<MemoEntry[]> replacement;
        try { replacement = std::make_unique<MemoEntry[]>(bytes / sizeof(MemoEntry)); }
        catch (const std::bad_alloc&) { budget.release(bytes); throw SearchLimit("memory"); }
        entries = std::move(replacement);
        capacity = bytes / sizeof(MemoEntry);
        budget.check(true);
    }
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
    template<class Function> void visit(Function function) const {
        for (size_t index = 0; index < capacity; ++index)
            if (entries[index].outcome) function(entries[index]);
    }
    uint64_t size() const { return count; }
    bool insert(GraphKey key, Answer answer, Budget& budget) {
        Answer previous;
        if (lookup(key, previous)) {
            if (previous.good != answer.good) throw std::runtime_error("conflicting completed memo outcomes");
            return false;
        }
        if (!capacity || (count + 1) * 10 > capacity * 7) grow(budget);
        size_t slot = hash_key(key) & (capacity - 1);
        while (entries[slot].outcome) slot = (slot + 1) & (capacity - 1);
        budget.reserve_state();
        entries[slot] = {key.lower, key.upper, static_cast<uint8_t>(answer.good ? 1 : 2), 0, answer.proof_id};
        ++count;
        return true;
    }
};

class SharedMemo {
    static constexpr size_t shard_count = 64;
    struct Shard { mutable std::mutex mutex; MemoTable table; };
    std::array<std::array<Shard, shard_count>, maximum_vertices + 1> levels;
public:
    using Counts = std::array<std::array<uint64_t, shard_count>, maximum_vertices + 1>;
    static size_t shard(GraphKey key) { return (hash_key(key) >> 32) & (shard_count - 1); }
    void reserve_empty(const Counts& counts, Budget& budget) {
        uint64_t required = budget.table_bytes.load();
        for (const auto& level : counts) for (auto count : level) {
            uint64_t bytes = MemoTable::reserved_bytes(count);
            if (bytes > budget.memory_bytes || required > budget.memory_bytes - bytes) throw SearchLimit("memory");
            required += bytes;
        }
        for (size_t level = 0; level < levels.size(); ++level)
            for (size_t shard_index = 0; shard_index < shard_count; ++shard_index) {
                budget.check(true);
                levels[level][shard_index].table.reserve_empty(counts[level][shard_index], budget);
            }
    }
    bool lookup(int level, GraphKey key, Answer& answer) const {
        const auto& target = levels[level][shard(key)];
        std::lock_guard<std::mutex> lock(target.mutex);
        return target.table.lookup(key, answer);
    }
    bool insert(int level, GraphKey key, Answer answer, Budget& budget) {
        auto& target = levels[level][shard(key)];
        std::lock_guard<std::mutex> lock(target.mutex);
        return target.table.insert(key, answer, budget);
    }
    template<class Function> void visit(int level, Function function) const {
        for (const auto& target : levels[level]) {
            std::lock_guard<std::mutex> lock(target.mutex);
            target.table.visit(function);
        }
    }
    uint64_t size(int level) const {
        uint64_t count = 0;
        for (const auto& target : levels[level]) {
            std::lock_guard<std::mutex> lock(target.mutex);
            count += target.table.size();
        }
        return count;
    }
};

struct Placement {
    uint16_t tree_index = 0;
    std::array<uint8_t, maximum_vertices> images{}, child_labels{};
    uint32_t child_id = 0;
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
    SharedMemo& memo;
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
                    try { raw_cache = std::make_unique<RawCacheEntry[]>(size_t{1} << cache_bits); }
                    catch (const std::bad_alloc&) {
                        budget.release((size_t{1} << cache_bits) * sizeof(RawCacheEntry));
                        throw SearchLimit("memory");
                    }
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
    Solver(int order, const Catalog& trees, Budget& limits, SharedMemo& shared, bool orbits, bool siblings, unsigned raw_cache_bits)
        : vertices(order), catalog(trees), budget(limits), memo(shared), use_orbits(orbits), order_siblings(siblings), cache_bits(raw_cache_bits) {}
    ~Solver() { if (raw_cache) budget.release(cache_bytes()); }

    uint64_t cache_bytes() const { return raw_cache ? (size_t{1} << cache_bits) * sizeof(RawCacheEntry) : 0; }
    template<class Function> void visit(int level, Function function) const { memo.visit(level, function); }
    uint64_t level_count(int level) const { return memo.size(level); }
    void reserve_restored(const SharedMemo::Counts& counts) { memo.reserve_empty(counts, budget); }
    void restore(int level, GraphKey key, bool good) {
        Answer previous;
        if (memo.lookup(level, key, previous)) throw std::runtime_error("duplicate checkpoint state");
        memo.insert(level, key, {good, 0}, budget);
    }
    bool known_good(int level, GraphKey key) const {
        if (level <= 2) return true;
        Answer answer;
        return memo.lookup(level, key, answer) && answer.good;
    }


    Answer evaluate(const CanonicalGraph& host, int level) {
        budget.check();
        if (level <= 2) return {true, 0};
        Answer cached;
        if (memo.lookup(level, host.key, cached)) { ++statistics.memo_hits; return cached; }
        ++statistics.states_by_level[level];
        std::array<uint8_t, maximum_vertices> host_degrees{};
        for (int vertex = 0; vertex < vertices; ++vertex) host_degrees[vertex] = static_cast<uint8_t>(population(host.adjacency[vertex]));
        std::sort(host_degrees.begin(), host_degrees.begin() + vertices, std::greater<uint8_t>());
        for (const auto& tree : catalog[level]) {
            bool feasible = true;
            for (int index = 0; index < level; ++index)
                if (tree.descending_degrees[index] > host_degrees[index]) { feasible = false; break; }
            Placement winner;
            std::array<uint8_t, maximum_vertices> images{};
            if (!feasible || !try_embedding(tree, host, 0, 0, images, winner)) {
                if (memo.insert(level, host.key, {false, 0}, budget)) ++statistics.bad_states;
                return {false, 0};
            }
        }
        Answer answer{true, 0};
        if (memo.insert(level, host.key, answer, budget)) ++statistics.good_states;
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
    std::string catalog, states, checkpoint, progress;
    double seconds = 60, checkpoint_seconds = 300;
    uint64_t memory_mib = 1024, output_mib = 1024, maximum_states = std::numeric_limits<uint64_t>::max();
    bool orbits = true, siblings = true, resume = false, inspect = false;
    unsigned cache_bits = 18, workers = 1;
    int stop_after_roots = 0;
};

Options parse_options(int count, char** arguments) {
    Options options;
    for (int index = 1; index < count; ++index) {
        std::string name = arguments[index];
        if (name == "--resume") { options.resume = true; continue; }
        if (name == "--no-orbits") { options.orbits = false; continue; }
        if (name == "--no-sibling-order") { options.siblings = false; continue; }
        if (index + 1 >= count) throw std::runtime_error("missing option value");
        std::string value = arguments[++index];
        if (name == "--n") {
            auto order = unsigned_number(value);
            if (order < 2 || order > maximum_vertices) throw std::runtime_error("n must be 2..13");
            options.vertices = static_cast<int>(order);
        } else if (name == "--trees") options.catalog = value;
        else if (name == "--states") options.states = value;
        else if (name == "--checkpoint") options.checkpoint = value;
        else if (name == "--inspect-checkpoint") { options.checkpoint = value; options.inspect = true; }
        else if (name == "--workers") {
            auto workers = unsigned_number(value);
            if (!workers || workers > 32) throw std::runtime_error("workers must be 1..32");
            options.workers = static_cast<unsigned>(workers);
        } else if (name == "--stop-after-roots") {
            auto roots = unsigned_number(value);
            if (!roots || roots > 1301) throw std::runtime_error("stop-after-roots must be positive");
            options.stop_after_roots = static_cast<int>(roots);
        }
        else if (name == "--progress") options.progress = value;
        else if (name == "--seconds" || name == "--checkpoint-seconds") {
            size_t used;
            double seconds = std::stod(value, &used);
            if (used != value.size() || !std::isfinite(seconds) || seconds <= 0)
                throw std::runtime_error("invalid time limit");
            if (name == "--seconds") options.seconds = seconds;
            else options.checkpoint_seconds = seconds;
        } else if (name == "--memory-mib") options.memory_mib = unsigned_number(value);
        else if (name == "--max-output-mib") options.output_mib = unsigned_number(value);
        else if (name == "--max-states") options.maximum_states = unsigned_number(value);
        else if (name == "--cache-bits") {
            auto bits = unsigned_number(value);
            if (bits && (bits < 10 || bits > 24)) throw std::runtime_error("cache bits must be 0 or 10..24");
            options.cache_bits = static_cast<unsigned>(bits);
        } else if (name == "--top") {
            size_t colon = value.find(':');
            if (colon == std::string::npos) throw std::runtime_error("top must be first:last");
            uint64_t first = unsigned_number(value.substr(0, colon)), last = unsigned_number(value.substr(colon + 1));
            if (first > 1301 || last > 1301 || first >= last) throw std::runtime_error("invalid top range");
            options.first_top = static_cast<int>(first); options.last_top = static_cast<int>(last);
        } else throw std::runtime_error("unknown option: " + name);
    }
    constexpr uint64_t largest_mib = std::numeric_limits<uint64_t>::max() / (1024 * 1024);
    if (!options.vertices || options.catalog.empty() || (!options.inspect && options.states.empty()) || options.checkpoint.empty() ||
        !options.memory_mib || !options.output_mib || !options.maximum_states ||
        options.memory_mib > largest_mib || options.output_mib > largest_mib)
        throw std::runtime_error("missing or invalid required option");
    if (options.last_top < 0) options.last_top = tree_counts[options.vertices];
    if (options.first_top >= options.last_top || options.last_top > tree_counts[options.vertices])
        throw std::runtime_error("top range exceeds catalog");
    if (options.stop_after_roots > options.last_top - options.first_top)
        throw std::runtime_error("root stop exceeds assigned scope");
    if (options.workers > 1 && !HAVE_TLS) throw std::runtime_error("parallel workers require thread-local nauty");
    if (options.inspect) {
        if (options.resume || !options.states.empty() || !options.progress.empty() || options.stop_after_roots)
            throw std::runtime_error("inspection accepts no mutable outputs or search controls");
        if (std::filesystem::is_symlink(options.checkpoint) || !std::filesystem::is_regular_file(options.checkpoint))
            throw std::runtime_error("inspection requires a regular checkpoint file");
        return options;
    }
    std::set<std::filesystem::path> paths;
    for (const auto& name : {options.catalog, options.states, options.checkpoint, options.progress,
                             options.states + ".partial", options.checkpoint + ".partial", options.checkpoint + ".lock",
                             options.progress.empty() ? std::string{} : options.progress + ".partial"}) {
        if (name.empty()) continue;
        if (!paths.insert(std::filesystem::weakly_canonical(name)).second)
            throw std::runtime_error("input and output paths overlap");
    }
    for (const auto& name : {options.states, options.checkpoint, options.progress,
                             options.states + ".partial", options.checkpoint + ".partial",
                             options.progress.empty() ? std::string{} : options.progress + ".partial"}) {
        if (name.empty()) continue;
        if (std::filesystem::is_symlink(name) || (std::filesystem::exists(name) && !std::filesystem::is_regular_file(name)))
            throw std::runtime_error("output must be a regular file");
        if (!options.resume && std::filesystem::exists(name)) throw std::runtime_error("output already exists");
    }
    if (options.resume && !std::filesystem::is_regular_file(options.checkpoint))
        throw std::runtime_error("checkpoint required for resume");
    if (!options.progress.empty() && std::filesystem::exists(options.progress))
        throw std::runtime_error("new progress path required");
    return options;
}

void validate_graph(GraphKey key, int vertices, int level) {
    int edges = vertices * (vertices - 1) / 2;
    if ((edges < 64 && (key.lower >> edges)) || (edges <= 64 && key.upper) || (edges > 64 && (key.upper >> (edges - 64))))
        throw std::runtime_error("graph has out-of-range edges");
    if (level < 3 || level >= vertices || __builtin_popcountll(key.lower) + population(key.upper) != level * (level - 1) / 2)
        throw std::runtime_error("graph edge count does not match level");
}

std::vector<uint8_t> proof_header(const Options& options, const Catalog& catalog) {
    std::vector<uint8_t> bytes;
    auto integer = [&](uint64_t value, unsigned width) {
        for (unsigned index = 0; index < width; ++index) bytes.push_back(static_cast<uint8_t>(value >> (8 * index)));
    };
    for (unsigned char byte : std::string("TPCRDP01")) integer(byte, 1);
    integer(options.vertices, 1); integer(options.first_top, 2); integer(options.last_top, 2);
    for (int level = 2; level <= options.vertices; ++level) {
        integer(catalog[level].size(), 2);
        std::vector<const Tree*> original(catalog[level].size());
        for (const auto& tree : catalog[level]) original[tree.index] = &tree;
        for (const auto* tree : original)
            for (int vertex = 1; vertex < level; ++vertex) integer(tree->parents[vertex], 1);
    }
    for (int top = options.first_top; top < options.last_top; ++top) integer(catalog[options.vertices][top].index, 2);
    return bytes;
}

void sync_directory(const std::string& path) {
    auto directory = std::filesystem::path(path).parent_path();
    if (directory.empty()) directory = ".";
    int descriptor = open(directory.c_str(), O_RDONLY);
    if (descriptor < 0) throw std::runtime_error("cannot open output directory");
    int result = fsync(descriptor);
    close(descriptor);
    if (result) throw std::runtime_error("output directory sync failed");
}

class FileLock {
    int descriptor;
public:
    explicit FileLock(const std::string& path) {
        descriptor = open(path.c_str(), O_CREAT | O_RDWR | O_NOFOLLOW, 0600);
        if (descriptor < 0) throw std::runtime_error("cannot open checkpoint lock");
        if (flock(descriptor, LOCK_EX | LOCK_NB)) { close(descriptor); throw std::runtime_error("checkpoint already in use"); }
    }
    ~FileLock() { close(descriptor); }
};

class BinaryWriter {
    int descriptor;
    uint64_t limit;
    std::array<uint8_t, 65536> buffer{};
    size_t used = 0;
public:
    uint64_t bytes = 0, checksum = 14695981039346656037ull;
    explicit BinaryWriter(const std::string& path, uint64_t maximum) : limit(maximum) {
        struct stat metadata{};
        if (!lstat(path.c_str(), &metadata)) {
            if (!S_ISREG(metadata.st_mode) || unlink(path.c_str())) throw std::runtime_error("invalid stale staging file");
        } else if (errno != ENOENT) throw std::runtime_error("cannot inspect staging file");
        descriptor = open(path.c_str(), O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW, 0600);
        if (descriptor < 0) throw std::runtime_error("cannot create output staging file");
    }
    ~BinaryWriter() { if (descriptor >= 0) close(descriptor); }
    void flush() {
        size_t offset = 0;
        while (offset < used) {
            ssize_t written = write(descriptor, buffer.data() + offset, used - offset);
            if (written < 0 && errno == EINTR) continue;
            if (written <= 0) throw std::runtime_error("output write failed");
            offset += static_cast<size_t>(written);
        }
        used = 0;
    }
    void integer(uint64_t value, unsigned width, bool hashing = true) {
        if (bytes > limit || width > limit - bytes) throw SearchLimit("output-size");
        for (unsigned index = 0; index < width; ++index) {
            uint8_t byte = static_cast<uint8_t>(value >> (8 * index));
            if (hashing) { checksum ^= byte; checksum *= 1099511628211ull; }
            buffer[used++] = byte;
            if (used == buffer.size()) flush();
        }
        bytes += width;
    }
    void finish() {
        flush();
        if (fsync(descriptor)) throw std::runtime_error("output sync failed");
        if (close(descriptor)) { descriptor = -1; throw std::runtime_error("output close failed"); }
        descriptor = -1;
    }
};

class BinaryReader {
    std::ifstream input;
public:
    uint64_t bytes = 0, checksum = 14695981039346656037ull;
    explicit BinaryReader(const std::string& path) : input(path, std::ios::binary) {
        if (!input) throw std::runtime_error("cannot read checkpoint");
    }
    uint64_t integer(unsigned width, bool hashing = true) {
        uint64_t value = 0;
        for (unsigned index = 0; index < width; ++index) {
            int next = input.get();
            if (next == EOF) throw std::runtime_error("truncated checkpoint");
            uint8_t byte = static_cast<uint8_t>(next);
            value |= uint64_t{byte} << (8 * index);
            if (hashing) { checksum ^= byte; checksum *= 1099511628211ull; }
        }
        bytes += width;
        return value;
    }
    void end() { if (input.get() != EOF || input.bad()) throw std::runtime_error("checkpoint trailing data or read error"); }
    void rewind() {
        input.clear();
        input.seekg(0);
        if (!input) throw std::runtime_error("cannot rewind checkpoint");
        bytes = 0;
        checksum = 14695981039346656037ull;
    }
};

std::array<uint64_t*, 7> statistic_fields(Statistics& statistics) {
    return {&statistics.canonical_calls, &statistics.embeddings, &statistics.memo_hits, &statistics.good_states,
            &statistics.bad_states, &statistics.degree_rejections, &statistics.raw_cache_hits};
}

uint64_t save_checkpoint(const Options& options, const std::vector<uint8_t>& header, Solver& solver,
                         const Budget& budget, int next_top) {
    BinaryWriter output(options.checkpoint + ".partial", options.output_mib * 1024 * 1024);
    for (unsigned char byte : std::string("TPCMEM01")) output.integer(byte, 1);
    output.integer(header.size(), 4);
    for (auto byte : header) output.integer(byte, 1);
    output.integer(options.orbits, 1); output.integer(options.siblings, 1); output.integer(options.cache_bits, 1);
    output.integer(next_top, 2); output.integer(budget.stored_states.load(), 8);
    auto fields = statistic_fields(solver.statistics);
    for (size_t index = 0; index < 7; ++index) output.integer(*fields[index], 8);
    for (auto value : solver.statistics.states_by_level) output.integer(value, 8);
    for (int level = 3; level < options.vertices; ++level)
        solver.visit(level, [&](const MemoEntry& entry) {
            output.integer(level, 1); output.integer(entry.outcome, 1);
            output.integer(entry.lower, 8); output.integer(entry.upper, 2);
        });
    output.integer(output.checksum, 8, false);
    output.finish();
    std::filesystem::rename(options.checkpoint + ".partial", options.checkpoint);
    sync_directory(options.checkpoint);
    return output.bytes;
}

std::array<uint64_t, 7> checkpoint_identity(const std::string& path) {
    struct stat metadata{};
    if (lstat(path.c_str(), &metadata) || !S_ISREG(metadata.st_mode))
        throw std::runtime_error("checkpoint must remain a regular file");
#ifdef __APPLE__
    auto modified = metadata.st_mtimespec, changed = metadata.st_ctimespec;
#else
    auto modified = metadata.st_mtim, changed = metadata.st_ctim;
#endif
    return {uint64_t(metadata.st_dev), uint64_t(metadata.st_ino), uint64_t(metadata.st_size),
            uint64_t(modified.tv_sec), uint64_t(modified.tv_nsec), uint64_t(changed.tv_sec), uint64_t(changed.tv_nsec)};
}

struct CheckpointData {
    int next_top = 0;
    uint64_t count = 0, checksum = 0;
    Statistics statistics;
};

template<class Function>
CheckpointData read_checkpoint(BinaryReader& input, const Options& options, const std::vector<uint8_t>& header,
                               uint64_t checkpoint_bytes, Budget& budget, Function visit) {
    CheckpointData data;
    for (unsigned char byte : std::string("TPCMEM01"))
        if (input.integer(1) != byte) throw std::runtime_error("checkpoint format differs");
    if (input.integer(4) != header.size()) throw std::runtime_error("checkpoint header size differs");
    for (auto byte : header)
        if (input.integer(1) != byte) throw std::runtime_error("checkpoint catalog or assigned scope differs");
    if (input.integer(1) != options.orbits || input.integer(1) != options.siblings || input.integer(1) != options.cache_bits)
        throw std::runtime_error("checkpoint search options differ");
    int next_top = static_cast<int>(input.integer(2));
    data.next_top = next_top;
    if (next_top < options.first_top || next_top > options.last_top) throw std::runtime_error("invalid checkpoint root cursor");
    uint64_t count = input.integer(8);
    data.count = count;
    if (count > budget.maximum_states || count > (std::numeric_limits<uint64_t>::max() - input.bytes - 176) / 12)
        throw std::runtime_error("checkpoint state count exceeds limit");
    auto fields = statistic_fields(data.statistics);
    for (size_t index = 0; index < 7; ++index) *fields[index] = input.integer(8);
    for (auto& value : data.statistics.states_by_level) value = input.integer(8);
    if (input.bytes + count * 12 + 8 != checkpoint_bytes)
        throw std::runtime_error("checkpoint length differs");
    uint64_t good = 0, bad = 0;
    for (uint64_t index = 0; index < count; ++index) {
        budget.check();
        int level = static_cast<int>(input.integer(1));
        unsigned outcome = static_cast<unsigned>(input.integer(1));
        GraphKey key{input.integer(8), static_cast<uint16_t>(input.integer(2))};
        validate_graph(key, options.vertices, level);
        if (outcome != 1 && outcome != 2) throw std::runtime_error("invalid checkpoint outcome");
        visit(level, key, outcome == 1);
        outcome == 1 ? ++good : ++bad;
    }
    uint64_t checksum = input.checksum;
    if (input.integer(8, false) != checksum) throw std::runtime_error("checkpoint checksum differs");
    input.end();
    data.checksum = checksum;
    if (good != data.statistics.good_states || bad != data.statistics.bad_states || good >= UINT32_MAX)
        throw std::runtime_error("checkpoint memo counts differ");
    budget.check(true);
    return data;
}

int load_checkpoint(const Options& options, const std::vector<uint8_t>& header, Solver& solver, Budget& budget) {
    auto identity = checkpoint_identity(options.checkpoint);
    if (identity[2] > options.output_mib * 1024 * 1024)
        throw std::runtime_error("checkpoint exceeds output limit");
    BinaryReader input(options.checkpoint);
    SharedMemo::Counts counts{};
    auto counted = read_checkpoint(input, options, header, identity[2], budget,
        [&](int level, GraphKey key, bool) { ++counts[level][SharedMemo::shard(key)]; });
    if (checkpoint_identity(options.checkpoint) != identity)
        throw std::runtime_error("checkpoint changed during count pass");
    solver.reserve_restored(counts);
    input.rewind();
    auto restored = read_checkpoint(input, options, header, identity[2], budget,
        [&](int level, GraphKey key, bool good) { solver.restore(level, key, good); });
    if (checkpoint_identity(options.checkpoint) != identity || counted.count != restored.count ||
        counted.next_top != restored.next_top || counted.checksum != restored.checksum)
        throw std::runtime_error("checkpoint changed between restore passes");
    solver.statistics = restored.statistics;
    int next_top = restored.next_top;
    Adjacency complete{};
    for (int vertex = 0; vertex < options.vertices; ++vertex) complete[vertex] = ((1u << options.vertices) - 1) ^ (1u << vertex);
    auto catalog = read_catalog(options.catalog, options.vertices);
    for (int top = options.first_top; top < next_top; ++top) {
        auto residual = complete;
        for (int vertex = 0; vertex < options.vertices; ++vertex) residual[vertex] &= ~catalog[options.vertices][top].adjacency[vertex];
        if (!solver.known_good(options.vertices - 1, canonicalize(residual, options.vertices).key))
            throw std::runtime_error("checkpoint completed root lacks winning child");
    }
    return next_top;
}

bool same_bytes(const std::string& first, const std::string& second) {
    if (std::filesystem::file_size(first) != std::filesystem::file_size(second)) return false;
    std::ifstream left(first, std::ios::binary), right(second, std::ios::binary);
    std::array<char, 65536> a{}, b{};
    while (left) {
        left.read(a.data(), a.size()); right.read(b.data(), b.size());
        if (left.gcount() != right.gcount() || !std::equal(a.begin(), a.begin() + left.gcount(), b.begin())) return false;
    }
    if (left.bad() || right.bad()) throw std::runtime_error("state comparison read failed");
    return true;
}

uint64_t publish_states(const Options& options, const std::vector<uint8_t>& header, Solver& solver, Budget& budget) {
    struct StateMemory {
        Budget& budget;
        uint64_t bytes;
        StateMemory(Budget& limits, uint64_t size) : budget(limits), bytes(size) { budget.allocate(bytes); }
        ~StateMemory() { budget.release(bytes); }
    };
    uint64_t count = solver.statistics.good_states;
    if (count >= UINT32_MAX) throw SearchLimit("proof-nodes");
    unsigned width = static_cast<unsigned>((options.vertices * (options.vertices - 1) / 2 + 7) / 8);
    uint64_t bytes = 16 + header.size() + count * width;
    if (bytes > options.output_mib * 1024 * 1024) throw SearchLimit("output-size");
    BinaryWriter output(options.states + ".partial", options.output_mib * 1024 * 1024);
    for (unsigned char byte : std::string("TPCGST01")) output.integer(byte, 1);
    for (auto byte : header) output.integer(byte, 1);
    output.integer(count, 8);
    uint64_t written = 0;
    for (int level = 3; level < options.vertices; ++level) {
        uint64_t good = 0;
        solver.visit(level, [&](const MemoEntry& entry) { if (entry.outcome == 1) ++good; });
        {
            StateMemory allocation(budget, good * sizeof(GraphKey));
            std::vector<GraphKey> keys;
            keys.reserve(good);
            solver.visit(level, [&](const MemoEntry& entry) { if (entry.outcome == 1) keys.push_back({entry.lower, entry.upper}); });
            std::sort(keys.begin(), keys.end(), [&](GraphKey left, GraphKey right) {
                budget.check();
                return left.upper == right.upper ? left.lower < right.lower : left.upper < right.upper;
            });
            for (auto key : keys) {
                budget.check();
                output.integer(key.lower, std::min(width, 8u));
                if (width > 8) output.integer(key.upper, width - 8);
                ++written;
            }
        }
    }
    if (written != count || output.bytes != bytes) throw std::runtime_error("final state count differs");
    budget.check(true);
    output.finish();
    if (std::filesystem::exists(options.states)) {
        if (!options.resume || !same_bytes(options.states + ".partial", options.states))
            throw std::runtime_error("existing state certificate differs");
    } else if (link((options.states + ".partial").c_str(), options.states.c_str())) {
        throw std::runtime_error("state certificate publication failed");
    }
    if (unlink((options.states + ".partial").c_str())) throw std::runtime_error("state staging cleanup failed");
    sync_directory(options.states);
    return bytes;
}

void inspect_checkpoint(const Options& options, const std::vector<uint8_t>& header, const Catalog& catalog, Budget& budget) {
    const uint64_t bytes = std::filesystem::file_size(options.checkpoint);
    if (bytes > options.output_mib * 1024 * 1024) throw std::runtime_error("checkpoint exceeds output limit");
    BinaryReader input(options.checkpoint);
    for (unsigned char byte : std::string("TPCMEM01"))
        if (input.integer(1) != byte) throw std::runtime_error("checkpoint format differs");
    if (input.integer(4) != header.size()) throw std::runtime_error("checkpoint header size differs");
    for (auto byte : header)
        if (input.integer(1) != byte) throw std::runtime_error("checkpoint catalog or assigned scope differs");
    if (input.integer(1) != options.orbits || input.integer(1) != options.siblings || input.integer(1) != options.cache_bits)
        throw std::runtime_error("checkpoint search options differ");
    int next_top = static_cast<int>(input.integer(2));
    if (next_top < options.first_top || next_top > options.last_top) throw std::runtime_error("invalid checkpoint root cursor");
    uint64_t count = input.integer(8);
    if (count > budget.maximum_states || count > (std::numeric_limits<uint64_t>::max() - input.bytes - 176) / 12)
        throw std::runtime_error("checkpoint state count exceeds limit");
    Statistics statistics;
    auto fields = statistic_fields(statistics);
    for (size_t index = 0; index < 7; ++index) *fields[index] = input.integer(8);
    for (auto& value : statistics.states_by_level) value = input.integer(8);
    if (input.bytes + count * 12 + 8 != bytes) throw std::runtime_error("checkpoint length differs");
    std::vector<GraphKey> required;
    std::vector<bool> found;
    Adjacency complete{};
    for (int vertex = 0; vertex < options.vertices; ++vertex) complete[vertex] = ((1u << options.vertices) - 1) ^ (1u << vertex);
    if (options.vertices > 3) {
        for (int top = options.first_top; top < next_top; ++top) {
            budget.check();
            auto residual = complete;
            for (int vertex = 0; vertex < options.vertices; ++vertex) residual[vertex] &= ~catalog[options.vertices][top].adjacency[vertex];
            required.push_back(canonicalize(residual, options.vertices).key);
        }
        found.resize(required.size());
    }
    uint64_t good = 0, bad = 0;
    for (uint64_t index = 0; index < count; ++index) {
        budget.check();
        int level = static_cast<int>(input.integer(1));
        unsigned outcome = static_cast<unsigned>(input.integer(1));
        GraphKey key{input.integer(8), static_cast<uint16_t>(input.integer(2))};
        validate_graph(key, options.vertices, level);
        if (outcome != 1 && outcome != 2) throw std::runtime_error("invalid checkpoint outcome");
        outcome == 1 ? ++good : ++bad;
        if (outcome == 1 && level == options.vertices - 1)
            for (size_t root = 0; root < required.size(); ++root)
                if (key == required[root]) found[root] = true;
    }
    uint64_t checksum = input.checksum;
    if (input.integer(8, false) != checksum) throw std::runtime_error("checkpoint checksum differs");
    input.end();
    if (good != statistics.good_states || bad != statistics.bad_states || good >= UINT32_MAX)
        throw std::runtime_error("checkpoint memo counts differ");
    if (std::find(found.begin(), found.end(), false) != found.end())
        throw std::runtime_error("checkpoint completed root lacks winning child");
    budget.check(true);
    std::cout << "{\"status\":\"valid\",\"n\":" << options.vertices
              << ",\"top_first\":" << options.first_top << ",\"top_last\":" << options.last_top
              << ",\"next_top\":" << next_top << ",\"completed\":" << next_top - options.first_top
              << ",\"stored_states\":" << count << ",\"good_states\":" << good << ",\"bad_states\":" << bad
              << ",\"checkpoint_bytes\":" << bytes << ",\"orbits\":" << (options.orbits ? "true" : "false")
              << ",\"siblings\":" << (options.siblings ? "true" : "false") << ",\"cache_bits\":" << options.cache_bits
              << ",\"checksum_valid\":true,\"root_children_checked\":true,\"duplicate_states_checked\":false}\n";
}

Statistics aggregate_statistics(const Statistics& initial, const std::vector<std::unique_ptr<Solver>>& workers) {
    Statistics total = initial;
    for (const auto& worker : workers) {
        auto fields = statistic_fields(total);
        auto values = statistic_fields(worker->statistics);
        for (size_t index = 0; index < fields.size(); ++index) *fields[index] += *values[index];
        for (size_t level = 0; level < total.states_by_level.size(); ++level)
            total.states_by_level[level] += worker->statistics.states_by_level[level];
    }
    return total;
}

int main(int argument_count, char** arguments) {
    std::signal(SIGINT, handle_signal); std::signal(SIGTERM, handle_signal);
    const auto started = std::chrono::steady_clock::now();
    const auto cpu_started = std::clock();
    try {
        auto options = parse_options(argument_count, arguments);
        nauty_check(WORDSIZE, 1, options.vertices, NAUTYVERSIONID);
        Budget budget;
        budget.started = started; budget.seconds = options.seconds;
        budget.memory_bytes = options.memory_mib * 1024 * 1024;
        budget.maximum_states = options.maximum_states;
        auto catalog = read_catalog(options.catalog, options.vertices);
        auto header = proof_header(options, catalog);
        if (options.inspect) { inspect_checkpoint(options, header, catalog, budget); return 0; }
        FileLock lock(options.checkpoint + ".lock");
        SharedMemo memo;
        Solver solver(options.vertices, catalog, budget, memo, options.orbits, options.siblings, options.cache_bits);
        int next_top = options.resume ? load_checkpoint(options, header, solver, budget) : options.first_top;
        int resumed_completed = next_top - options.first_top;
        uint64_t resumed_states = budget.stored_states.load();
        uint64_t checkpoint_bytes = options.resume ? std::filesystem::file_size(options.checkpoint) : 0;
        uint64_t states_bytes = 0, checkpoints_written = 0;
        bool good = true;
        std::string stop_reason;
        auto next_checkpoint = std::chrono::steady_clock::now() + std::chrono::duration<double>(options.checkpoint_seconds);
        auto checkpoint = [&] {
            checkpoint_bytes = save_checkpoint(options, header, solver, budget, next_top);
            ++checkpoints_written;
            next_checkpoint = std::chrono::steady_clock::now() + std::chrono::duration<double>(options.checkpoint_seconds);
        };
        auto write_progress = [&](const char* status) {
            if (options.progress.empty()) return;
            auto temporary = options.progress + ".partial";
            if (std::filesystem::is_symlink(temporary)) throw std::runtime_error("progress staging symlink");
            std::ofstream output(temporary);
            if (!output) throw std::runtime_error("cannot create progress snapshot");
            output << std::setprecision(10) << "{\"status\":\"" << status << "\",\"n\":" << options.vertices
                   << ",\"top\":" << next_top << ",\"completed\":" << next_top - options.first_top
                   << ",\"workers\":" << options.workers
                   << ",\"stored_states\":" << budget.stored_states.load() << ",\"good_states\":" << solver.statistics.good_states
                   << ",\"bad_states\":" << solver.statistics.bad_states << ",\"checkpoint_bytes\":" << checkpoint_bytes
                   << ",\"checkpoints_written\":" << checkpoints_written
                   << ",\"wall_seconds\":" << std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count() << "}\n";
            output.flush(); output.close();
            if (!output) throw std::runtime_error("progress snapshot write failed");
            std::filesystem::rename(temporary, options.progress);
        };
        if (!options.resume) checkpoint();
        const Statistics initial = solver.statistics;
        const int dispatch_end = options.stop_after_roots ? options.first_top + options.stop_after_roots : options.last_top;
        std::atomic<int> claimed{next_top};
        std::array<std::atomic<bool>, 1301> completed{};
        for (int root = options.first_top; root < next_top; ++root) completed[root].store(true);
        std::vector<std::unique_ptr<Solver>> workers;
        const unsigned worker_count = static_cast<unsigned>(std::min<int>(options.workers, std::max(0, dispatch_end - next_top)));
        for (unsigned index = 0; index < worker_count; ++index)
            workers.push_back(std::make_unique<Solver>(options.vertices, catalog, budget, memo, options.orbits, options.siblings, options.cache_bits));
        WorkerControl control;
        control.register_workers(worker_count);
        budget.workers = &control;
        std::vector<std::thread> threads;
        threads.reserve(worker_count);
        auto join_workers = [&] {
            control.resume();
            for (auto& thread : threads) if (thread.joinable()) thread.join();
        };
        auto fold = [&] {
            solver.statistics = aggregate_statistics(initial, workers);
            while (next_top < options.last_top && completed[next_top].load(std::memory_order_acquire)) ++next_top;
        };
        try {
            for (unsigned index = 0; index < worker_count; ++index) {
                threads.emplace_back([&, index] {
                    worker_thread = true;
                    try {
                        Adjacency complete{};
                        for (int vertex = 0; vertex < options.vertices; ++vertex) complete[vertex] = ((1u << options.vertices) - 1) ^ (1u << vertex);
                        for (;;) {
                            budget.check(true);
                            int root = claimed.fetch_add(1, std::memory_order_relaxed);
                            if (root >= dispatch_end) break;
                            auto residual = complete;
                            for (int vertex = 0; vertex < options.vertices; ++vertex) residual[vertex] &= ~catalog[options.vertices][root].adjacency[vertex];
                            auto canonical = workers[index]->normalize(residual);
                            if (!workers[index]->evaluate(canonical, options.vertices - 1).good) {
                                control.stop_rejected_root();
                                break;
                            }
                            completed[root].store(true, std::memory_order_release);
                        }
                    } catch (const SearchLimit& limit) { control.stop_limit(limit.what()); }
                    catch (...) { control.stop_failure(std::current_exception()); }
                    worker_thread = false;
                    control.finished();
                });
            }
            auto next_progress = std::chrono::steady_clock::now();
            bool first_root_checkpoint = next_top == options.first_top;
            while (control.active()) {
                try { budget.check(true); }
                catch (const SearchLimit& limit) { control.stop_limit(limit.what()); }
                if (control.stopped()) break;
                auto now = std::chrono::steady_clock::now();
                bool first_complete = first_root_checkpoint && completed[options.first_top].load(std::memory_order_acquire);
                bool checkpoint_due = now >= next_checkpoint || first_complete;
                if (checkpoint_due || now >= next_progress) {
                    control.pause();
                    fold();
                    if (checkpoint_due) { checkpoint(); first_root_checkpoint = false; }
                    write_progress("running");
                    next_progress = std::chrono::steady_clock::now() +
                        std::chrono::duration_cast<std::chrono::steady_clock::duration>(std::chrono::duration<double>(std::min(30.0, options.checkpoint_seconds)));
                    control.resume();
                }
                control.wait();
            }
            join_workers();
        } catch (...) {
            control.stop_failure(std::current_exception());
            if (threads.size() < worker_count) control.finished(worker_count - threads.size());
            join_workers();
            throw;
        }
        control.rethrow_failure();
        fold();
        stop_reason = control.stop_reason();
        good = !control.root_failed();
        if (good && stop_reason.empty() && dispatch_end < options.last_top) stop_reason = "roots";
        if (good && stop_reason.empty() && next_top != options.last_top) throw std::runtime_error("root completion prefix incomplete");
        try {
            checkpoint();
            if (good && stop_reason.empty()) states_bytes = publish_states(options, header, solver, budget);
        } catch (const SearchLimit& limit) {
            stop_reason = limit.what();
            checkpoint();
        }
        const char* status = stop_reason.empty() ? (good ? "complete" : "online-false") : "incomplete";
        write_progress(status);
        struct rusage usage{};
        if (getrusage(RUSAGE_SELF, &usage)) throw std::runtime_error("resource accounting failed");
        uint64_t peak = static_cast<uint64_t>(usage.ru_maxrss);
#ifndef __APPLE__
        peak *= 1024;
#endif
        const auto& statistics = solver.statistics;
        uint64_t raw_cache_bytes = 0;
        for (const auto& worker : workers) raw_cache_bytes += worker->cache_bytes();
        std::cout << std::setprecision(10) << "{\"status\":\"" << status << "\",\"stop_reason\":\"" << stop_reason
                  << "\",\"n\":" << options.vertices << ",\"top_first\":" << options.first_top
                  << ",\"top_last\":" << options.last_top << ",\"completed\":" << next_top - options.first_top
                  << ",\"workers\":" << options.workers << ",\"worker_threads\":" << worker_count
                  << ",\"nodes\":" << statistics.good_states << ",\"states_bytes\":" << states_bytes
                  << ",\"checkpoint_bytes\":" << checkpoint_bytes << ",\"resumed\":" << (options.resume ? "true" : "false")
                  << ",\"resumed_states\":" << resumed_states << ",\"resumed_completed\":" << resumed_completed
                  << ",\"checkpoints_written\":" << checkpoints_written
                  << ",\"cpu_seconds\":" << static_cast<double>(std::clock() - cpu_started) / CLOCKS_PER_SEC
                  << ",\"wall_seconds\":" << std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count()
                  << ",\"peak_memory_bytes\":" << peak << ",\"memo_bytes\":" << budget.table_bytes.load() - raw_cache_bytes
                  << ",\"stored_states\":" << budget.stored_states.load() << ",\"good_states\":" << statistics.good_states
                  << ",\"bad_states\":" << statistics.bad_states << ",\"memo_hits\":" << statistics.memo_hits
                  << ",\"canonical_calls\":" << statistics.canonical_calls << ",\"embeddings\":" << statistics.embeddings
                  << ",\"states_by_level\":{";
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
