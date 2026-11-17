// parallel state reconstruction
// sorted states > per-level immutable child index > bounded worker results > ordered proof
// level barrier > child-index replacement; stream > unchanged independent checkers
#define main residual_solver_main
#include "graph_helpers.cpp"
#undef main
#include <atomic>
#include <cerrno>
#include <condition_variable>
#include <exception>
#include <fcntl.h>
#include <iomanip>
#include <mutex>
#include <poll.h>
#include <thread>
#include <unistd.h>
#ifndef USE_TLS
#error "parallel reconstruction requires TLS-enabled nauty"
#endif

struct State {
    GraphKey key;
    uint8_t level = 0;
};

bool state_less(const State& left, const State& right) {
    if (left.level != right.level) return left.level < right.level;
    if (left.key.upper != right.key.upper) return left.key.upper < right.key.upper;
    return left.key.lower < right.key.lower;
}

class Input {
    std::ifstream stream;
public:
    uint64_t bytes = 0;
    bool capture = false;
    std::vector<uint8_t> header;
    explicit Input(const std::string& path) {
        if (!std::filesystem::is_regular_file(path)) throw std::runtime_error("input must be a regular file");
        stream.open(path, std::ios::binary);
        if (!stream) throw std::runtime_error("cannot open input");
    }
    uint64_t integer(unsigned width) {
        uint64_t value = 0;
        for (unsigned offset = 0; offset < width; ++offset) {
            int byte = stream.get();
            if (byte == EOF) throw std::runtime_error("truncated input");
            value |= uint64_t{static_cast<uint8_t>(byte)} << (8 * offset);
            if (capture) header.push_back(static_cast<uint8_t>(byte));
            ++bytes;
        }
        return value;
    }
    void magic(const std::string& expected) {
        for (unsigned char byte : expected)
            if (integer(1) != byte) throw std::runtime_error("invalid input format");
    }
    void end() {
        if (stream.get() != EOF || stream.bad()) throw std::runtime_error("trailing bytes or input error");
    }
};

struct Header {
    int order = 0, first = 0, last = 0;
    Catalog catalog;
    std::vector<uint8_t> bytes;
};

Header read_header(Input& input) {
    input.capture = true;
    input.magic("TPCRDP01");
    Header header;
    header.order = static_cast<int>(input.integer(1));
    if (header.order < 2 || header.order > maximum_vertices) throw std::runtime_error("order must be 2..13");
    header.first = static_cast<int>(input.integer(2));
    header.last = static_cast<int>(input.integer(2));
    if (header.first >= header.last || header.last > tree_counts[header.order])
        throw std::runtime_error("invalid assigned range");
    for (int size = 2; size <= header.order; ++size) {
        if (input.integer(2) != static_cast<unsigned>(tree_counts[size]))
            throw std::runtime_error("wrong catalog count");
        for (int index = 0; index < tree_counts[size]; ++index) {
            Tree tree;
            tree.size = size;
            tree.index = index;
            for (int vertex = 1; vertex < size; ++vertex) {
                unsigned parent = static_cast<unsigned>(input.integer(1));
                if (parent >= static_cast<unsigned>(vertex)) throw std::runtime_error("invalid catalog parent");
                tree.parents[vertex] = static_cast<uint8_t>(parent);
                tree.adjacency[vertex] |= 1u << parent;
                tree.adjacency[parent] |= 1u << vertex;
            }
            prepare_tree(tree);
            header.catalog[size].push_back(tree);
        }
        std::stable_sort(header.catalog[size].begin(), header.catalog[size].end(),
                         [](const Tree& left, const Tree& right) { return left.maximum_degree > right.maximum_degree; });
    }
    for (int top = header.first; top < header.last; ++top)
        if (input.integer(2) != static_cast<unsigned>(header.catalog[header.order][top].index))
            throw std::runtime_error("assigned top index differs");
    input.capture = false;
    header.bytes = std::move(input.header);
    return header;
}

std::atomic<int> reconstruction_signal{0};
static_assert(std::atomic<int>::is_always_lock_free, "signal atomic must be lock-free");

void reconstruction_interrupt(int number) {
    reconstruction_signal.store(number, std::memory_order_relaxed);
}

struct ReconstructionLimits {
    std::chrono::steady_clock::time_point started = std::chrono::steady_clock::now();
    double seconds = 0;
    uint64_t memory_bytes = 0, allocated_bytes = 0;
    std::atomic<bool> cancelled{false};

    void check(uint64_t& polls, bool force = false) const {
        if (!force && (++polls & 1023u)) return;
        if (reconstruction_signal.load(std::memory_order_relaxed)) throw SearchLimit("signal");
        if (cancelled.load(std::memory_order_relaxed)) throw SearchLimit("cancelled");
        if (std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count() >= seconds)
            throw SearchLimit("time");
        struct rusage usage{};
        if (getrusage(RUSAGE_SELF, &usage)) throw std::runtime_error("resource accounting failed");
#ifdef __APPLE__
        uint64_t peak = static_cast<uint64_t>(usage.ru_maxrss);
#else
        uint64_t peak = static_cast<uint64_t>(usage.ru_maxrss) * 1024;
#endif
        if (peak > memory_bytes) throw SearchLimit("memory");
    }

    void reserve(uint64_t bytes) {
        uint64_t polls = 0;
        check(polls, true);
        if (bytes > memory_bytes || allocated_bytes > memory_bytes - bytes) throw SearchLimit("memory");
        allocated_bytes += bytes;
    }

    void release(uint64_t bytes) {
        if (bytes > allocated_bytes) throw std::logic_error("memory accounting underflow");
        allocated_bytes -= bytes;
    }
};

std::vector<State> read_parallel_states(Input& input, const Header& header, ReconstructionLimits& limits,
                                       std::array<size_t, maximum_vertices + 1>& counts) {
    uint64_t count = input.integer(8);
    if (count >= UINT32_MAX || count > std::numeric_limits<size_t>::max() / sizeof(State))
        throw SearchLimit("state-count");
    std::vector<State> states;
    limits.reserve(count * sizeof(State));
    states.reserve(static_cast<size_t>(count));
    if (states.capacity() > count) limits.reserve((states.capacity() - count) * sizeof(State));
    const unsigned width = static_cast<unsigned>((header.order * (header.order - 1) / 2 + 7) / 8);
    uint64_t polls = 0;
    for (uint64_t index = 0; index < count; ++index) {
        limits.check(polls);
        State state;
        state.key.lower = input.integer(std::min(width, 8u));
        if (width > 8) state.key.upper = static_cast<uint16_t>(input.integer(width - 8));
        int edges = __builtin_popcountll(state.key.lower) + population(state.key.upper);
        for (int level = 3; level < header.order; ++level)
            if (edges == level * (level - 1) / 2) state.level = static_cast<uint8_t>(level);
        if (!state.level) throw std::runtime_error("nontriangular or terminal state");
        validate_graph(state.key, header.order, state.level);
        if (!states.empty() && !state_less(states.back(), state)) throw std::runtime_error("states are duplicate or unsorted");
        states.push_back(state);
        ++counts[state.level];
    }
    input.end();
    limits.check(polls, true);
    return states;
}

class ChildIndex {
    ReconstructionLimits& limits;
    std::unique_ptr<MemoEntry[]> entries;
    size_t capacity = 0;
public:
    explicit ChildIndex(ReconstructionLimits& budget) : limits(budget) {}
    ChildIndex(const ChildIndex&) = delete;
    ChildIndex& operator=(const ChildIndex&) = delete;

    void clear() {
        entries.reset();
        limits.release(capacity * sizeof(MemoEntry));
        capacity = 0;
    }

    void build(const std::vector<State>& states, size_t first, size_t last) {
        clear();
        if (first == last) return;
        size_t wanted = 1024;
        const uint64_t count = last - first;
        while (count * 10 > uint64_t{wanted} * 7) {
            if (wanted > std::numeric_limits<size_t>::max() / 2 / sizeof(MemoEntry))
                throw SearchLimit("memory");
            wanted *= 2;
        }
        limits.reserve(wanted * sizeof(MemoEntry));
        try {
            entries = std::make_unique<MemoEntry[]>(wanted);
        } catch (...) {
            limits.release(wanted * sizeof(MemoEntry));
            throw;
        }
        capacity = wanted;
        uint64_t polls = 0;
        for (size_t index = first; index < last; ++index) {
            limits.check(polls);
            const auto key = states[index].key;
            size_t slot = hash_key(key) & (capacity - 1);
            while (entries[slot].outcome) {
                if (entries[slot].lower == key.lower && entries[slot].upper == key.upper)
                    throw std::runtime_error("duplicate child index key");
                slot = (slot + 1) & (capacity - 1);
            }
            entries[slot] = {key.lower, key.upper, 1, 0, static_cast<uint32_t>(index + 1)};
        }
        limits.check(polls, true);
    }

    bool lookup(GraphKey key, Answer& answer) const {
        if (!capacity) return false;
        size_t slot = hash_key(key) & (capacity - 1);
        while (entries[slot].outcome) {
            const auto& entry = entries[slot];
            if (entry.lower == key.lower && entry.upper == key.upper) {
                answer = {true, entry.proof_id};
                return true;
            }
            slot = (slot + 1) & (capacity - 1);
        }
        return false;
    }
};
class StreamProofWriter {
    ReconstructionLimits& budget;
    uint64_t maximum_bytes;
    uint32_t nodes = 0;
    uint64_t polls = 0;
    int original_flags;
    std::array<uint8_t, 64 * 1024> buffer{};
    size_t used = 0;

    void flush() {
        size_t offset = 0;
        while (offset < used) {
            budget.check(polls, true);
            ssize_t written = write(STDOUT_FILENO, buffer.data() + offset, used - offset);
            if (written > 0) {
                offset += static_cast<size_t>(written);
                continue;
            }
            if (written < 0 && errno == EINTR) continue;
            if (written < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
                pollfd descriptor{STDOUT_FILENO, POLLOUT, 0};
                int result = poll(&descriptor, 1, 100);
                if (result < 0 && errno != EINTR) throw std::runtime_error("stream poll failed");
                continue;
            }
            throw std::runtime_error("proof stream write failed");
        }
        used = 0;
    }

    void placement(const Placement& choice, int level, int vertices) {
        integer(choice.tree_index, 2);
        for (int vertex = 0; vertex < level; ++vertex) integer(choice.images[vertex], 1);
        integer(choice.child_id, 4);
        for (int vertex = 0; vertex < vertices; ++vertex) integer(choice.child_labels[vertex], 1);
    }

public:
    uint64_t bytes = 0;
    StreamProofWriter(ReconstructionLimits& limits, uint64_t maximum) : budget(limits), maximum_bytes(maximum) {
        original_flags = fcntl(STDOUT_FILENO, F_GETFL);
        if (original_flags < 0 || fcntl(STDOUT_FILENO, F_SETFL, original_flags | O_NONBLOCK) < 0)
            throw std::runtime_error("cannot configure bounded stdout");
    }
    ~StreamProofWriter() { fcntl(STDOUT_FILENO, F_SETFL, original_flags); }
    StreamProofWriter(const StreamProofWriter&) = delete;
    StreamProofWriter& operator=(const StreamProofWriter&) = delete;

    void integer(uint64_t value, unsigned width) {
        if (width > maximum_bytes - bytes) throw SearchLimit("proof-size");
        for (unsigned index = 0; index < width; ++index) {
            if (used == buffer.size()) flush();
            buffer[used++] = static_cast<uint8_t>(value >> (8 * index));
        }
        bytes += width;
    }
    uint32_t node(GraphKey key, int level, int vertices, const std::vector<Placement>& choices) {
        if (nodes == UINT32_MAX) throw SearchLimit("proof-nodes");
        integer(1, 1); integer(level, 1); integer(key.lower, 8); integer(key.upper, 2);
        for (const auto& choice : choices) placement(choice, level, vertices);
        return ++nodes;
    }
    void root(const Placement& choice, int vertices) { integer(2, 1); placement(choice, vertices, vertices); }
    void finish_frames() { flush(); }
    void finish(int roots) {
        integer(3, 1); integer(roots, 2);
        flush();
    }
};

struct ReconstructionStatistics {
    uint64_t embeddings = 0, canonical_calls = 0, polls = 0;
};

class StateReconstructor {
    const Header& header;
    const ChildIndex& children;
    ReconstructionLimits& limits;
    ReconstructionStatistics& statistics;

    bool embedding(const Tree& tree, const CanonicalGraph& host, int position, unsigned used,
                   std::array<uint8_t, maximum_vertices>& images, Placement& choice) {
        limits.check(statistics.polls);
        if (position == tree.size) {
            ++statistics.embeddings;
            choice.tree_index = static_cast<uint16_t>(tree.index);
            for (int vertex = 0; vertex < tree.size; ++vertex) choice.images[tree.order[vertex]] = images[vertex];
            if (tree.size <= 3) {
                choice.child_id = 0;
                for (int vertex = 0; vertex < header.order; ++vertex) choice.child_labels[vertex] = static_cast<uint8_t>(vertex);
                return true;
            }
            Adjacency residual = host.adjacency;
            for (int vertex = 1; vertex < tree.size; ++vertex) {
                int left = images[tree.parent_positions[vertex]], right = images[vertex];
                residual[left] &= ~(1u << right);
                residual[right] &= ~(1u << left);
            }
            ++statistics.canonical_calls;
            auto canonical = canonicalize(residual, header.order);
            Answer answer;
            if (!children.lookup(canonical.key, answer)) return false;
            choice.child_id = answer.proof_id;
            choice.child_labels = canonical.original_labels;
            return true;
        }
        int parent = tree.parent_positions[position];
        unsigned candidates = parent < 0 ? host.root_representatives : host.adjacency[images[parent]] & ~used;
        int sibling = tree.previous_siblings[position];
        if (sibling >= 0) candidates &= ~((1u << (images[sibling] + 1)) - 1);
        int children_needed = tree.degrees[position] - (parent >= 0 ? 1 : 0);
        while (candidates) {
            int candidate = first_vertex(candidates);
            candidates &= candidates - 1;
            if (population(host.adjacency[candidate] & ~used) < children_needed) continue;
            images[position] = static_cast<uint8_t>(candidate);
            if (embedding(tree, host, position + 1, used | (1u << candidate), images, choice)) return true;
        }
        return false;
    }

public:
    StateReconstructor(const Header& catalog, const ChildIndex& index, ReconstructionLimits& budget,
                       ReconstructionStatistics& counters)
        : header(catalog), children(index), limits(budget), statistics(counters) {}

    void reconstruct(const State& state, std::vector<Placement>& choices) {
        limits.check(statistics.polls);
        ++statistics.canonical_calls;
        auto host = canonicalize(decode_graph(state.key, header.order), header.order);
        if (!(host.key == state.key)) throw std::runtime_error("state canonical form differs from expansion backend");
        choices.clear();
        for (const auto& tree : header.catalog[state.level]) {
            Placement choice;
            std::array<uint8_t, maximum_vertices> images{};
            if (!embedding(tree, host, 0, 0, images, choice))
                throw std::runtime_error("state has no supplied winning continuation");
            choices.push_back(choice);
        }
    }
};

struct ResultSlot {
    std::vector<Placement> choices;
    bool ready = false;
};

unsigned reconstruct_level(const Header& header, const std::vector<State>& states, size_t first, size_t last,
                           const ChildIndex& children, unsigned requested_workers, StreamProofWriter& writer,
                           ReconstructionLimits& limits, ReconstructionStatistics& total) {
    if (first == last) return 0;
    const unsigned worker_count = static_cast<unsigned>(std::min<size_t>(requested_workers, last - first));
    const size_t window = std::min<size_t>(2 * worker_count, last - first);
    const size_t choices_per_state = header.catalog[states[first].level].size();
    const uint64_t slot_bytes = window * (sizeof(ResultSlot) + choices_per_state * sizeof(Placement));
    limits.reserve(slot_bytes);
    std::vector<ResultSlot> slots(window);
    for (auto& slot : slots) slot.choices.reserve(choices_per_state);
    std::vector<ReconstructionStatistics> statistics(worker_count);
    std::vector<std::thread> threads;
    threads.reserve(worker_count);
    std::mutex mutex;
    std::condition_variable changed;
    size_t next = first, emitted = first;
    bool stop = false;
    std::exception_ptr failure;

    auto worker = [&](unsigned number) {
        try {
            StateReconstructor reconstructor(header, children, limits, statistics[number]);
            while (true) {
                size_t index;
                {
                    std::unique_lock<std::mutex> lock(mutex);
                    changed.wait_for(lock, std::chrono::milliseconds(100), [&] {
                        return stop || next == last || next - emitted < window;
                    });
                    if (stop || next == last) return;
                    if (next - emitted >= window) {
                        lock.unlock();
                        limits.check(statistics[number].polls, true);
                        continue;
                    }
                    index = next++;
                }
                auto& slot = slots[(index - first) % window];
                reconstructor.reconstruct(states[index], slot.choices);
                {
                    std::lock_guard<std::mutex> lock(mutex);
                    slot.ready = true;
                }
                changed.notify_all();
            }
        } catch (...) {
            {
                std::lock_guard<std::mutex> lock(mutex);
                if (!failure) failure = std::current_exception();
                stop = true;
            }
            limits.cancelled.store(true, std::memory_order_relaxed);
            changed.notify_all();
        }
    };

    auto stop_and_join = [&] {
        {
            std::lock_guard<std::mutex> lock(mutex);
            stop = true;
        }
        changed.notify_all();
        for (auto& thread : threads) if (thread.joinable()) thread.join();
    };

    try {
        for (unsigned number = 0; number < worker_count; ++number) threads.emplace_back(worker, number);
        while (emitted < last) {
            ResultSlot& slot = slots[(emitted - first) % window];
            {
                std::unique_lock<std::mutex> lock(mutex);
                changed.wait_for(lock, std::chrono::milliseconds(100), [&] { return failure || slot.ready; });
                if (failure) std::rethrow_exception(failure);
                if (!slot.ready) {
                    lock.unlock();
                    limits.check(total.polls, true);
                    continue;
                }
            }
            limits.check(total.polls);
            writer.node(states[emitted].key, states[emitted].level, header.order, slot.choices);
            {
                std::lock_guard<std::mutex> lock(mutex);
                slot.ready = false;
                ++emitted;
            }
            changed.notify_all();
        }
        stop_and_join();
    } catch (...) {
        auto error = std::current_exception();
        limits.cancelled.store(true, std::memory_order_relaxed);
        stop_and_join();
        if (failure) error = failure;
        std::rethrow_exception(error);
    }
    for (const auto& counters : statistics) {
        total.embeddings += counters.embeddings;
        total.canonical_calls += counters.canonical_calls;
    }
    slots.clear();
    slots.shrink_to_fit();
    limits.release(slot_bytes);
    return worker_count;
}

struct ReconstructionOptions {
    bool benchmark = false;
    std::string input;
    unsigned workers = 1;
    uint64_t seconds = 0, memory_mib = 0, output_mib = 0;
    int level = 0;
    uint64_t first = 0, count = 0;
};

ReconstructionOptions reconstruction_options(int argc, char** argv) {
    if (argc < 3) throw std::runtime_error("usage: compact_states stream|benchmark INPUT --seconds S --memory-mib M --max-output-mib B [--workers N] [--level K --first I --count C]");
    ReconstructionOptions options;
    options.benchmark = std::string(argv[1]) == "benchmark";
    if (!options.benchmark && std::string(argv[1]) != "stream") throw std::runtime_error("unknown reconstruction mode");
    options.input = argv[2];
    std::set<std::string> seen;
    for (int index = 3; index < argc; index += 2) {
        if (index + 1 >= argc) throw std::runtime_error("missing option value");
        const std::string name = argv[index];
        if (!seen.insert(name).second) throw std::runtime_error("duplicate option");
        const uint64_t value = unsigned_number(argv[index + 1]);
        if (name == "--workers") {
            if (!value || value > 32) throw std::runtime_error("workers must be1..32");
            options.workers = static_cast<unsigned>(value);
        } else if (name == "--seconds") options.seconds = value;
        else if (name == "--memory-mib") options.memory_mib = value;
        else if (name == "--max-output-mib") options.output_mib = value;
        else if (name == "--first" && options.benchmark) options.first = value;
        else if (name == "--count" && options.benchmark) options.count = value;
        else if (name == "--level" && options.benchmark) {
            if (value < 3 || value >= maximum_vertices) throw std::runtime_error("benchmark level must be3..12");
            options.level = static_cast<int>(value);
        } else throw std::runtime_error("unknown option");
    }
    if (!options.seconds || !options.memory_mib || !options.output_mib ||
        options.memory_mib > UINT64_MAX / (1024 * 1024) || options.output_mib > UINT64_MAX / (1024 * 1024))
        throw std::runtime_error("positive explicit seconds, memory and output limits required");
    if (options.benchmark && (!options.level || !options.count || !seen.count("--first")))
        throw std::runtime_error("benchmark level, first and positive count required");
    return options;
}

int main(int argc, char** argv) {
    std::signal(SIGINT, reconstruction_interrupt);
    std::signal(SIGTERM, reconstruction_interrupt);
    std::signal(SIGPIPE, SIG_IGN);
    const auto started = std::chrono::steady_clock::now();
    const auto cpu_started = std::clock();
    try {
        const auto options = reconstruction_options(argc, argv);
        ReconstructionLimits limits;
        limits.started = started;
        limits.seconds = static_cast<double>(options.seconds);
        limits.memory_bytes = options.memory_mib * 1024 * 1024;
        Input input(options.input);
        input.magic("TPCGST01");
        const auto header = read_header(input);
        nauty_check(WORDSIZE, 1, header.order, NAUTYVERSIONID);
        std::array<size_t, maximum_vertices + 1> counts{}, offsets{};
        const auto states = read_parallel_states(input, header, limits, counts);
        for (int level = 3; level <= maximum_vertices; ++level) offsets[level] = offsets[level - 1] + counts[level - 1];
        const double load_seconds = std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count();
        if (options.benchmark && (options.level >= header.order || options.first >= counts[options.level] ||
                                 options.count > counts[options.level] - options.first))
            throw std::runtime_error("benchmark interval outside level");
        ChildIndex children(limits);
        StreamProofWriter writer(limits, options.output_mib * 1024 * 1024);
        ReconstructionStatistics statistics;
        double index_seconds = 0, reconstruction_seconds = 0;
        unsigned worker_threads = 0;
        size_t emitted_states = 0;
        auto build_index = [&](int level) {
            const auto before = std::chrono::steady_clock::now();
            if (level < 3) children.clear();
            else children.build(states, offsets[level], offsets[level] + counts[level]);
            index_seconds += std::chrono::duration<double>(std::chrono::steady_clock::now() - before).count();
        };
        auto emit_level = [&](size_t first, size_t last) {
            const auto before = std::chrono::steady_clock::now();
            worker_threads = std::max(worker_threads, reconstruct_level(header, states, first, last, children,
                                                                         options.workers, writer, limits, statistics));
            writer.finish_frames();
            emitted_states += last - first;
            reconstruction_seconds += std::chrono::duration<double>(std::chrono::steady_clock::now() - before).count();
        };
        if (options.benchmark) {
            build_index(options.level - 1);
            const size_t first = offsets[options.level] + static_cast<size_t>(options.first);
            emit_level(first, first + static_cast<size_t>(options.count));
        } else {
            for (uint8_t byte : header.bytes) writer.integer(byte, 1);
            for (int level = 3; level < header.order; ++level) {
                build_index(level - 1);
                emit_level(offsets[level], offsets[level] + counts[level]);
            }
            build_index(header.order - 1);
            for (int top = header.first; top < header.last; ++top) {
                limits.check(statistics.polls, true);
                const auto& tree = header.catalog[header.order][top];
                Adjacency residual{};
                for (int vertex = 0; vertex < header.order; ++vertex)
                    residual[vertex] = ((1u << header.order) - 1) & ~(1u << vertex) & ~tree.adjacency[vertex];
                ++statistics.canonical_calls;
                auto canonical = canonicalize(residual, header.order);
                Answer answer{true, 0};
                if (header.order > 3 && !children.lookup(canonical.key, answer))
                    throw std::runtime_error("assigned root child missing");
                Placement root;
                root.tree_index = static_cast<uint16_t>(tree.index);
                root.child_id = answer.proof_id;
                root.child_labels = canonical.original_labels;
                for (int vertex = 0; vertex < header.order; ++vertex) root.images[vertex] = static_cast<uint8_t>(vertex);
                writer.root(root, header.order);
            }
            writer.finish(header.last - header.first);
        }
        limits.check(statistics.polls, true);
        struct rusage usage{};
        if (getrusage(RUSAGE_SELF, &usage)) throw std::runtime_error("resource accounting failed");
#ifdef __APPLE__
        const uint64_t peak_memory = static_cast<uint64_t>(usage.ru_maxrss);
#else
        const uint64_t peak_memory = static_cast<uint64_t>(usage.ru_maxrss) * 1024;
#endif
        std::cerr << std::setprecision(15) << "{\"status\":\"" << (options.benchmark ? "benchmarked" : "streamed")
                  << "\",\"n\":" << header.order << ",\"top_first\":" << header.first << ",\"top_last\":" << header.last
                  << ",\"states\":" << emitted_states << ",\"input_states\":" << states.size()
                  << ",\"input_bytes\":" << input.bytes << ",\"output_bytes\":" << writer.bytes
                  << ",\"embeddings\":" << statistics.embeddings << ",\"canonical_calls\":" << statistics.canonical_calls
                  << ",\"workers\":" << options.workers << ",\"worker_threads\":" << worker_threads
                  << ",\"load_seconds\":" << load_seconds << ",\"index_seconds\":" << index_seconds
                  << ",\"reconstruction_seconds\":" << reconstruction_seconds
                  << ",\"cpu_seconds\":" << double(std::clock() - cpu_started) / CLOCKS_PER_SEC
                  << ",\"wall_seconds\":" << std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count()
                  << ",\"peak_memory_bytes\":" << peak_memory;
        if (options.benchmark)
            std::cerr << ",\"format\":\"ordered-node-frames\",\"level\":" << options.level
                      << ",\"first\":" << options.first << ",\"count\":" << options.count
                      << ",\"first_state_id\":" << offsets[options.level] + options.first + 1
                      << ",\"complete_proof_stream\":false,\"mathematical_proof_checked\":false";
        std::cerr << "}\n";
        return 0;
    } catch (const SearchLimit& error) {
        std::cerr << "incomplete: " << error.what() << '\n';
        return 3;
    } catch (const std::bad_alloc&) {
        std::cerr << "incomplete: memory\n";
        return 3;
    } catch (const std::exception& error) {
        std::cerr << "failed: " << error.what() << '\n';
        return 1;
    }
}
