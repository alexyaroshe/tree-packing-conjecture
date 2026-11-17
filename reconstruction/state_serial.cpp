// compact winning states
// extract: proof header & nodes > sorted masks > exclusive state certificate
// expand: lower-level membership > embeddings & permutations > ordinary proof
// stream: bounded stdout > ordinary proof; stderr > statistics
// expanded proof > separate existing checker
#define main residual_solver_main
#include "graph_helpers.cpp"
#undef main
#include <cerrno>
#include <fcntl.h>
#include <poll.h>
#include <unistd.h>

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

void reserve_states(std::vector<State>& states, size_t capacity, Budget& budget) {
    if (capacity > UINT32_MAX - 1 || capacity > std::numeric_limits<size_t>::max() / sizeof(State))
        throw SearchLimit("state-count");
    const uint64_t old_bytes = states.capacity() * sizeof(State);
    budget.allocate(capacity * sizeof(State));
    states.reserve(capacity);
    budget.table_bytes -= old_bytes;
}

int read_placement(Input& input, int size, int order, const std::vector<State>& states) {
    int tree = static_cast<int>(input.integer(2));
    if (tree >= tree_counts[size]) throw std::runtime_error("tree index outside catalog");
    unsigned seen = 0;
    for (int vertex = 0; vertex < size; ++vertex) {
        unsigned image = static_cast<unsigned>(input.integer(1));
        if (image >= static_cast<unsigned>(order) || (seen & (1u << image)))
            throw std::runtime_error("invalid embedding image");
        seen |= 1u << image;
    }
    uint64_t child = input.integer(4);
    if (child > states.size() || (!child && size > 3) ||
        (child && states[child - 1].level != size - 1))
        throw std::runtime_error("invalid backward child reference");
    seen = 0;
    for (int vertex = 0; vertex < order; ++vertex) {
        unsigned label = static_cast<unsigned>(input.integer(1));
        if (label >= static_cast<unsigned>(order) || (seen & (1u << label)))
            throw std::runtime_error("invalid child permutation");
        seen |= 1u << label;
    }
    return tree;
}

std::vector<State> extract_states(Input& input, const Header& header, Budget& budget) {
    std::vector<State> states;
    std::set<int> roots;
    while (true) {
        budget.check(true);
        unsigned kind = static_cast<unsigned>(input.integer(1));
        if (kind == 3) {
            if (input.integer(2) != roots.size() || roots.size() != static_cast<size_t>(header.last - header.first))
                throw std::runtime_error("incomplete root coverage");
            input.end();
            break;
        }
        if (kind == 2) {
            int tree = read_placement(input, header.order, header.order, states);
            if (!roots.insert(tree).second) throw std::runtime_error("duplicate root");
            continue;
        }
        if (kind != 1) throw std::runtime_error("invalid proof record");
        State state;
        state.level = static_cast<uint8_t>(input.integer(1));
        state.key.lower = input.integer(8);
        state.key.upper = static_cast<uint16_t>(input.integer(2));
        if (state.level < 3 || state.level >= header.order) throw std::runtime_error("invalid state level");
        validate_graph(state.key, header.order, state.level);
        std::set<int> obligations;
        for (int index = 0; index < tree_counts[state.level]; ++index)
            if (!obligations.insert(read_placement(input, state.level, header.order, states)).second)
                throw std::runtime_error("duplicate tree obligation");
        if (states.size() == states.capacity()) reserve_states(states, states.empty() ? 1024 : states.capacity() * 2, budget);
        states.push_back(state);
    }
    for (int top = header.first; top < header.last; ++top)
        if (!roots.count(header.catalog[header.order][top].index)) throw std::runtime_error("assigned root missing");
    std::sort(states.begin(), states.end(), [&](const State& left, const State& right) {
        budget.check();
        return state_less(left, right);
    });
    states.erase(std::unique(states.begin(), states.end(), [&](const State& left, const State& right) {
        budget.check();
        return left.level == right.level && left.key == right.key;
    }), states.end());
    budget.check(true);
    return states;
}

unsigned mask_width(int order) { return static_cast<unsigned>((order * (order - 1) / 2 + 7) / 8); }

void write_integer(std::ostream& output, uint64_t value, unsigned width) {
    for (unsigned index = 0; index < width; ++index) output.put(static_cast<char>(value >> (8 * index)));
}

uint64_t write_states(const std::string& path, const Header& header, const std::vector<State>& states,
                      uint64_t limit, Budget& budget) {
    unsigned width = mask_width(header.order);
    uint64_t bytes = 16 + header.bytes.size() + states.size() * width;
    if (bytes > limit) throw SearchLimit("output-size");
    std::ofstream output(path, std::ios::binary);
    output.write("TPCGST01", 8);
    output.write(reinterpret_cast<const char*>(header.bytes.data()), header.bytes.size());
    write_integer(output, states.size(), 8);
    for (const auto& state : states) {
        budget.check();
        write_integer(output, state.key.lower, std::min(width, 8u));
        if (width > 8) write_integer(output, state.key.upper, width - 8);
    }
    output.flush();
    output.close();
    if (!output) throw std::runtime_error("compact output failed");
    return bytes;
}

std::vector<State> read_states(Input& input, const Header& header, Budget& budget) {
    std::vector<State> states;
    uint64_t count = input.integer(8);
    reserve_states(states, count, budget);
    unsigned width = mask_width(header.order);
    for (uint64_t index = 0; index < count; ++index) {
        budget.check();
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
    }
    input.end();
    return states;
}

class StreamProofWriter {
    Budget& budget;
    uint64_t maximum_bytes;
    uint32_t nodes = 0;
    int original_flags;
    std::array<uint8_t, 64 * 1024> buffer{};
    size_t used = 0;

    void flush() {
        size_t offset = 0;
        while (offset < used) {
            budget.check(true);
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
    StreamProofWriter(Budget& limits, uint64_t maximum) : budget(limits), maximum_bytes(maximum) {
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
    void finish(int roots) {
        integer(3, 1); integer(roots, 2);
        flush();
    }
};

template <typename Writer>
class Expander {
    const Header& header;
    Budget& budget;
    Writer& proof;
    std::array<MemoTable, maximum_vertices + 1> completed;

    bool embedding(const Tree& tree, const CanonicalGraph& host, int position, unsigned used,
                   std::array<uint8_t, maximum_vertices>& images, Placement& choice) {
        budget.check();
        if (position == tree.size) {
            ++embeddings;
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
            ++canonical_calls;
            auto canonical = canonicalize(residual, header.order);
            Answer answer;
            if (!completed[tree.size - 1].lookup(canonical.key, answer)) return false;
            choice.child_id = answer.proof_id;
            choice.child_labels = canonical.original_labels;
            return true;
        }
        int parent = tree.parent_positions[position];
        unsigned candidates = parent < 0 ? host.root_representatives : host.adjacency[images[parent]] & ~used;
        int sibling = tree.previous_siblings[position];
        if (sibling >= 0) candidates &= ~((1u << (images[sibling] + 1)) - 1);
        int children = tree.degrees[position] - (parent >= 0 ? 1 : 0);
        while (candidates) {
            int candidate = first_vertex(candidates);
            candidates &= candidates - 1;
            if (population(host.adjacency[candidate] & ~used) < children) continue;
            images[position] = static_cast<uint8_t>(candidate);
            if (embedding(tree, host, position + 1, used | (1u << candidate), images, choice)) return true;
        }
        return false;
    }
public:
    uint64_t embeddings = 0, canonical_calls = 0;
    Expander(const Header& record, Budget& limits, Writer& output) : header(record), budget(limits), proof(output) {}

    void expand(const std::vector<State>& states) {
        for (uint8_t byte : header.bytes) proof.integer(byte, 1);
        for (const auto& state : states) {
            budget.check(true);
            ++canonical_calls;
            auto host = canonicalize(decode_graph(state.key, header.order), header.order);
            if (!(host.key == state.key)) throw std::runtime_error("state canonical form differs from expansion backend");
            std::vector<Placement> choices;
            choices.reserve(header.catalog[state.level].size());
            for (const auto& tree : header.catalog[state.level]) {
                Placement choice;
                std::array<uint8_t, maximum_vertices> images{};
                if (!embedding(tree, host, 0, 0, images, choice)) throw std::runtime_error("state has no supplied winning continuation");
                choices.push_back(choice);
            }
            uint32_t id = proof.node(state.key, state.level, header.order, choices);
            completed[state.level].insert(state.key, {true, id}, budget);
        }
        for (int top = header.first; top < header.last; ++top) {
            budget.check(true);
            const auto& tree = header.catalog[header.order][top];
            Adjacency residual{};
            for (int vertex = 0; vertex < header.order; ++vertex)
                residual[vertex] = ((1u << header.order) - 1) & ~(1u << vertex) & ~tree.adjacency[vertex];
            ++canonical_calls;
            auto canonical = canonicalize(residual, header.order);
            Answer answer{true, 0};
            if (header.order > 3 && !completed[header.order - 1].lookup(canonical.key, answer))
                throw std::runtime_error("assigned root child missing");
            Placement root;
            root.tree_index = static_cast<uint16_t>(tree.index);
            root.child_id = answer.proof_id;
            root.child_labels = canonical.original_labels;
            for (int vertex = 0; vertex < header.order; ++vertex) root.images[vertex] = static_cast<uint8_t>(vertex);
            proof.root(root, header.order);
        }
        proof.finish(header.last - header.first);
    }
};

void publish(const std::filesystem::path& staged, const std::filesystem::path& output, uint64_t bytes) {
    if (std::filesystem::file_size(staged) != bytes) throw std::runtime_error("output size differs");
    int descriptor = open(staged.c_str(), O_RDONLY);
    if (descriptor < 0) throw std::runtime_error("cannot sync output");
    int result = fsync(descriptor);
    close(descriptor);
    if (result) throw std::runtime_error("output sync failed");
    auto parent = output.parent_path().empty() ? std::filesystem::path(".") : output.parent_path();
    descriptor = open(parent.c_str(), O_RDONLY);
    if (descriptor < 0) throw std::runtime_error("cannot sync output directory");
    if (link(staged.c_str(), output.c_str())) {
        close(descriptor);
        throw std::runtime_error("cannot publish exclusive output");
    }
    result = fsync(descriptor);
    if (result) {
        std::error_code error;
        if (std::filesystem::equivalent(staged, output, error)) std::filesystem::remove(output, error);
        fsync(descriptor);
    }
    close(descriptor);
    if (result) throw std::runtime_error("output directory sync failed");
    std::error_code error;
    std::filesystem::remove(staged, error);
    std::filesystem::remove(staged.parent_path(), error);
}

int main(int argc, char** argv) {
    std::signal(SIGINT, handle_signal);
    std::signal(SIGTERM, handle_signal);
    const auto started = std::chrono::steady_clock::now();
    try {
        if (argc < 3) throw std::runtime_error("usage: compact_states extract|expand INPUT OUTPUT [limits]; compact_states stream INPUT [limits]");
        std::string mode = argv[1];
        bool streaming = mode == "stream";
        if (mode != "extract" && mode != "expand" && !streaming) throw std::runtime_error("unknown mode");
        if (!streaming && argc < 4) throw std::runtime_error("output path required");
        if (streaming) std::signal(SIGPIPE, SIG_IGN);
        Budget budget;
        budget.seconds = 1800;
        budget.memory_bytes = uint64_t{4096} * 1024 * 1024;
        uint64_t maximum_bytes = uint64_t{1024} * 1024 * 1024;
        for (int index = streaming ? 3 : 4; index < argc; index += 2) {
            if (index + 1 >= argc) throw std::runtime_error("missing option value");
            std::string name = argv[index];
            uint64_t value = unsigned_number(argv[index + 1]);
            if (!value || value > UINT64_MAX / (1024 * 1024)) throw std::runtime_error("invalid limit");
            if (name == "--seconds") budget.seconds = static_cast<double>(value);
            else if (name == "--memory-mib") budget.memory_bytes = value * 1024 * 1024;
            else if (name == "--max-output-mib") maximum_bytes = value * 1024 * 1024;
            else throw std::runtime_error("unknown option");
        }
        std::filesystem::path output;
        if (!streaming) {
            output = argv[3];
            if (std::filesystem::exists(output) || std::filesystem::is_symlink(output)) throw std::runtime_error("output already exists");
        }
        Input input(argv[2]);
        if (mode != "extract") input.magic("TPCGST01");
        auto header = read_header(input);
        nauty_check(WORDSIZE, 1, header.order, NAUTYVERSIONID);
        auto states = mode == "extract" ? extract_states(input, header, budget) : read_states(input, header, budget);
        std::filesystem::path staged;
        if (!streaming) {
            auto staging = std::filesystem::path(output.string() + ".partial");
            if (!std::filesystem::create_directory(staging)) throw std::runtime_error("staging directory already exists");
            staged = staging / "data";
        }
        uint64_t bytes = 0, embeddings = 0, canonical_calls = 0;
        if (mode == "extract") bytes = write_states(staged.string(), header, states, maximum_bytes, budget);
        else if (streaming) {
            StreamProofWriter writer(budget, maximum_bytes);
            Expander<StreamProofWriter> expander(header, budget, writer);
            expander.expand(states);
            bytes = writer.bytes;
            embeddings = expander.embeddings;
            canonical_calls = expander.canonical_calls;
        }
        else {
            ProofWriter writer(staged.string(), maximum_bytes);
            Expander<ProofWriter> expander(header, budget, writer);
            expander.expand(states);
            bytes = writer.bytes;
            embeddings = expander.embeddings;
            canonical_calls = expander.canonical_calls;
        }
        budget.check(true);
        if (!streaming) publish(staged, output, bytes);
        struct rusage usage{};
        getrusage(RUSAGE_SELF, &usage);
#ifdef __APPLE__
        uint64_t peak_memory_bytes = static_cast<uint64_t>(usage.ru_maxrss);
#else
        uint64_t peak_memory_bytes = static_cast<uint64_t>(usage.ru_maxrss) * 1024;
#endif
        std::ostream& statistics = streaming ? std::cerr : std::cout;
        statistics << "{\"status\":\"" << (mode == "extract" ? "extracted" : streaming ? "streamed" : "expanded")
                  << "\",\"n\":" << header.order << ",\"top_first\":" << header.first << ",\"top_last\":" << header.last
                  << ",\"states\":" << states.size() << ",\"input_bytes\":" << input.bytes << ",\"output_bytes\":" << bytes
                  << ",\"embeddings\":" << embeddings << ",\"canonical_calls\":" << canonical_calls
                  << ",\"wall_seconds\":" << std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count()
                  << ",\"peak_memory_bytes\":" << peak_memory_bytes << "}\n";
        return 0;
    } catch (const SearchLimit& error) {
        std::cerr << "incomplete: " << error.what() << '\n';
        return 3;
    } catch (const std::exception& error) {
        std::cerr << "failed: " << error.what() << '\n';
        return 1;
    }
}
