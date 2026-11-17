// compressed proof checker
// catalog > exact tree shapes; nodes > placements > relabelled children
// roots > assigned top range; footer > complete proof
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

constexpr int largest_order = 13;
constexpr std::array<int, 14> expected_trees{0, 1, 1, 1, 2, 3, 6, 11, 23, 47, 106, 235, 551, 1301};
using SmallGraph = std::array<uint16_t, largest_order>;
struct CatalogTree { SmallGraph graph{}; std::array<uint8_t, largest_order> parents{}; int largest_degree = 0; };
struct VerifiedNode { uint64_t lower; uint16_t upper; uint8_t level; };
static_assert(sizeof(VerifiedNode) == 16, "compact verified nodes");

void require(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(message);
}

std::string branch_code(const SmallGraph& tree, int root, int parent) {
    std::vector<std::string> codes;
    for (int neighbor = 0; neighbor < largest_order; ++neighbor)
        if (neighbor != parent && (tree[root] & (1u << neighbor))) codes.push_back(branch_code(tree, neighbor, root));
    std::sort(codes.begin(), codes.end());
    std::string code = "[";
    for (const auto& child : codes) code += child;
    return code + "]";
}

SmallGraph unpack_graph(uint64_t lower, uint16_t upper, int order) {
    SmallGraph graph{};
    int bit = 0;
    for (int left = 0; left < order; ++left)
        for (int right = left + 1; right < order; ++right, ++bit) {
            bool present = bit < 64 ? ((lower >> bit) & 1u) : ((upper >> (bit - 64)) & 1u);
            if (present) { graph[left] |= 1u << right; graph[right] |= 1u << left; }
        }
    return graph;
}

class Checker {
    std::ifstream input;
    int order = 0, first_top = 0, last_top = 0;
    std::array<std::vector<CatalogTree>, largest_order + 1> catalog;
    std::vector<int> top_indices;
    std::vector<VerifiedNode> verified_nodes{{0, 0, 0}};
    std::set<int> verified_roots;
    std::chrono::steady_clock::time_point started = std::chrono::steady_clock::now();
    uint64_t maximum_bytes;
    double seconds;
    uint64_t bytes_read = 0, placements = 0;

    uint64_t integer(unsigned width) {
        require(bytes_read <= maximum_bytes - width, "proof exceeds byte limit");
        uint64_t value = 0;
        for (unsigned offset = 0; offset < width; ++offset) {
            int byte = input.get();
            require(byte != EOF, "truncated proof");
            value |= uint64_t{static_cast<unsigned char>(byte)} << (8 * offset);
        }
        bytes_read += width;
        return value;
    }

    void check_time() {
        require(std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count() < seconds, "checker deadline");
    }

    int edge_count(const SmallGraph& graph) const {
        int total = 0;
        for (int vertex = 0; vertex < order; ++vertex) total += __builtin_popcount(graph[vertex]);
        return total / 2;
    }

    void read_header() {
        std::string magic;
        for (int offset = 0; offset < 8; ++offset) magic += static_cast<char>(integer(1));
        require(magic == "TPCRDP01", "invalid proof format");
        order = static_cast<int>(integer(1));
        require(order >= 2 && order <= largest_order, "invalid graph order");
        first_top = static_cast<int>(integer(2)); last_top = static_cast<int>(integer(2));
        require(first_top < last_top && last_top <= expected_trees[order], "invalid top range");
        for (int size = 2; size <= order; ++size) {
            require(integer(2) == static_cast<unsigned>(expected_trees[size]), "wrong catalog count");
            std::set<std::string> shapes;
            for (int index = 0; index < expected_trees[size]; ++index) {
                CatalogTree tree;
                for (int vertex = 1; vertex < size; ++vertex) {
                    int parent = static_cast<int>(integer(1));
                    require(parent < vertex, "invalid catalog parent");
                    tree.parents[vertex] = static_cast<uint8_t>(parent);
                    tree.graph[vertex] |= 1u << parent; tree.graph[parent] |= 1u << vertex;
                }
                std::string smallest;
                for (int root = 0; root < size; ++root) {
                    auto code = branch_code(tree.graph, root, -1);
                    if (smallest.empty() || code < smallest) smallest = code;
                    tree.largest_degree = std::max(tree.largest_degree, __builtin_popcount(tree.graph[root]));
                }
                require(shapes.insert(smallest).second, "duplicate catalog shape");
                catalog[size].push_back(tree);
            }
        }
        std::vector<int> ordered(expected_trees[order]);
        for (int index = 0; index < expected_trees[order]; ++index) ordered[index] = index;
        std::stable_sort(ordered.begin(), ordered.end(), [&](int left, int right) {
            return catalog[order][left].largest_degree > catalog[order][right].largest_degree;
        });
        for (int position = first_top; position < last_top; ++position) {
            int index = static_cast<int>(integer(2));
            require(index == ordered[position], "top indices do not match assigned range");
            top_indices.push_back(index);
        }
    }

    int check_placement(const SmallGraph& host, int size) {
        check_time();
        int tree_index = static_cast<int>(integer(2));
        require(tree_index < expected_trees[size], "tree index outside catalog");
        std::array<int, largest_order> images{};
        unsigned used = 0;
        for (int vertex = 0; vertex < size; ++vertex) {
            int image = static_cast<int>(integer(1));
            require(image < order && !(used & (1u << image)), "invalid embedding image");
            images[vertex] = image; used |= 1u << image;
        }
        SmallGraph remainder = host;
        const auto& tree = catalog[size][tree_index];
        for (int vertex = 1; vertex < size; ++vertex) {
            int left = images[vertex], right = images[tree.parents[vertex]];
            require(remainder[left] & (1u << right), "tree edge missing from host");
            remainder[left] &= ~(1u << right); remainder[right] &= ~(1u << left);
        }
        auto child = integer(4);
        require(child < verified_nodes.size(), "forward or missing child");
        std::array<int, largest_order> labels{};
        used = 0;
        for (int vertex = 0; vertex < order; ++vertex) {
            int label = static_cast<int>(integer(1));
            require(label < order && !(used & (1u << label)), "invalid child permutation");
            labels[vertex] = label; used |= 1u << label;
        }
        int next_level = size - 1;
        require(edge_count(remainder) == next_level * (next_level - 1) / 2, "wrong residual edge count");
        if (!child) require(next_level <= 2, "unproved nonterminal child");
        else {
            require(verified_nodes[child].level == next_level, "wrong child level");
            auto expected = unpack_graph(verified_nodes[child].lower, verified_nodes[child].upper, order);
            for (int left = 0; left < order; ++left)
                for (int right = left + 1; right < order; ++right)
                    require(bool(remainder[labels[left]] & (1u << labels[right])) == bool(expected[left] & (1u << right)),
                            "child graph does not match residual");
        }
        ++placements;
        return tree_index;
    }

    void check_node() {
        int level = static_cast<int>(integer(1));
        require(level >= 3 && level < order, "invalid node level");
        auto lower = integer(8), high = integer(2);
        int pairs = order * (order - 1) / 2;
        require(!(pairs < 64 && (lower >> pairs)) && !(pairs <= 64 && high) && !(pairs > 64 && (high >> (pairs - 64))), "node edge outside host");
        auto host = unpack_graph(lower, static_cast<uint16_t>(high), order);
        require(edge_count(host) == level * (level - 1) / 2, "wrong node edge count");
        std::set<int> trees_seen;
        for (int index = 0; index < expected_trees[level]; ++index)
            require(trees_seen.insert(check_placement(host, level)).second, "duplicate tree obligation");
        require(verified_nodes.size() < UINT32_MAX, "too many proof nodes");
        verified_nodes.push_back({lower, static_cast<uint16_t>(high), static_cast<uint8_t>(level)});
    }

    void check_root() {
        SmallGraph complete{};
        for (int vertex = 0; vertex < order; ++vertex) complete[vertex] = ((1u << order) - 1) ^ (1u << vertex);
        int index = check_placement(complete, order);
        require(std::find(top_indices.begin(), top_indices.end(), index) != top_indices.end(), "root outside assigned range");
        require(verified_roots.insert(index).second, "duplicate root");
    }
public:
    Checker(const std::string& path, uint64_t byte_limit, double deadline) : maximum_bytes(byte_limit), seconds(deadline) {
        input.open(path, std::ios::binary);
        require(bool(input), "cannot open proof");
    }
    void run() {
        read_header();
        while (true) {
            check_time();
            int kind = static_cast<int>(integer(1));
            if (kind == 1) check_node();
            else if (kind == 2) check_root();
            else if (kind == 3) {
                auto roots = integer(2);
                require(roots == verified_roots.size() && roots == static_cast<unsigned>(last_top - first_top), "incomplete top coverage");
                require(input.get() == EOF, "trailing proof bytes");
                std::cout << "{\"status\":\"verified\",\"n\":" << order << ",\"top_first\":" << first_top << ",\"top_last\":" << last_top
                          << ",\"roots\":" << roots << ",\"nodes\":" << verified_nodes.size() - 1
                          << ",\"placements\":" << placements << ",\"proof_bytes\":" << bytes_read << "}\n";
                return;
            } else throw std::runtime_error("invalid record kind");
        }
    }
};

uint64_t positive_number(const std::string& text) {
    require(!text.empty() && text[0] >= '0' && text[0] <= '9', "invalid positive integer");
    size_t used;
    auto value = std::stoull(text, &used);
    require(used == text.size() && value > 0, "invalid positive integer");
    return value;
}

int main(int count, char** arguments) {
    try {
        require(count >= 2 && count % 2 == 0, "usage: check_proof proof [--max-mib N] [--seconds N]");
        uint64_t maximum_mib = 1024, seconds = 60;
        for (int index = 2; index < count; index += 2) {
            std::string name = arguments[index];
            auto value = positive_number(arguments[index + 1]);
            if (name == "--max-mib") maximum_mib = value;
            else if (name == "--seconds") seconds = value;
            else throw std::runtime_error("unknown checker option");
        }
        require(maximum_mib <= std::numeric_limits<uint64_t>::max() / (1024 * 1024), "byte limit overflow");
        Checker checker(arguments[1], maximum_mib * 1024 * 1024, static_cast<double>(seconds));
        checker.run();
        return 0;
    } catch (const std::exception& error) {
        std::cerr << "REJECTED: " << error.what() << '\n';
        return 1;
    }
}
