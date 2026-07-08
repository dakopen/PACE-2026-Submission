// Improved PACE 2026 solver. Adds a Global Column Pool and a Multi-Start 
// Greedy Set Packing Endgame to close the integrality gap left by Price-and-Branch.

#include <highs/Highs.h>
#include <algorithm>
#include <atomic>
#include <cctype>
#include <cerrno>
#include <chrono>
#include <cmath>
#include <csignal>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <iostream>
#include <limits>
#include <memory>
#include <new>
#include <numeric>
#include <random>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#if defined(__unix__) || defined(__APPLE__)
#include <unistd.h>
#include <sys/resource.h>
#endif

using Clock = std::chrono::steady_clock;
using TimePoint = Clock::time_point;
struct TreeQueries;
static TreeQueries* g_output_query = nullptr;
static std::ostream& log_out() { std::cerr << "# "; return std::cerr; }

// ---------------------------------------------------------------------
// Parameters
// ---------------------------------------------------------------------
struct Params {
    double time_limit = 300.0;
    bool disable_kernel = false;
    bool quiet = false;
};

// ---------------------------------------------------------------------
// Component
// ---------------------------------------------------------------------
struct Component {
    std::vector<int> leaves;
    Component() = default;
    explicit Component(std::vector<int> xs) : leaves(std::move(xs)) { normalize(); }
    void normalize() {
        std::sort(leaves.begin(), leaves.end());
        leaves.erase(std::unique(leaves.begin(), leaves.end()), leaves.end());
    }
    int size() const { return static_cast<int>(leaves.size()); }
    bool empty() const { return leaves.empty(); }
    int min_leaf() const { return leaves.empty() ? 0 : leaves.front(); }
    bool operator==(const Component& o) const { return leaves == o.leaves; }
};

struct ComponentHash {
    std::size_t operator()(const Component& c) const noexcept {
        std::uint64_t h = 1469598103934665603ULL;
        for (int x : c.leaves) {
            h ^= static_cast<std::uint64_t>(x) + 0x9e3779b97f4a7c15ULL;
            h *= 1099511628211ULL;
        }
        h ^= c.leaves.size() + 0x9e3779b97f4a7c15ULL;
        return static_cast<std::size_t>(h);
    }
};

static Component component_union(const Component& a, const Component& b) {
    Component out;
    out.leaves.reserve(a.leaves.size() + b.leaves.size());
    std::set_union(a.leaves.begin(), a.leaves.end(), b.leaves.begin(), b.leaves.end(),
                   std::back_inserter(out.leaves));
    return out;
}

static std::vector<Component> singleton_forest(int n) {
    std::vector<Component> f;
    f.reserve(n);
    for (int l = 1; l <= n; ++l) f.emplace_back(std::vector<int>{l});
    return f;
}
// Common chains detected by the reduction, as ready-made components (reduced labels).
// The solver seeds from these (kept whole) instead of collapsing them.
static std::vector<Component> g_seed_chains;
static std::vector<Component> seed_forest_impl(int n, const std::vector<Component>& chains) {
    std::vector<char> used(n + 1, 0);
    std::vector<Component> f;
    for (const Component& c : chains) {
        bool ok = c.size() >= 2;
        if (ok) for (int l : c.leaves) if (l < 1 || l > n || used[l]) { ok = false; break; }
        if (!ok) continue;
        for (int l : c.leaves) used[l] = 1;
        f.push_back(c);
    }
    for (int l = 1; l <= n; ++l) if (!used[l]) f.emplace_back(std::vector<int>{l});
    return f;
}

static std::string format_forest(const std::vector<Component>& forest);

// ---------------------------------------------------------------------
// Anytime state + async-signal-safe publication
// ---------------------------------------------------------------------
static std::vector<Component> g_best_forest;
static std::string g_best_output;
static int g_lower_bound = 1;
static std::vector<std::vector<int>> g_leaf_expansion;
static std::vector<Component> g_forced_components;
static bool g_suppress_publish = false;
static std::string g_pub_buf[2];
static std::atomic<int> g_pub_idx{-1};
static std::atomic<bool> g_termination_started{false};
static std::atomic<bool> g_normal_output_started{false};

static_assert(std::atomic<int>::is_always_lock_free, "lock-free index required");
static_assert(std::atomic<bool>::is_always_lock_free, "lock-free flag required");

#if defined(__unix__) || defined(__APPLE__)
static void write_all_fd(int fd, const char* data, std::size_t size) {
    while (size > 0) {
        ssize_t w = write(fd, data, size);
        if (w > 0) { data += w; size -= static_cast<std::size_t>(w); }
        else if (w < 0 && errno == EINTR) continue;
        else break;
    }
}
#endif

static void publish_output(const std::string& s) {
    if (g_termination_started.load(std::memory_order_acquire)) return;
    int cur = g_pub_idx.load(std::memory_order_acquire);
    int nxt = (cur == 0) ? 1 : 0;
    g_pub_buf[nxt] = s;
    if (g_termination_started.load(std::memory_order_acquire)) return;
    g_pub_idx.store(nxt, std::memory_order_release);
}

static std::vector<Component> lift_forest(const std::vector<Component>& forest) {
    if (g_leaf_expansion.empty() && g_forced_components.empty()) return forest;
    std::vector<Component> out;
    out.reserve(forest.size() + g_forced_components.size());
    for (const Component& c : forest) {
        std::vector<int> leaves;
        for (int r : c.leaves) {
            if (!g_leaf_expansion.empty() && r >= 1 && r < static_cast<int>(g_leaf_expansion.size()))
                for (int o : g_leaf_expansion[r]) leaves.push_back(o);
            else
                leaves.push_back(r);
        }
        out.emplace_back(std::move(leaves));
    }
    for (const Component& fc : g_forced_components) out.push_back(fc);
    return out;
}

static void set_best_forest(const std::vector<Component>& forest) {
    if (!g_best_forest.empty() && forest.size() >= g_best_forest.size()) return;
    g_best_forest = forest;
    if (g_suppress_publish) return;
    g_best_output = format_forest(lift_forest(g_best_forest));
    publish_output(g_best_output);
}

static void sigterm_handler(int) {
    static constexpr char msg[] = "# Termination signal: printing best known forest.\n";
#if defined(__unix__) || defined(__APPLE__)
    if (g_normal_output_started.load(std::memory_order_acquire)) return;
    if (g_termination_started.exchange(true, std::memory_order_acq_rel)) return;
    write_all_fd(STDERR_FILENO, msg, sizeof(msg) - 1);
    int idx = g_pub_idx.load(std::memory_order_acquire);
    if (idx >= 0) { const std::string& o = g_pub_buf[idx]; write_all_fd(STDOUT_FILENO, o.data(), o.size()); }
    _Exit(0);
#else
    std::cerr << msg;
    int idx = g_pub_idx.load(std::memory_order_acquire);
    if (idx >= 0) std::cout << g_pub_buf[idx];
    std::cout.flush();
    std::exit(0);
#endif
}

static void install_termination_handlers() {
#if defined(__unix__) || defined(__APPLE__)
    struct sigaction action {};
    action.sa_handler = sigterm_handler;
    sigemptyset(&action.sa_mask);
    sigaddset(&action.sa_mask, SIGTERM);
    sigaddset(&action.sa_mask, SIGINT);
    action.sa_flags = 0;
    if (sigaction(SIGTERM, &action, nullptr) != 0 || sigaction(SIGINT, &action, nullptr) != 0)
        throw std::runtime_error("Failed to install termination handlers.");
#else
    std::signal(SIGTERM, sigterm_handler);
    std::signal(SIGINT, sigterm_handler);
#endif
}

[[noreturn]] static void emit_final_output_and_exit(const std::string& output, int status) {
#if defined(__unix__) || defined(__APPLE__)
    g_normal_output_started.store(true, std::memory_order_release);
    sigset_t blocked;
    sigemptyset(&blocked);
    sigaddset(&blocked, SIGTERM);
    sigaddset(&blocked, SIGINT);
    (void)sigprocmask(SIG_BLOCK, &blocked, nullptr);
    write_all_fd(STDOUT_FILENO, output.data(), output.size());
    _Exit(status);
#else
    std::cout << output;
    std::cout.flush();
    std::exit(status);
#endif
}

// ---------------------------------------------------------------------
// Time budget
// ---------------------------------------------------------------------
struct TimeBudgetExceeded : public std::runtime_error {
    TimeBudgetExceeded() : std::runtime_error("time budget exceeded") {}
};

static double seconds_left(TimePoint deadline) {
    return std::max(0.0, std::chrono::duration<double>(deadline - Clock::now()).count());
}

static void check_time(TimePoint deadline) {
    if (Clock::now() >= deadline) throw TimeBudgetExceeded();
}

static std::size_t saturating_mul(std::size_t a, std::size_t b) {
    if (a != 0 && b > std::numeric_limits<std::size_t>::max() / a)
        return std::numeric_limits<std::size_t>::max();
    return a * b;
}

static int capped_int(std::size_t x) {
    return x > static_cast<std::size_t>(std::numeric_limits<int>::max())
               ? std::numeric_limits<int>::max()
               : static_cast<int>(x);
}

static std::size_t ceil_log2_size(std::size_t x) {
    if (x <= 1) return 1;
    --x;
    std::size_t r = 0;
    while (x) { ++r; x >>= 1; }
    return std::max<std::size_t>(1, r);
}

static std::uint64_t host_memory_bytes() {
#if defined(_SC_PHYS_PAGES) && defined(_SC_PAGE_SIZE)
    long pages = sysconf(_SC_PHYS_PAGES);
    long page_size = sysconf(_SC_PAGE_SIZE);
    if (pages > 0 && page_size > 0)
        return static_cast<std::uint64_t>(pages) * static_cast<std::uint64_t>(page_size);
#endif
    return 0;
}

static std::size_t memory_budget_bytes() {
    std::uint64_t host = host_memory_bytes();
    std::size_t budget = host > 0 ? static_cast<std::size_t>(host / 2)
                                  : std::numeric_limits<std::size_t>::max();
    // Respect an OS-imposed address-space / data limit (ulimit -v/-d, cgroup),
    // which can be far below physical RAM on shared judges. sysconf reports the
    // machine's physical memory, so without this the budget can overshoot the real
    // cap and the process gets OOM-killed. Use ~85% of the smaller limit.
#if defined(__unix__) || defined(__APPLE__)
    for (int res : {RLIMIT_AS, RLIMIT_DATA}) {
        struct rlimit rl;
        if (getrlimit(res, &rl) == 0 && rl.rlim_cur != RLIM_INFINITY && rl.rlim_cur > 0) {
            std::size_t lim = static_cast<std::size_t>(rl.rlim_cur / 10 * 8);
            if (lim < budget) budget = lim;
        }
    }
#endif
    return budget;
}

static std::size_t current_rss_bytes() {
#if defined(__unix__) || defined(__APPLE__)
    struct rusage ru;
    if (getrusage(RUSAGE_SELF, &ru) == 0) {
#if defined(__APPLE__)
        return static_cast<std::size_t>(ru.ru_maxrss);          // bytes on macOS
#else
        return static_cast<std::size_t>(ru.ru_maxrss) * 1024;   // kilobytes on Linux
#endif
    }
#endif
    return 0;
}

// Column cap for an exact ILP master with `num_rows` rows. A HiGHS MIP's peak
// memory grows roughly with rows * columns (presolved copies, B&B LP
// factorizations), and this cost is otherwise unbudgeted -- on large instances
// (num_rows ~= 3n) an unbounded master can allocate many GB and get OOM-killed,
// producing NO output (score 0). Cap columns to fit the memory still available
// (budget minus what the solver already holds), so the cap only bites when memory
// is actually tight: mid-size instances (small footprint) run uncapped, while
// large instances / low-RAM machines are held back. INT_MAX when budget unknown.
static int ilp_master_column_cap(int num_rows) {
    const std::size_t budget = memory_budget_bytes();
    if (budget == std::numeric_limits<std::size_t>::max()) return std::numeric_limits<int>::max();
    const std::size_t rows = std::max<std::size_t>(1, static_cast<std::size_t>(num_rows));
    const std::size_t used = current_rss_bytes();
    const std::size_t headroom = budget > used ? budget - used : 0;
    // ~48 bytes per (row * column) measured for the HiGHS MIP; spend at most 70%
    // of the remaining headroom on it.
    const std::size_t cap = (headroom / 10 * 7) / (48 * rows);
    return capped_int(std::max<std::size_t>(500, cap));
}

static std::size_t wmast_cell_budget() {
    constexpr std::size_t hard_cap = 400'000'000;
    const std::size_t bytes = memory_budget_bytes();
    if (bytes == std::numeric_limits<std::size_t>::max()) return hard_cap;
    return std::max<std::size_t>(1'000'000, std::min(hard_cap, bytes / 96));
}

static int wmast_leaf_budget() {
    long double cells = static_cast<long double>(wmast_cell_budget());
    long double leaves = std::sqrt(cells) / 2.0L;
    long double cap = static_cast<long double>(std::numeric_limits<int>::max());
    return leaves >= cap ? std::numeric_limits<int>::max() : std::max(1, static_cast<int>(leaves));
}

static std::size_t adaptive_column_budget(int n, int num_rows) {
    const std::size_t nn = static_cast<std::size_t>(std::max(1, n));
    const std::size_t rows = static_cast<std::size_t>(std::max(1, num_rows));
    const std::size_t structural = saturating_mul(nn, ceil_log2_size(nn + 1));
    std::size_t target = std::max(rows, structural);
    const std::size_t bytes = memory_budget_bytes();
    if (bytes != std::numeric_limits<std::size_t>::max()) {
        const std::size_t avg_span = ceil_log2_size(nn + 1);
        const std::size_t per_col =
            sizeof(Component) + avg_span * (sizeof(int) + sizeof(HighsInt) + sizeof(double));
        target = std::min(target, std::max<std::size_t>(1, bytes / std::max<std::size_t>(1, per_col)));
    }
    return std::max<std::size_t>(1, target);
}

// ---------------------------------------------------------------------
// Input parsing
// ---------------------------------------------------------------------
static std::vector<std::string> read_nonempty_lines_from_stream(std::istream& in) {
    std::vector<std::string> lines;
    std::string line;
    while (std::getline(in, line)) {
        while (!line.empty() && (line.back() == '\r' || line.back() == ' ' || line.back() == '\t'))
            line.pop_back();
        std::size_t s = 0;
        while (s < line.size() && (line[s] == ' ' || line[s] == '\t')) ++s;
        if (s) line.erase(0, s);
        if (!line.empty()) lines.push_back(line);
    }
    return lines;
}

static std::vector<std::string> read_nonempty_lines(const std::string& path) {
    if (path.empty() || path == "-") return read_nonempty_lines_from_stream(std::cin);
    std::ifstream in(path);
    if (!in) throw std::runtime_error("Cannot open input file: " + path);
    return read_nonempty_lines_from_stream(in);
}

// ---------------------------------------------------------------------
// Tree metadata
// ---------------------------------------------------------------------
struct TreeInfo {
    struct Node {
        int parent = -1, left = -1, right = -1, label = 0, depth = 0, tin = 0, tout = 0, subtree_size = 0;
        bool is_leaf = false;
    };
    int n = 0;
    int root = -1;
    std::vector<Node> nodes;
    std::vector<int> leaf_node;
    std::vector<int> edge_nodes;
    std::vector<int> edge_row;
    std::vector<std::vector<int>> up;

    int add_leaf(int label, int parent) {
        int id = static_cast<int>(nodes.size());
        nodes.push_back(Node{}); nodes[id].parent = parent; nodes[id].label = label; nodes[id].is_leaf = true;
        return id;
    }
    int add_internal(int parent) {
        int id = static_cast<int>(nodes.size());
        nodes.push_back(Node{}); nodes[id].parent = parent;
        return id;
    }
    bool is_ancestor(int anc, int v) const {
        return nodes[anc].tin <= nodes[v].tin && nodes[v].tout <= nodes[anc].tout;
    }

    void finalize(int leaf_count) {
        n = leaf_count;
        leaf_node.assign(n + 1, -1);
        for (int id = 0; id < static_cast<int>(nodes.size()); ++id) {
            if (!nodes[id].is_leaf) continue;
            int lab = nodes[id].label;
            if (lab < 1 || lab > n) throw std::runtime_error("Leaf label outside 1..n.");
            if (leaf_node[lab] != -1) throw std::runtime_error("Duplicate leaf label.");
            leaf_node[lab] = id;
        }
        for (int lab = 1; lab <= n; ++lab)
            if (leaf_node[lab] == -1) throw std::runtime_error("Missing leaf label.");

        int timer = 0;
        std::vector<std::pair<int, int>> st;
        st.push_back({root, 0});
        nodes[root].depth = 0;
        while (!st.empty()) {
            auto [u, state] = st.back();
            st.pop_back();
            if (state == 0) {
                nodes[u].tin = timer++;
                st.push_back({u, 1});
                if (!nodes[u].is_leaf) {
                    int r = nodes[u].right, l = nodes[u].left;
                    nodes[r].depth = nodes[l].depth = nodes[u].depth + 1;
                    st.push_back({r, 0});
                    st.push_back({l, 0});
                }
            } else {
                nodes[u].tout = timer - 1;
            }
        }

        edge_nodes.clear();
        edge_row.assign(nodes.size(), -1);
        for (int id = 0; id < static_cast<int>(nodes.size()); ++id) {
            if (id == root || nodes[id].is_leaf) continue;
            edge_row[id] = static_cast<int>(edge_nodes.size());
            edge_nodes.push_back(id);
        }

        int log = 1;
        while ((1 << log) <= static_cast<int>(nodes.size())) ++log;
        up.assign(log, std::vector<int>(nodes.size(), -1));
        for (int id = 0; id < static_cast<int>(nodes.size()); ++id) up[0][id] = nodes[id].parent;
        for (int j = 1; j < log; ++j)
            for (int id = 0; id < static_cast<int>(nodes.size()); ++id) {
                int p = up[j - 1][id];
                up[j][id] = (p < 0) ? -1 : up[j - 1][p];
            }

        std::vector<int> order;
        order.reserve(nodes.size());
        std::vector<int> ps = {root};
        while (!ps.empty()) {
            int u = ps.back(); ps.pop_back();
            order.push_back(u);
            if (!nodes[u].is_leaf) { ps.push_back(nodes[u].left); ps.push_back(nodes[u].right); }
        }
        for (int i = (int)order.size() - 1; i >= 0; --i) {
            int u = order[i];
            nodes[u].subtree_size = nodes[u].is_leaf ? 1 : nodes[nodes[u].left].subtree_size + nodes[nodes[u].right].subtree_size;
        }
    }

    int lca_node(int a, int b) const {
        if (a == b) return a;
        if (nodes[a].depth < nodes[b].depth) std::swap(a, b);
        int diff = nodes[a].depth - nodes[b].depth;
        for (int j = 0; diff; ++j) { if (diff & 1) a = up[j][a]; diff >>= 1; }
        if (a == b) return a;
        for (int j = static_cast<int>(up.size()) - 1; j >= 0; --j)
            if (up[j][a] != up[j][b]) { a = up[j][a]; b = up[j][b]; }
        return nodes[a].parent;
    }
    int lca_component(const Component& c) const {
        if (c.empty()) throw std::runtime_error("LCA of empty component.");
        int cur = leaf_node[c.leaves[0]];
        for (std::size_t i = 1; i < c.leaves.size(); ++i) cur = lca_node(cur, leaf_node[c.leaves[i]]);
        return cur;
    }
};

struct NewickParser {
    const std::string& s;
    int i = 0;
    TreeInfo tree;
    explicit NewickParser(const std::string& input) : s(input) {}
    void skip() { while (i < (int)s.size() && std::isspace((unsigned char)s[i])) ++i; }
    int parse_subtree(int parent) {
        skip();
        if (i >= (int)s.size()) throw std::runtime_error("Unexpected end of Newick string.");
        if (s[i] == '(') {
            int id = tree.add_internal(parent);
            ++i;
            int left = parse_subtree(id);
            skip();
            if (i >= (int)s.size() || s[i] != ',') throw std::runtime_error("Expected ',' in Newick.");
            ++i;
            int right = parse_subtree(id);
            skip();
            if (i >= (int)s.size() || s[i] != ')') throw std::runtime_error("Expected ')' in Newick.");
            ++i;
            tree.nodes[id].left = left;
            tree.nodes[id].right = right;
            return id;
        }
        if (!std::isdigit((unsigned char)s[i])) throw std::runtime_error("Expected integer leaf label.");
        int label = 0;
        while (i < (int)s.size() && std::isdigit((unsigned char)s[i])) { label = 10 * label + (s[i] - '0'); ++i; }
        return tree.add_leaf(label, parent);
    }

    TreeInfo parse(int n) {
        std::string cleaned = s;
        while (!cleaned.empty() && (cleaned.back() == ';' || std::isspace((unsigned char)cleaned.back())))
            cleaned.pop_back();
        NewickParser p(cleaned);
        int root_id = p.parse_subtree(-1);
        p.skip();
        if (p.i != (int)cleaned.size()) throw std::runtime_error("Trailing content in Newick string.");
        p.tree.root = root_id;
        p.tree.finalize(n);
        return std::move(p.tree);
    }
};

struct Instance {
    int n = 0;
    std::vector<TreeInfo> trees;
    TreeInfo t1, t2;
};

static Instance read_instance(const std::string& path) {
    std::vector<std::string> lines = read_nonempty_lines(path);
    std::string p_line;
    std::vector<std::string> newicks;
    for (const std::string& line : lines) {
        if (line.rfind("#p ", 0) == 0) p_line = line;
        else if (!line.empty() && line[0] != '#') newicks.push_back(line);
    }
    if (p_line.empty()) throw std::runtime_error("No #p line found.");
    std::istringstream ps(p_line);
    std::string tag;
    int tree_count = 0, n = 0;
    ps >> tag >> tree_count >> n;
    if (!ps || tag != "#p" || tree_count < 2 || n <= 0) throw std::runtime_error("Invalid #p line.");
    if ((int)newicks.size() < tree_count) throw std::runtime_error("Expected the number of Newick tree lines declared by #p.");

    Instance inst;
    inst.n = n;
    inst.trees.reserve(tree_count);
    for (int i = 0; i < tree_count; ++i) inst.trees.push_back(NewickParser(newicks[i]).parse(n));
    inst.t1 = inst.trees[0];
    inst.t2 = inst.trees[1];
    return inst;
}

// ---------------------------------------------------------------------
// Tree queries
// ---------------------------------------------------------------------
struct TreeQueries {
    const TreeInfo& info;
    std::unordered_map<Component, std::string, ComponentHash> restriction_cache;
    std::unordered_map<Component, std::vector<int>, ComponentHash> used_edge_cache;
    mutable std::vector<int> mark;
    mutable int epoch = 1;
    explicit TreeQueries(const TreeInfo& t) : info(t), mark(t.nodes.size(), 0) {}
    void clear_caches() { restriction_cache.clear(); used_edge_cache.clear(); }

    std::string restriction_key_rec(int node, const std::vector<int>& leaves) const {
        if (leaves.size() <= 1) return leaves.empty() ? "" : std::to_string(leaves[0]);
        if (info.nodes[node].is_leaf) return std::to_string(info.nodes[node].label);
        int left = info.nodes[node].left, right = info.nodes[node].right;
        std::vector<int> lpart, rpart;
        lpart.reserve(leaves.size());
        rpart.reserve(leaves.size());
        for (int leaf : leaves)
            (info.is_ancestor(left, info.leaf_node[leaf]) ? lpart : rpart).push_back(leaf);
        if (lpart.empty()) return restriction_key_rec(right, rpart);
        if (rpart.empty()) return restriction_key_rec(left, lpart);
        std::string a = restriction_key_rec(left, lpart);
        std::string b = restriction_key_rec(right, rpart);
        if (b < a) std::swap(a, b);
        return "(" + a + "," + b + ")";
    }

    const std::string& restriction_key(const Component& c) {
        auto it = restriction_cache.find(c);
        if (it != restriction_cache.end()) return it->second;
        std::string key = c.empty() ? std::string() : restriction_key_rec(info.lca_component(c), c.leaves);
        return restriction_cache.emplace(c, std::move(key)).first->second;
    }

    const std::vector<int>& used_edge_nodes(const Component& c) {
        auto cached = used_edge_cache.find(c);
        if (cached != used_edge_cache.end()) return cached->second;
        if (c.size() <= 1) return used_edge_cache.emplace(c, std::vector<int>{}).first->second;

        if (++epoch == std::numeric_limits<int>::max()) { std::fill(mark.begin(), mark.end(), 0); epoch = 1; }
        int root = info.lca_component(c);
        std::vector<int> used;
        auto add_edge = [&](int child) {
            if (child < 0 || child == info.root || info.edge_row[child] < 0) return;
            if (mark[child] == epoch) return;
            mark[child] = epoch;
            used.push_back(child);
        };
        add_edge(root);
        for (int leaf : c.leaves) {
            int cur = info.leaf_node[leaf];
            while (cur != root) { add_edge(cur); cur = info.nodes[cur].parent; if (cur < 0) break; }
        }
        std::sort(used.begin(), used.end());
        return used_edge_cache.emplace(c, std::move(used)).first->second;
    }
};

// ---------------------------------------------------------------------
// Forest formatting + validity
// ---------------------------------------------------------------------
static std::string fallback_component_newick(const Component& c, int l, int r) {
    if (r - l == 1) return std::to_string(c.leaves[l]);
    int m = l + (r - l) / 2;
    return "(" + fallback_component_newick(c, l, m) + "," + fallback_component_newick(c, m, r) + ")";
}
static std::string component_to_newick(const Component& c) {
    if (c.empty()) return "";
    if (g_output_query) return g_output_query->restriction_key(c);
    return fallback_component_newick(c, 0, c.size());
}
static std::string format_forest(const std::vector<Component>& forest) {
    std::vector<Component> comps = forest;
    std::sort(comps.begin(), comps.end(), [](const Component& a, const Component& b) {
        if (a.size() != b.size()) return a.size() < b.size();
        return a.leaves < b.leaves;
    });
    std::ostringstream out;
    out << "# tree size " << comps.size() << "\n";
    for (const Component& c : comps) out << component_to_newick(c) << ";\n";
    return out.str();
}
static bool is_valid_component(TreeQueries& q1, TreeQueries& q2, const Component& c) {
    if (c.empty()) return false;
    bool valid = (q1.restriction_key(c) == q2.restriction_key(c));
    if (!valid) { q1.restriction_cache.erase(c); q2.restriction_cache.erase(c); }
    return valid;
}
static bool forest_is_valid(int n, TreeQueries& q1, TreeQueries& q2, const std::vector<Component>& forest) {
    std::vector<int> leaf_count(n + 1, 0);
    std::vector<char> used1(q1.info.edge_nodes.size(), 0), used2(q2.info.edge_nodes.size(), 0);
    for (const Component& c : forest) {
        if (!is_valid_component(q1, q2, c)) return false;
        for (int leaf : c.leaves) {
            if (leaf < 1 || leaf > n) return false;
            ++leaf_count[leaf];
        }
        for (int u : q1.used_edge_nodes(c)) { int r = q1.info.edge_row[u]; if (r < 0) continue; if (used1[r]) return false; used1[r] = 1; }
        for (int u : q2.used_edge_nodes(c)) { int r = q2.info.edge_row[u]; if (r < 0) continue; if (used2[r]) return false; used2[r] = 1; }
    }
    for (int leaf = 1; leaf <= n; ++leaf) if (leaf_count[leaf] != 1) return false;
    return true;
}

static bool is_valid_component_all(const std::vector<TreeQueries*>& qs, const Component& c) {
    if (c.empty() || qs.empty()) return false;
    const std::string& key = qs[0]->restriction_key(c);
    for (std::size_t i = 1; i < qs.size(); ++i)
        if (qs[i]->restriction_key(c) != key) return false;
    return true;
}

static bool forest_is_valid_all(int n, const std::vector<TreeQueries*>& qs, const std::vector<Component>& forest) {
    if (qs.empty()) return false;
    std::vector<int> leaf_count(n + 1, 0);
    std::vector<std::vector<char>> used(qs.size());
    for (std::size_t t = 0; t < qs.size(); ++t) used[t].assign(qs[t]->info.edge_nodes.size(), 0);
    for (const Component& c : forest) {
        if (!is_valid_component_all(qs, c)) return false;
        for (int leaf : c.leaves) {
            if (leaf < 1 || leaf > n) return false;
            ++leaf_count[leaf];
        }
        for (std::size_t t = 0; t < qs.size(); ++t) {
            for (int u : qs[t]->used_edge_nodes(c)) {
                int r = qs[t]->info.edge_row[u];
                if (r < 0) continue;
                if (used[t][r]) return false;
                used[t][r] = 1;
            }
        }
    }
    for (int leaf = 1; leaf <= n; ++leaf) if (leaf_count[leaf] != 1) return false;
    return true;
}

static std::vector<Component> greedy_merge_improvement_all(
    int n, const std::vector<TreeQueries*>& qs, const std::vector<Component>& input, TimePoint deadline
) {
    if (!forest_is_valid_all(n, qs, input)) return input;
    std::vector<Component> forest = input;
    while (seconds_left(deadline) > 0.05) {
        const int full = (int)forest.size();
        std::vector<std::vector<int>> owners(qs.size());
        for (std::size_t t = 0; t < qs.size(); ++t) owners[t].assign(qs[t]->info.edge_nodes.size(), -1);
        for (int i = 0; i < full; ++i) {
            for (std::size_t t = 0; t < qs.size(); ++t) {
                for (int u : qs[t]->used_edge_nodes(forest[i])) {
                    int r = qs[t]->info.edge_row[u];
                    if (r >= 0) owners[t][r] = i;
                }
            }
        }

        std::vector<int> order(full);
        std::iota(order.begin(), order.end(), 0);
        std::sort(order.begin(), order.end(), [&](int a, int b) {
            if (forest[a].min_leaf() != forest[b].min_leaf()) return forest[a].min_leaf() < forest[b].min_leaf();
            return forest[a].leaves < forest[b].leaves;
        });

        std::vector<std::vector<char>> reserved(qs.size());
        for (std::size_t t = 0; t < qs.size(); ++t) reserved[t].assign(qs[t]->info.edge_nodes.size(), 0);
        std::vector<char> matched(full, 0);
        std::vector<Component> merges;
        const int window = full <= 512 ? full : std::min(full, std::max(8, capped_int(std::ceil(std::sqrt((double)full)))));
        bool any = false;

        auto fits = [&](const Component& merged, int i, int j) {
            for (std::size_t t = 0; t < qs.size(); ++t) {
                for (int u : qs[t]->used_edge_nodes(merged)) {
                    int r = qs[t]->info.edge_row[u];
                    if (r < 0) continue;
                    int o = owners[t][r];
                    if ((o >= 0 && o != i && o != j) || reserved[t][r]) return false;
                }
            }
            return true;
        };

        for (int oi = 0; oi < full; ++oi) {
            if ((oi & 127) == 0) check_time(deadline);
            int i = order[oi];
            if (matched[i]) continue;
            int best_j = -1, best_size = -1;
            Component best_merged;
            const int stop = std::min(full, oi + 1 + window);
            for (int oj = oi + 1; oj < stop; ++oj) {
                int j = order[oj];
                if (matched[j]) continue;
                Component merged = component_union(forest[i], forest[j]);
                if (merged.size() <= best_size) continue;
                if (!is_valid_component_all(qs, merged)) continue;
                if (!fits(merged, i, j)) continue;
                best_j = j;
                best_size = merged.size();
                best_merged = std::move(merged);
            }
            if (best_j < 0) continue;
            for (std::size_t t = 0; t < qs.size(); ++t) {
                for (int u : qs[t]->used_edge_nodes(best_merged)) {
                    int r = qs[t]->info.edge_row[u];
                    if (r >= 0) reserved[t][r] = 1;
                }
            }
            matched[i] = matched[best_j] = 1;
            merges.push_back(std::move(best_merged));
            any = true;
        }

        if (!any) break;
        std::vector<Component> next;
        next.reserve(full);
        for (int i = 0; i < full; ++i) if (!matched[i]) next.push_back(std::move(forest[i]));
        for (Component& m : merges) next.push_back(std::move(m));
        if (!forest_is_valid_all(n, qs, next)) break;
        forest = std::move(next);
        set_best_forest(forest);
    }
    return forest;
}

static std::vector<Component> enumerate_multi_tree_columns(
    int n, const std::vector<TreeQueries*>& qs, TimePoint deadline
) {
    std::vector<Component> cols;
    if (n > 22) return cols;
    const std::uint64_t total = 1ULL << n;
    std::vector<int> leaves;
    for (std::uint64_t mask = 1; mask < total; ++mask) {
        if ((mask & (mask - 1)) == 0) continue;
        if ((mask & 4095ULL) == 0) check_time(deadline);
        leaves.clear();
        for (int i = 0; i < n; ++i)
            if (mask & (1ULL << i)) leaves.push_back(i + 1);
        Component c(leaves);
        if (is_valid_component_all(qs, c)) cols.push_back(std::move(c));
    }
    return cols;
}

struct IlpResult;
static IlpResult solve_master_ilp_all(
    int n, const std::vector<Component>& cols, const std::vector<TreeQueries*>& qs,
    double time_limit, bool quiet
);

static std::vector<Component> greedy_round(
    int n, const std::vector<Component>& cols, TreeQueries& q1, TreeQueries& q2,
    const std::vector<double>* x
) {
    int m = static_cast<int>(cols.size());
    std::vector<int> order(m);
    std::iota(order.begin(), order.end(), 0);
    std::vector<double> score(m, 0.0);
    for (int i = 0; i < m; ++i) {
        double xi = (x && i < (int)x->size() && (*x)[i] == (*x)[i]) ? (*x)[i] : 0.0;
        int sz = cols[i].size();
        int used = (int)(q1.used_edge_nodes(cols[i]).size() + q2.used_edge_nodes(cols[i]).size());
        score[i] = 1e6 * xi + 1e3 * double(sz) * sz - 0.25 * used;
    }
    std::sort(order.begin(), order.end(), [&](int a, int b) {
        if (score[a] != score[b]) return score[a] > score[b];
        return cols[a].leaves < cols[b].leaves;
    });
    std::vector<char> leaf_used(n + 1, 0), used1(q1.info.edge_nodes.size(), 0), used2(q2.info.edge_nodes.size(), 0);
    std::vector<Component> forest;
    auto can_add = [&](const Component& c) {
        if (c.size() <= 1) return false;
        for (int l : c.leaves) if (l < 1 || l > n || leaf_used[l]) return false;
        if (!is_valid_component(q1, q2, c)) return false;
        for (int u : q1.used_edge_nodes(c)) { int r = q1.info.edge_row[u]; if (r >= 0 && used1[r]) return false; }
        for (int u : q2.used_edge_nodes(c)) { int r = q2.info.edge_row[u]; if (r >= 0 && used2[r]) return false; }
        return true;
    };
    auto add = [&](const Component& c) {
        forest.push_back(c);
        for (int l : c.leaves) leaf_used[l] = 1;
        for (int u : q1.used_edge_nodes(c)) { int r = q1.info.edge_row[u]; if (r >= 0) used1[r] = 1; }
        for (int u : q2.used_edge_nodes(c)) { int r = q2.info.edge_row[u]; if (r >= 0) used2[r] = 1; }
    };
    for (int idx : order) if (can_add(cols[idx])) add(cols[idx]);
    for (int l = 1; l <= n; ++l) if (!leaf_used[l]) add(Component(std::vector<int>{l}));
    if (!forest_is_valid(n, q1, q2, forest)) forest = singleton_forest(n);
    return forest;
}

// ---------------------------------------------------------------------
// Subtree and 3-2-chain kernelization
// ---------------------------------------------------------------------
struct SubtreeReduction {
    std::string newick1;
    std::string newick2;
    int reduced_n = 0;
    std::vector<std::vector<int>> expansion;
    std::vector<Component> forced_components;
    int subtree_contractions = 0;
    int three_two_reductions = 0;
    int chain_reductions = 0;
    int chain_leaves_removed = 0;
    double elapsed_seconds = 0.0;
    std::vector<std::vector<int>> chains;   // common chains (reduced labels), NOT collapsed
    bool changed = false;
};

static std::string serialize_reduced_newick(
    const std::vector<char>& leaf,
    const std::vector<int>& lc,
    const std::vector<int>& rc,
    const std::vector<int>& lab,
    const std::vector<int>& newlabel,
    int root
) {
    std::string out;
    struct Frame { int node; int stage; };
    std::vector<Frame> st;
    st.push_back({root, 0});
    while (!st.empty()) {
        Frame& f = st.back();
        int u = f.node;
        if (leaf[u]) {
            out += std::to_string(newlabel[lab[u]]);
            st.pop_back();
            continue;
        }
        if (f.stage == 0) { out += '('; f.stage = 1; st.push_back({lc[u], 0}); continue; }
        if (f.stage == 1) { out += ','; f.stage = 2; st.push_back({rc[u], 0}); continue; }
        out += ')';
        st.pop_back();
    }
    return out;
}

static SubtreeReduction compute_subtree_reduction(
    const TreeInfo& t1, const TreeInfo& t2, int n, bool enable_three_two, bool enable_chain
) {
    const TimePoint start = Clock::now();
    auto copy_tree = [](
        const TreeInfo& t,
        std::vector<char>& leaf,
        std::vector<char>& node_alive,
        std::vector<int>& parent,
        std::vector<int>& lc,
        std::vector<int>& rc,
        std::vector<int>& lab,
        std::vector<int>& node_of_label
    ) {
        int m = static_cast<int>(t.nodes.size());
        leaf.assign(m, 0);
        node_alive.assign(m, 1);
        parent.assign(m, -1);
        lc.assign(m, -1);
        rc.assign(m, -1);
        lab.assign(m, 0);
        node_of_label.assign(t.n + 1, -1);
        for (int i = 0; i < m; ++i) {
            leaf[i] = t.nodes[i].is_leaf ? 1 : 0;
            parent[i] = t.nodes[i].parent;
            lc[i] = t.nodes[i].left;
            rc[i] = t.nodes[i].right;
            lab[i] = t.nodes[i].label;
            if (leaf[i]) node_of_label[lab[i]] = i;
        }
    };
    std::vector<char> l1, l2, node_alive1, node_alive2;
    std::vector<int> p1, p2, lc1, rc1, lab1, lc2, rc2, lab2;
    std::vector<int> node_of_label1, node_of_label2;
    copy_tree(t1, l1, node_alive1, p1, lc1, rc1, lab1, node_of_label1);
    copy_tree(t2, l2, node_alive2, p2, lc2, rc2, lab2, node_of_label2);
    int root1 = t1.root;
    int root2 = t2.root;
    std::vector<std::vector<int>> exp(n + 1);
    std::vector<char> alive(n + 1, 1);
    for (int L = 1; L <= n; ++L) exp[L] = {L};

    auto key = [](int a, int b) -> std::uint64_t {
        if (a > b) std::swap(a, b);
        return (static_cast<std::uint64_t>(static_cast<std::uint32_t>(a)) << 32) |
               static_cast<std::uint32_t>(b);
    };

    auto sibling = [](
        const std::vector<int>& lc,
        const std::vector<int>& rc,
        int parent,
        int child
    ) -> int {
        if (parent < 0) return -1;
        if (lc[parent] == child) return rc[parent];
        if (rc[parent] == child) return lc[parent];
        return -1;
    };

    auto is_cherry = [&](
        const std::vector<char>& node_alive,
        const std::vector<int>& parent,
        const std::vector<int>& node_of_label,
        int a,
        int b
    ) -> bool {
        if (a <= 0 || b <= 0 || a == b ||
            a >= static_cast<int>(node_of_label.size()) ||
            b >= static_cast<int>(node_of_label.size())) {
            return false;
        }
        const int ua = node_of_label[a];
        const int ub = node_of_label[b];
        return ua >= 0 && ub >= 0 && node_alive[ua] && node_alive[ub] &&
               parent[ua] >= 0 && parent[ua] == parent[ub];
    };

    auto delete_leaf = [&](
        std::vector<char>& node_alive,
        std::vector<int>& parent,
        std::vector<int>& lc,
        std::vector<int>& rc,
        std::vector<int>& node_of_label,
        int& root,
        int label
    ) -> bool {
        if (label <= 0 || label >= static_cast<int>(node_of_label.size())) return false;
        const int leaf = node_of_label[label];
        if (leaf < 0 || !node_alive[leaf]) return false;
        const int par = parent[leaf];
        if (par < 0) return false;
        const int sib = sibling(lc, rc, par, leaf);
        if (sib < 0 || !node_alive[sib]) return false;
        const int grandparent = parent[par];
        if (grandparent < 0) {
            root = sib;
            parent[sib] = -1;
        } else {
            if (lc[grandparent] == par) lc[grandparent] = sib;
            else if (rc[grandparent] == par) rc[grandparent] = sib;
            else return false;
            parent[sib] = grandparent;
        }
        node_alive[leaf] = 0;
        node_alive[par] = 0;
        node_of_label[label] = -1;
        return true;
    };

    struct ThreeTwoEvent {
        int direction = 0;
        int x1 = 0;
        int x2 = 0;
        int x3 = 0;
        int keep = 0;
        int remove = 0;
    };

    auto collect_three_two = [&](
        const std::vector<char>& chain_leaf,
        const std::vector<char>& chain_node_alive,
        const std::vector<int>& chain_parent,
        const std::vector<int>& chain_lc,
        const std::vector<int>& chain_rc,
        const std::vector<int>& chain_lab,
        const std::vector<char>& pendant_node_alive,
        const std::vector<int>& pendant_parent,
        const std::vector<int>& pendant_node_of_label,
        int direction,
        std::vector<ThreeTwoEvent>& events
    ) {
        for (int par = 0; par < static_cast<int>(chain_node_alive.size()); ++par) {
            if (!chain_node_alive[par] || chain_leaf[par]) continue;
            const int left = chain_lc[par];
            const int right = chain_rc[par];
            if (left < 0 || right < 0 ||
                !chain_node_alive[left] || !chain_node_alive[right] ||
                !chain_leaf[left] || !chain_leaf[right]) {
                continue;
            }
            const int grandparent = chain_parent[par];
            if (grandparent < 0) continue;
            const int uncle = sibling(chain_lc, chain_rc, grandparent, par);
            if (uncle < 0 || !chain_node_alive[uncle] || !chain_leaf[uncle]) {
                continue;
            }

            const int x1 = chain_lab[left];
            const int x2 = chain_lab[right];
            const int x3 = chain_lab[uncle];
            if (!alive[x1] || !alive[x2] || !alive[x3]) continue;
            if (is_cherry(pendant_node_alive, pendant_parent, pendant_node_of_label, x1, x3)) {
                events.push_back({direction, x1, x2, x3, x1, x2});
            } else if (is_cherry(pendant_node_alive, pendant_parent, pendant_node_of_label, x2, x3)) {
                events.push_back({direction, x1, x2, x3, x2, x1});
            }
        }
    };

    auto three_two_valid = [&](
        const ThreeTwoEvent& event,
        const std::vector<char>& chain_node_alive,
        const std::vector<int>& chain_parent,
        const std::vector<int>& chain_lc,
        const std::vector<int>& chain_rc,
        const std::vector<int>& chain_lab,
        const std::vector<int>& chain_node_of_label,
        const std::vector<char>& pendant_node_alive,
        const std::vector<int>& pendant_parent,
        const std::vector<int>& pendant_node_of_label
    ) -> bool {
        if (!is_cherry(chain_node_alive, chain_parent, chain_node_of_label, event.x1, event.x2)) {
            return false;
        }
        const int first_leaf = chain_node_of_label[event.x1];
        const int cherry_parent = chain_parent[first_leaf];
        const int grandparent = chain_parent[cherry_parent];
        if (grandparent < 0) return false;
        const int uncle = sibling(chain_lc, chain_rc, grandparent, cherry_parent);
        if (uncle < 0 || !chain_node_alive[uncle] || chain_lab[uncle] != event.x3) {
            return false;
        }
        return is_cherry(pendant_node_alive, pendant_parent, pendant_node_of_label, event.keep, event.x3);
    };

    SubtreeReduction red;

    // Common-chain detection (MAF). A maximal common m-chain is a run of pendant leaves
    // that hang, in the SAME root-to-leaf order, off a caterpillar spine in BOTH trees.
    // We do NOT collapse it (collapsing loses the interior spine edges and lets a forest
    // that is edge-disjoint on the reduced trees lift to one that is not on the originals).
    // Instead we detect each chain and hand it to the solver as a whole component to seed
    // from -- keeping a common chain intact is optimal, and its edges stay in the model.
    // up_neighbor gives, for a leaf L, the leaf directly above it on the spine, but only
    // when the step has the same rooted direction in both trees.
    auto up_neighbor = [&](const std::vector<char>& na, const std::vector<int>& par,
                           const std::vector<int>& clc, const std::vector<int>& crc,
                           const std::vector<char>& lf, const std::vector<int>& lab,
                           const std::vector<int>& nol, int L) -> int {
        if (L <= 0 || L >= static_cast<int>(nol.size())) return 0;
        const int u = nol[L];
        if (u < 0 || !na[u]) return 0;
        const int p = par[u];
        if (p < 0) return 0;
        const int sib = sibling(clc, crc, p, u);
        if (sib < 0 || !na[sib] || lf[sib]) return 0;  // pendant of a spine: sibling is internal
        const int gp = par[p];
        if (gp < 0) return 0;
        const int uncle = sibling(clc, crc, gp, p);
        if (uncle < 0 || !na[uncle] || !lf[uncle]) return 0;  // leaf directly above on the spine
        return lab[uncle];
    };


    bool any = false;
    while (true) {
        std::unordered_map<std::uint64_t, int> ch1, ch2;
        for (int u = 0; u < static_cast<int>(l1.size()); ++u) {
            if (!node_alive1[u] || l1[u]) continue;
            int a = lc1[u], b = rc1[u];
            if (a >= 0 && b >= 0 && node_alive1[a] && node_alive1[b] && l1[a] && l1[b]) {
                ch1[key(lab1[a], lab1[b])] = u;
            }
        }
        for (int u = 0; u < static_cast<int>(l2.size()); ++u) {
            if (!node_alive2[u] || l2[u]) continue;
            int a = lc2[u], b = rc2[u];
            if (a >= 0 && b >= 0 && node_alive2[a] && node_alive2[b] && l2[a] && l2[b]) {
                ch2[key(lab2[a], lab2[b])] = u;
            }
        }
        bool pass_changed = false;
        for (const auto& kv : ch1) {
            auto it = ch2.find(kv.first);
            if (it == ch2.end()) continue;
            int u1 = kv.second, u2 = it->second;
            if (!node_alive1[u1] || !node_alive2[u2] || l1[u1] || l2[u2]) continue;
            int a = lab1[lc1[u1]], b = lab1[rc1[u1]];
            if (!alive[a] || !alive[b]) continue;
            int rep = std::min(a, b), other = std::max(a, b);
            node_alive1[lc1[u1]] = 0; node_alive1[rc1[u1]] = 0;
            l1[u1] = 1; lc1[u1] = -1; rc1[u1] = -1; lab1[u1] = rep;
            node_alive2[lc2[u2]] = 0; node_alive2[rc2[u2]] = 0;
            l2[u2] = 1; lc2[u2] = -1; rc2[u2] = -1; lab2[u2] = rep;
            node_of_label1[rep] = u1; node_of_label1[other] = -1;
            node_of_label2[rep] = u2; node_of_label2[other] = -1;
            for (int x : exp[other]) exp[rep].push_back(x);
            exp[other].clear();
            alive[other] = 0;
            pass_changed = true;
            any = true;
            ++red.subtree_contractions;
        }
        if (pass_changed) continue;
        if (!enable_three_two) break;

        std::vector<ThreeTwoEvent> events;
        collect_three_two(l1, node_alive1, p1, lc1, rc1, lab1, node_alive2, p2, node_of_label2, 0, events);
        collect_three_two(l2, node_alive2, p2, lc2, rc2, lab2, node_alive1, p1, node_of_label1, 1, events);
        std::sort(events.begin(), events.end(), [](const auto& a, const auto& b) {
            return std::tie(a.remove, a.keep, a.x3, a.direction) <
                   std::tie(b.remove, b.keep, b.x3, b.direction);
        });
        events.erase(
            std::unique(events.begin(), events.end(), [](const auto& a, const auto& b) {
                return a.remove == b.remove && a.keep == b.keep &&
                       a.x3 == b.x3 && a.direction == b.direction;
            }),
            events.end());

        std::vector<ThreeTwoEvent> selected;
        std::vector<char> touched(n + 1, 0);
        for (const ThreeTwoEvent& event : events) {
            if (touched[event.x1] || touched[event.x2] || touched[event.x3]) continue;
            selected.push_back(event);
            touched[event.x1] = touched[event.x2] = touched[event.x3] = 1;
        }

        int applied = 0;
        for (const ThreeTwoEvent& event : selected) {
            const bool direction_one = event.direction == 0;
            const bool valid = direction_one
                ? three_two_valid(event, node_alive1, p1, lc1, rc1, lab1, node_of_label1, node_alive2, p2, node_of_label2)
                : three_two_valid(event, node_alive2, p2, lc2, rc2, lab2, node_of_label2, node_alive1, p1, node_of_label1);
            if (!valid || exp[event.remove].empty()) continue;

            Component forced(exp[event.remove]);
            if (!delete_leaf(node_alive1, p1, lc1, rc1, node_of_label1, root1, event.remove) ||
                !delete_leaf(node_alive2, p2, lc2, rc2, node_of_label2, root2, event.remove)) {
                throw std::runtime_error("Failed to apply a validated 3-2-chain reduction.");
            }
            red.forced_components.push_back(std::move(forced));
            exp[event.remove].clear();
            alive[event.remove] = 0;
            ++applied;
            ++red.three_two_reductions;
            any = true;
        }
        if (applied == 0) break;
    }

    // Detect maximal common chains on the reduced trees WITHOUT collapsing them. Keeping
    // their leaves (and thus their spine edges) in the model is what makes the lift sound;
    // the solver treats each chain as one pre-seeded component (optimal, since splitting a
    // common chain only adds components).
    std::vector<std::vector<int>> chains_cur;
    if (enable_chain) {
        std::vector<int> succ(n + 1, 0), pred(n + 1, 0);
        for (int L = 1; L <= n; ++L) {
            if (!alive[L]) continue;
            int u1 = up_neighbor(node_alive1, p1, lc1, rc1, l1, lab1, node_of_label1, L);
            if (u1 == 0) continue;
            int u2 = up_neighbor(node_alive2, p2, lc2, rc2, l2, lab2, node_of_label2, L);
            if (u2 == 0 || u2 != u1 || !alive[u1]) continue;
            succ[L] = u1; pred[u1] = L;
        }
        for (int L = 1; L <= n; ++L) {
            if (!alive[L] || pred[L] != 0 || succ[L] == 0) continue;  // chain start
            std::vector<int> ch;
            for (int cur = L; cur != 0 && alive[cur]; cur = succ[cur]) ch.push_back(cur);
            if ((int)ch.size() >= 4) { chains_cur.push_back(std::move(ch)); ++red.chain_reductions; }
        }
    }

    std::vector<int> survivors;
    for (int L = 1; L <= n; ++L) if (alive[L]) survivors.push_back(L);
    int rn = static_cast<int>(survivors.size());

    std::vector<int> newlabel(n + 1, 0);
    red.reduced_n = rn;
    red.expansion.assign(rn + 1, {});
    for (int i = 0; i < rn; ++i) {
        int L = survivors[i];
        newlabel[L] = i + 1;
        std::sort(exp[L].begin(), exp[L].end());
        red.expansion[i + 1] = exp[L];
    }
    for (auto& ch : chains_cur) {
        std::vector<int> rc;
        for (int L : ch) if (L >= 1 && L <= n && newlabel[L]) rc.push_back(newlabel[L]);
        if (rc.size() >= 2) red.chains.push_back(std::move(rc));
    }
    red.newick1 = serialize_reduced_newick(l1, lc1, rc1, lab1, newlabel, root1);
    red.newick2 = serialize_reduced_newick(l2, lc2, rc2, lab2, newlabel, root2);
    red.changed = any && rn < n;
    red.elapsed_seconds = std::chrono::duration<double>(Clock::now() - start).count();
    return red;
}

// ---------------------------------------------------------------------
// Edge-packing master (HiGHS)
// ---------------------------------------------------------------------
static void column_edges(const Component& c, TreeQueries& q1, TreeQueries& q2,
                         int t1_off, int t2_off, std::vector<int>& out) {
    out.clear();
    for (int u : q1.used_edge_nodes(c)) { int r = q1.info.edge_row[u]; if (r >= 0) out.push_back(t1_off + r); }
    for (int u : q2.used_edge_nodes(c)) { int r = q2.info.edge_row[u]; if (r >= 0) out.push_back(t2_off + r); }
}

static void build_packing_model(
    HighsModel& model, const std::vector<Component>& cols, int num_rows, int n,
    TreeQueries& q1, TreeQueries& q2, int t1_off, int t2_off
) {
    const int num_cols = (int)cols.size();
    model.lp_.num_col_ = num_cols;
    model.lp_.num_row_ = num_rows;
    model.lp_.sense_ = ObjSense::kMinimize;
    model.lp_.offset_ = double(n);
    model.lp_.col_cost_.resize(num_cols);
    for (int c = 0; c < num_cols; ++c) model.lp_.col_cost_[c] = -double(std::max(0, cols[c].size() - 1));
    model.lp_.col_lower_.assign(num_cols, 0.0);
    model.lp_.col_upper_.assign(num_cols, 1.0);
    model.lp_.row_lower_.assign(num_rows, -1e30);
    model.lp_.row_upper_.assign(num_rows, 1.0);
    auto& A = model.lp_.a_matrix_;
    A.format_ = MatrixFormat::kColwise;
    A.num_col_ = num_cols;
    A.num_row_ = num_rows;
    A.start_.clear(); A.index_.clear(); A.value_.clear();
    A.start_.reserve(num_cols + 1);
    std::vector<int> es;
    for (const Component& c : cols) {
        A.start_.push_back((HighsInt)A.index_.size());
        for (int leaf : c.leaves) { A.index_.push_back(leaf - 1); A.value_.push_back(1.0); }
        column_edges(c, q1, q2, t1_off, t2_off, es);
        for (int e : es) { A.index_.push_back(e); A.value_.push_back(1.0); }
    }
    A.start_.push_back((HighsInt)A.index_.size());
}

struct IlpResult {
    bool ok = false;
    std::vector<Component> forest;
};

static IlpResult solve_master_ilp_all(
    int n, const std::vector<Component>& cols, const std::vector<TreeQueries*>& qs,
    double time_limit, bool quiet
) {
    IlpResult res;
    if (qs.empty()) return res;
    if (cols.empty()) {
        res.ok = true;
        res.forest = greedy_merge_improvement_all(n, qs, singleton_forest(n), Clock::now());
        if (res.forest.empty()) res.forest = singleton_forest(n);
        return res;
    }
    if (time_limit <= 0.0) return res;

    std::vector<int> tree_off(qs.size(), n);
    int num_rows = n;
    for (std::size_t t = 0; t < qs.size(); ++t) {
        tree_off[t] = num_rows;
        num_rows += (int)qs[t]->info.edge_nodes.size();
    }

    HighsModel model;
    const int num_cols = (int)cols.size();
    model.lp_.num_col_ = num_cols;
    model.lp_.num_row_ = num_rows;
    model.lp_.sense_ = ObjSense::kMinimize;
    model.lp_.offset_ = double(n);
    model.lp_.col_cost_.resize(num_cols);
    for (int c = 0; c < num_cols; ++c) model.lp_.col_cost_[c] = -double(std::max(0, cols[c].size() - 1));
    model.lp_.col_lower_.assign(num_cols, 0.0);
    model.lp_.col_upper_.assign(num_cols, 1.0);
    model.lp_.row_lower_.assign(num_rows, -1e30);
    model.lp_.row_upper_.assign(num_rows, 1.0);
    model.lp_.integrality_.assign(num_cols, HighsVarType::kInteger);

    auto& A = model.lp_.a_matrix_;
    A.format_ = MatrixFormat::kColwise;
    A.num_col_ = num_cols;
    A.num_row_ = num_rows;
    A.start_.clear(); A.index_.clear(); A.value_.clear();
    A.start_.reserve(num_cols + 1);
    for (const Component& c : cols) {
        A.start_.push_back((HighsInt)A.index_.size());
        for (int leaf : c.leaves) {
            A.index_.push_back(leaf - 1);
            A.value_.push_back(1.0);
        }
        for (std::size_t t = 0; t < qs.size(); ++t) {
            for (int u : qs[t]->used_edge_nodes(c)) {
                int r = qs[t]->info.edge_row[u];
                if (r >= 0) {
                    A.index_.push_back(tree_off[t] + r);
                    A.value_.push_back(1.0);
                }
            }
        }
    }
    A.start_.push_back((HighsInt)A.index_.size());

    Highs highs;
    highs.setOptionValue("output_flag", false);
    highs.setOptionValue("log_to_console", false);
    highs.setOptionValue("time_limit", time_limit);
    highs.setOptionValue("mip_rel_gap", 0.0);
    highs.setOptionValue("threads", 1);
    highs.setOptionValue("random_seed", 0);

    auto fallback = [&]() {
        res.ok = true;
        res.forest = greedy_merge_improvement_all(
            n, qs, g_best_forest.empty() ? singleton_forest(n) : g_best_forest,
            Clock::now() + std::chrono::duration_cast<Clock::duration>(std::chrono::duration<double>(std::max(0.01, 0.15 * time_limit))));
        if (!forest_is_valid_all(n, qs, res.forest)) res.forest = singleton_forest(n);
        return res;
    };

    if (highs.passModel(model) != HighsStatus::kOk) return fallback();
    HighsStatus rs = highs.run();
    if (rs != HighsStatus::kOk && rs != HighsStatus::kWarning) return fallback();
    HighsSolution sol = highs.getSolution();
    if ((int)sol.col_value.size() < num_cols) return fallback();

    std::vector<Component> chosen;
    std::vector<char> covered(n + 1, 0);
    for (int i = 0; i < num_cols; ++i) {
        if (cols[i].size() <= 1 || sol.col_value[i] <= 0.5) continue;
        chosen.push_back(cols[i]);
        for (int l : cols[i].leaves) if (l >= 1 && l <= n) covered[l] = 1;
    }
    for (int l = 1; l <= n; ++l) if (!covered[l]) chosen.emplace_back(std::vector<int>{l});
    if (forest_is_valid_all(n, qs, chosen)) {
        res.ok = true;
        res.forest = std::move(chosen);
        return res;
    }
    if (!quiet) log_out() << "Multi-tree MIP solution invalid; using greedy fallback.\n";
    return fallback();
}

static IlpResult solve_master_ilp(
    int n, const std::vector<Component>& cols, TreeQueries& q1, TreeQueries& q2,
    double time_limit, bool quiet
) {
    IlpResult res;
    if (cols.empty()) { res.ok = true; res.forest = singleton_forest(n); return res; }
    if (time_limit <= 0.0) return res;
    const int num_rows = n + (int)q1.info.edge_nodes.size() + (int)q2.info.edge_nodes.size();
    const int t1_off = n, t2_off = n + (int)q1.info.edge_nodes.size();

    // Memory safety: an unbounded integer master over a ~3n-row model can allocate
    // many GB and be OOM-killed (score 0). Keep at most a budget-scaled number of
    // columns; callers pass their most valuable columns first, so truncation keeps
    // the best ones.
    const int col_cap = ilp_master_column_cap(num_rows);
    std::vector<Component> capped;
    if ((int)cols.size() > col_cap) {
        capped.assign(cols.begin(), cols.begin() + col_cap);
        if (!quiet) log_out() << "Master ILP: capped " << cols.size() << " -> " << col_cap
                              << " cols (memory budget, rows " << num_rows << ")\n";
    }
    const std::vector<Component>& C = ((int)cols.size() > col_cap) ? capped : cols;
    const int num_cols = (int)C.size();

    HighsModel model;
    build_packing_model(model, C, num_rows, n, q1, q2, t1_off, t2_off);
    model.lp_.integrality_.assign(num_cols, HighsVarType::kInteger);

    Highs highs;
    highs.setOptionValue("output_flag", false);
    highs.setOptionValue("log_to_console", false);
    highs.setOptionValue("time_limit", time_limit);
    highs.setOptionValue("mip_rel_gap", 0.0);
    highs.setOptionValue("threads", 1);
    highs.setOptionValue("random_seed", 0);
    highs.setOptionValue("presolve", "off");

    auto fallback = [&](const std::vector<double>* x) {
        res.ok = true; res.forest = greedy_round(n, cols, q1, q2, x); return res;
    };
    if (highs.passModel(model) != HighsStatus::kOk) return fallback(nullptr);

    if (!g_best_forest.empty()) {
        std::unordered_set<Component, ComponentHash> inc;
        for (const Component& c : g_best_forest) if (c.size() > 1) inc.insert(c);
        if (!inc.empty()) {
            HighsSolution start;
            start.col_value.assign(num_cols, 0.0);
            for (int i = 0; i < num_cols; ++i) if (inc.count(C[i])) start.col_value[i] = 1.0;
            highs.setSolution(start);
        }
    }

    HighsStatus rs = highs.run();
    if (rs != HighsStatus::kOk && rs != HighsStatus::kWarning) return fallback(nullptr);
    HighsSolution sol = highs.getSolution();
    if ((int)sol.col_value.size() < num_cols) return fallback(nullptr);

    std::vector<Component> chosen;
    for (int i = 0; i < num_cols; ++i) if (C[i].size() > 1 && sol.col_value[i] > 0.5) chosen.push_back(C[i]);
    std::vector<char> covered(n + 1, 0);
    for (const Component& c : chosen) for (int l : c.leaves) if (l >= 1 && l <= n) covered[l] = 1;
    for (int l = 1; l <= n; ++l) if (!covered[l]) chosen.emplace_back(std::vector<int>{l});

    if (forest_is_valid(n, q1, q2, chosen)) { res.ok = true; res.forest = std::move(chosen); return res; }
    if (!quiet) log_out() << "MIP solution not a valid forest; greedy-repairing.\n";
    return fallback(&sol.col_value);
}

// ---------------------------------------------------------------------
// Exact branch pricer (WmastPricer)
// ---------------------------------------------------------------------
static double component_branch_profit(const Component& c, TreeQueries& q1, TreeQueries& q2,
                                      const std::vector<double>& dual, int t1_off, int t2_off) {
    double profit = std::max(0, c.size() - 1);
    for (int l : c.leaves) profit += dual[l - 1];
    for (int v : q1.used_edge_nodes(c)) { int r = q1.info.edge_row[v]; if (r >= 0) profit += dual[t1_off + r]; }
    for (int v : q2.used_edge_nodes(c)) { int r = q2.info.edge_row[v]; if (r >= 0) profit += dual[t2_off + r]; }
    return profit;
}

struct CherryMutForest {
    std::vector<int> par, c0, c1, blk;
    std::vector<char> alive, leaf;
};

static void cherry_build_template(const TreeInfo& t, CherryMutForest& f, std::vector<int>& block_leaf_node) {
    const int m = (int)t.nodes.size();
    f.par.resize(m); f.c0.resize(m); f.c1.resize(m);
    f.alive.assign(m, 1); f.leaf.assign(m, 0); f.blk.assign(m, -1);
    for (int i = 0; i < m; ++i) {
        f.par[i] = t.nodes[i].parent; f.c0[i] = t.nodes[i].left; f.c1[i] = t.nodes[i].right;
        if (t.nodes[i].is_leaf) { f.leaf[i] = 1; f.blk[i] = t.nodes[i].label; block_leaf_node[t.nodes[i].label] = i; }
    }
}

static void cherry_cut_node(CherryMutForest& f, int leafnode, std::vector<int>* wl) {
    f.alive[leafnode] = 0;
    const int P = f.par[leafnode];
    if (P < 0) return;
    const int S = (f.c0[P] == leafnode) ? f.c1[P] : f.c0[P];
    const int GP = f.par[P];
    f.alive[P] = 0;
    if (GP < 0) { f.par[S] = -1; }
    else { if (f.c0[GP] == P) f.c0[GP] = S; else f.c1[GP] = S; f.par[S] = GP; if (wl) wl->push_back(GP); }
}

class WmastPricer {
public:
    WmastPricer(int n, TreeQueries& q1, TreeQueries& q2, int t1_off, int t2_off,
                std::size_t cell_budget = wmast_cell_budget())
        : n_(n), q1_(q1), q2_(q2), T1_(q1.info), T2_(q2.info), t1_off_(t1_off), t2_off_(t2_off) {
        N1_ = (int)T1_.nodes.size();
        N2_ = (int)T2_.nodes.size();
        build_tree(T1_, left1_, right1_, leaf1_, label1_, post1_);
        build_tree(T2_, left2_, right2_, leaf2_, label2_, post2_);
        edge_w1_.assign(N1_, 0.0);
        edge_w2_.assign(N2_, 0.0);
        std::vector<int> leafcount1(N1_, 0), leafcount2(N2_, 0);
        for (int u : post1_) leafcount1[u] = leaf1_[u] ? 1 : leafcount1[left1_[u]] + leafcount1[right1_[u]];
        for (int v : post2_) leafcount2[v] = leaf2_[v] ? 1 : leafcount2[left2_[v]] + leafcount2[right2_[v]];
        cover_count_.assign(n_ + 1, 0);
        cover_stamp_.assign(n_ + 1, 0);
        try { build_sparse(leafcount1, leafcount2, cell_budget); feasible_ = true; }
        catch (const std::bad_alloc&) { feasible_ = false; clear_sparse(); }
    }
    bool feasible() const { return feasible_; }
    bool found_improving() const { return found_improving_; }
    std::size_t cells() const { return cells_; }
    double max_profit() const { return max_profit_; }

    std::vector<Component> price(const std::vector<double>& dual, const std::unordered_set<Component, ComponentHash>& pool,
                                 TimePoint deadline, int max_new, int cover_cap) {
        std::vector<Component> out;
        max_profit_ = 0.0;
        if (!feasible_ || max_new <= 0) { found_improving_ = false; return out; }
        if (cover_cap <= 0) cover_cap = std::numeric_limits<int>::max();
        for (int u = 0; u < N1_; ++u) { int r = T1_.edge_row[u]; edge_w1_[u] = (r >= 0) ? dual[t1_off_ + r] : 0.0; }
        for (int v = 0; v < N2_; ++v) { int r = T2_.edge_row[v]; edge_w2_[v] = (r >= 0) ? dual[t2_off_ + r] : 0.0; }

        fill_and_harvest(deadline, dual);
        if (!found_improving_) return out;

        std::sort(cands_.begin(), cands_.end(), [](const Cand& a, const Cand& b) { return a.profit > b.profit; });

        std::vector<Component> kept;
        const std::size_t budget = std::min(
            std::numeric_limits<std::size_t>::max() - 64,
            saturating_mul(static_cast<std::size_t>(max_new), 4)) + 64;
        std::unordered_set<Component, ComponentHash> seen;
        std::vector<int> leaves;
        int scanned = 0;
        for (const Cand& c : cands_) {
            if (kept.size() >= budget) break;
            if ((scanned++ & 1023) == 0) check_time(deadline);
            leaves.clear();
            trace_top(c, leaves);
            if (leaves.empty()) continue;
            Component comp(std::move(leaves));
            if (comp.size() <= 1) continue;
            if (pool.find(comp) != pool.end()) continue;
            if (!seen.insert(comp).second) continue;
            double p = component_branch_profit(comp, q1_, q2_, dual, t1_off_, t2_off_);
            if (p <= kProfitEps) continue;
            if (kept.empty()) max_profit_ = p;
            kept.push_back(std::move(comp));
        }

        found_improving_ = !kept.empty();

        if (++cover_epoch_ == std::numeric_limits<int>::max()) { std::fill(cover_stamp_.begin(), cover_stamp_.end(), 0); cover_epoch_ = 1; }
        for (Component& k : kept) {
            if ((int)out.size() >= max_new) break;
            bool fresh = false;
            for (int l : k.leaves) if (cover_of(l) < cover_cap) { fresh = true; break; }
            if (!fresh) continue;
            for (int l : k.leaves) bump_cover(l);
            out.push_back(std::move(k));
        }
        return out;
    }
private:
    struct Cand { double profit; int ci; unsigned char split; };
    static constexpr double kNeg = -1e30;
    static constexpr double kProfitEps = 1e-7;
    enum Choice : unsigned char { kNone, kLeaf, kSkipULeft, kSkipURight, kSkipVLeft, kSkipVRight, kSplitStraight, kSplitCross };
    void build_tree(const TreeInfo& T, std::vector<int>& left, std::vector<int>& right,
                    std::vector<char>& leaf, std::vector<int>& label, std::vector<int>& post) {
        int N = (int)T.nodes.size();
        left.assign(N, -1); right.assign(N, -1); leaf.assign(N, 0); label.assign(N, -1);
        for (int u = 0; u < N; ++u) {
            const auto& nu = T.nodes[u];
            leaf[u] = nu.is_leaf ? 1 : 0;
            if (nu.is_leaf) label[u] = nu.label; else { left[u] = nu.left; right[u] = nu.right; }
        }
        post.clear();
        post.reserve(N);
        std::vector<int> st{T.root};
        while (!st.empty()) {
            int u = st.back(); st.pop_back();
            post.push_back(u);
            if (!T.nodes[u].is_leaf) { st.push_back(T.nodes[u].left); st.push_back(T.nodes[u].right); }
        }
        std::reverse(post.begin(), post.end());
    }

    void clear_sparse() {
        cu_.clear(); cv_.clear(); split_idx_.clear();
        d_su0_.clear(); d_su1_.clear(); d_sv0_.clear(); d_sv1_.clear();
        d_ss00_.clear(); d_ss11_.clear(); d_ss01_.clear(); d_ss10_.clear();
        V_.clear(); choice_.clear();
        cells_ = 0;
    }

    void build_sparse(const std::vector<int>& leafcount1, const std::vector<int>& leafcount2,
                      std::size_t cell_budget) {
        std::vector<int> rank1(N1_, 0), rank2(N2_, 0);
        for (int i = 0; i < N1_; ++i) rank1[post1_[i]] = i;
        for (int i = 0; i < N2_; ++i) rank2[post2_[i]] = i;

        std::vector<std::vector<int>> S(N1_);
        std::vector<std::uint64_t> keys;

        for (int u : post1_) {
            if (leaf1_[u]) {
                int l = label1_[u];
                if (l >= 1 && l < (int)T2_.leaf_node.size()) {
                    int v = T2_.leaf_node[l];
                    if (v >= 0) {
                        for (int curr = v; curr >= 0; curr = T2_.nodes[curr].parent) {
                            S[u].push_back(rank2[curr]);
                        }
                    }
                }
            } else {
                int left = left1_[u];
                int right = right1_[u];
                S[u].reserve(S[left].size() + S[right].size());
                std::set_union(S[left].begin(), S[left].end(),
                               S[right].begin(), S[right].end(),
                               std::back_inserter(S[u]));
                std::vector<int>().swap(S[left]);
                std::vector<int>().swap(S[right]);
            }
            std::uint64_t base = (std::uint64_t)rank1[u] * (std::uint64_t)N2_;
            for (int rv : S[u]) {
                if (keys.size() >= cell_budget ||
                    keys.size() >= static_cast<std::size_t>(std::numeric_limits<int>::max())) {
                    throw std::bad_alloc();
                }
                keys.push_back(base + (std::uint64_t)rv);
            }
        }

        cells_ = keys.size();
        const int M = (int)cells_;
        cu_.resize(M); cv_.resize(M); split_idx_.assign(M, -1);
        d_su0_.assign(M, -1); d_su1_.assign(M, -1); d_sv0_.assign(M, -1); d_sv1_.assign(M, -1);
        d_ss00_.clear(); d_ss11_.clear(); d_ss01_.clear(); d_ss10_.clear();
        for (int i = 0; i < M; ++i) {
            cu_[i] = post1_[(int)(keys[i] / (std::uint64_t)N2_)];
            cv_[i] = post2_[(int)(keys[i] % (std::uint64_t)N2_)];
        }
        auto look = [&](int u, int v) -> int {
            std::uint64_t k = (std::uint64_t)rank1[u] * (std::uint64_t)N2_ + (std::uint64_t)rank2[v];
            auto it = std::lower_bound(keys.begin(), keys.end(), k);
            return (it != keys.end() && *it == k) ? (int)(it - keys.begin()) : -1;
        };
        for (int i = 0; i < M; ++i) {
            int u = cu_[i], v = cv_[i];
            bool ul = leaf1_[u] != 0, vl = leaf2_[v] != 0;
            if (!ul) { d_su0_[i] = look(left1_[u], v); d_su1_[i] = look(right1_[u], v); }
            if (!vl) { d_sv0_[i] = look(u, left2_[v]); d_sv1_[i] = look(u, right2_[v]); }
            if (!ul && !vl && leafcount1[u] >= 2 && leafcount2[v] >= 2) {
                split_idx_[i] = (int)d_ss00_.size();
                d_ss00_.push_back(look(left1_[u], left2_[v]));
                d_ss11_.push_back(look(right1_[u], right2_[v]));
                d_ss01_.push_back(look(left1_[u], right2_[v]));
                d_ss10_.push_back(look(right1_[u], left2_[v]));
            }
        }
        { std::vector<std::uint64_t> tmp; keys.swap(tmp); }
        d_ss00_.shrink_to_fit(); d_ss11_.shrink_to_fit();
        d_ss01_.shrink_to_fit(); d_ss10_.shrink_to_fit();
        V_.assign(M, static_cast<float>(kNeg));
        choice_.assign(M, kNone);
    }

    static bool fin(double x) { return x > kNeg / 2.0; }
    double Vdep(int i) const { return i >= 0 ? V_[i] : kNeg; }
    double with_edge1(int c, double s) const { return fin(s) ? edge_w1_[c] + s : kNeg; }
    double with_edge2(int c, double s) const { return fin(s) ? edge_w2_[c] + s : kNeg; }
    double pair_score(int uu, int vv, double s) const { return fin(s) ? edge_w1_[uu] + edge_w2_[vv] + s : kNeg; }
    static void upd(double cand, unsigned char cc, double& best, unsigned char& bc) { if (cand > best) { best = cand; bc = cc; } }
    void maybe_harvest(double bs, int i, unsigned char sc) {
        double profit = bs + edge_w1_[cu_[i]] + edge_w2_[cv_[i]] - 1.0;
        if (profit > kProfitEps) { found_improving_ = true; cands_.push_back({profit, i, sc}); }
    }

    void fill_and_harvest(TimePoint deadline, const std::vector<double>& dual) {
        cands_.clear();
        found_improving_ = false;
        const int M = (int)cells_;
        for (int i = 0; i < M; ++i) {
            if ((i & 8191) == 0) check_time(deadline);
            const int u = cu_[i], v = cv_[i];
            const bool ul = leaf1_[u] != 0, vl = leaf2_[v] != 0;
            double best = kNeg;
            unsigned char bc = kNone;
            if (ul && vl) {
                if (label1_[u] == label2_[v]) {
                    int lbl = label1_[u];
                    best = 1.0 + dual[lbl - 1];
                    bc = kLeaf;
                }
            } else {
                if (!ul) {
                    upd(with_edge1(left1_[u], Vdep(d_su0_[i])), kSkipULeft, best, bc);
                    upd(with_edge1(right1_[u], Vdep(d_su1_[i])), kSkipURight, best, bc);
                }
                if (!vl) {
                    upd(with_edge2(left2_[v], Vdep(d_sv0_[i])), kSkipVLeft, best, bc);
                    upd(with_edge2(right2_[v], Vdep(d_sv1_[i])), kSkipVRight, best, bc);
                }
                if (split_idx_[i] >= 0) {
                    const int si = split_idx_[i];
                    double a = pair_score(left1_[u], left2_[v], Vdep(d_ss00_[si]));
                    double b = pair_score(right1_[u], right2_[v], Vdep(d_ss11_[si]));
                    if (fin(a) && fin(b)) { double s = a + b; upd(s, kSplitStraight, best, bc); maybe_harvest(s, i, kSplitStraight); }
                    double c = pair_score(left1_[u], right2_[v], Vdep(d_ss01_[si]));
                    double d = pair_score(right1_[u], left2_[v], Vdep(d_ss10_[si]));
                    if (fin(c) && fin(d)) { double s = c + d; upd(s, kSplitCross, best, bc); maybe_harvest(s, i, kSplitCross); }
                }
            }
            V_[i] = static_cast<float>(best);
            choice_[i] = bc;
        }
    }

    void trace_cell(int start, std::vector<int>& out) const {
        if (start < 0) return;
        trace_stack_.clear();
        trace_stack_.push_back(start);
        while (!trace_stack_.empty()) {
            int i = trace_stack_.back(); trace_stack_.pop_back();
            if (i < 0) continue;
            switch (choice_[i]) {
            case kLeaf: out.push_back(label1_[cu_[i]]); break;
            case kSkipULeft: trace_stack_.push_back(d_su0_[i]); break;
            case kSkipURight: trace_stack_.push_back(d_su1_[i]); break;
            case kSkipVLeft: trace_stack_.push_back(d_sv0_[i]); break;
            case kSkipVRight: trace_stack_.push_back(d_sv1_[i]); break;
            case kSplitStraight: { int si = split_idx_[i]; trace_stack_.push_back(d_ss00_[si]); trace_stack_.push_back(d_ss11_[si]); } break;
            case kSplitCross: { int si = split_idx_[i]; trace_stack_.push_back(d_ss01_[si]); trace_stack_.push_back(d_ss10_[si]); } break;
            default: break;
            }
        }
    }
    void trace_top(const Cand& c, std::vector<int>& out) const {
        const int si = split_idx_[c.ci];
        if (c.split == kSplitStraight) { trace_cell(d_ss00_[si], out); trace_cell(d_ss11_[si], out); }
        else { trace_cell(d_ss01_[si], out); trace_cell(d_ss10_[si], out); }
    }

    int cover_of(int l) const { return cover_stamp_[l] == cover_epoch_ ? cover_count_[l] : 0; }
    void bump_cover(int l) { if (cover_stamp_[l] != cover_epoch_) { cover_stamp_[l] = cover_epoch_; cover_count_[l] = 0; } ++cover_count_[l]; }

    int n_;
    TreeQueries& q1_;
    TreeQueries& q2_;
    const TreeInfo& T1_;
    const TreeInfo& T2_;
    int t1_off_, t2_off_, N1_ = 0, N2_ = 0;
    bool feasible_ = false, found_improving_ = false;
    std::size_t cells_ = 0;
    std::vector<double> edge_w1_, edge_w2_;
    std::vector<int> left1_, right1_, label1_, post1_, left2_, right2_, label2_, post2_;
    std::vector<char> leaf1_, leaf2_;
    std::vector<int> cu_, cv_;
    std::vector<int> split_idx_;
    std::vector<int> d_su0_, d_su1_, d_sv0_, d_sv1_;
    std::vector<int> d_ss00_, d_ss11_, d_ss01_, d_ss10_;
    std::vector<float> V_;
    std::vector<unsigned char> choice_;
    std::vector<Cand> cands_;
    mutable std::vector<int> trace_stack_;
    std::vector<int> cover_count_, cover_stamp_;
    int cover_epoch_ = 0;
    double max_profit_ = 0.0;
};

// ---------------------------------------------------------------------
// Column generation
// ---------------------------------------------------------------------
static void column_generation(int n, TreeQueries& q1, TreeQueries& q2, const Params& params, TimePoint deadline, std::vector<Component>& global_pool) {
    const int t1_off = n, t2_off = n + (int)q1.info.edge_nodes.size();
    const int num_rows = n + (int)q1.info.edge_nodes.size() + (int)q2.info.edge_nodes.size();
    
    auto pricer = std::make_unique<WmastPricer>(n, q1, q2, t1_off, t2_off);
    if (!pricer->feasible()) {
        if (!params.quiet) log_out() << "CG: sparse pricer allocation failed; skipping CG.\n";
        return;
    }

    const std::size_t kPoolTarget = adaptive_column_budget(n, num_rows);
    const std::size_t kPoolCap = kPoolTarget + std::max<std::size_t>(1, kPoolTarget / ceil_log2_size(kPoolTarget + 1));
    const int kMaxNew = capped_int(kPoolTarget);
    int kAddPerRound = std::min<int>(kMaxNew, std::max(2048, num_rows / 8));
    const int kCoverCap = capped_int(ceil_log2_size(static_cast<std::size_t>(n) + 1));
    int kMinAge = 1;
    const double kStabAlpha = (pricer->cells() > kPoolTarget) ? 0.4 : 0.0;
    std::vector<double> stab_dual;

    std::size_t kLpCap = std::min(kPoolCap, static_cast<std::size_t>(3000));
    const std::size_t kLpTarget = std::max<std::size_t>(1, (std::size_t)(0.85 * (double)kLpCap));
    constexpr double kSupportEps = 1e-3;
    std::vector<Component> last_support;

    std::unordered_set<Component, ComponentHash> pool;
    std::vector<Component> lp_cols;
    std::vector<int> col_age;
    for (const Component& c : g_best_forest) if (c.size() > 1 && pool.insert(c).second) { 
        lp_cols.push_back(c); 
        col_age.push_back(0); 
        global_pool.push_back(c);
    }

    if (lp_cols.empty()) {
        std::vector<double> zero(num_rows, 0.0);
        std::vector<Component> seed = pricer->price(zero, pool, deadline, kMaxNew, kCoverCap);
        for (Component& c : seed) if (pool.insert(c).second) { 
            lp_cols.push_back(std::move(c)); 
            col_age.push_back(0); 
            global_pool.push_back(lp_cols.back());
        }
    }
    if (lp_cols.empty()) { if (!params.quiet) log_out() << "CG: no branches to seed; skipping.\n"; return; }

    HighsModel model;
    build_packing_model(model, lp_cols, num_rows, n, q1, q2, t1_off, t2_off);
    std::vector<int> es;

    Highs highs;
    highs.setOptionValue("output_flag", false);
    highs.setOptionValue("log_to_console", false);
    highs.setOptionValue("presolve", "off");
    highs.setOptionValue("threads", 1);
    highs.setOptionValue("random_seed", 0);
    bool lp_ok = (highs.passModel(model) == HighsStatus::kOk);

    std::vector<HighsInt> idx;
    std::vector<double> val;
    int rounds = 0, total_priced = 0, aged = 0;
    bool converged = false;
    double conv_lp = -1.0;
    double lp_sec = 0.0, price_sec = 0.0;

    auto add_columns = [&](std::vector<Component>& priced) -> int {
        int added = 0;
        for (Component& c : priced) {
            if (pool.find(c) != pool.end()) continue;
            if (!is_valid_component(q1, q2, c)) continue;
            global_pool.push_back(c);
            if (added >= kAddPerRound) continue;
            column_edges(c, q1, q2, t1_off, t2_off, es);
            idx.assign(es.begin(), es.end());
            val.assign(idx.size(), 1.0);
            if (highs.addCol(-double(std::max(0, c.size() - 1)), 0.0, 1.0, (HighsInt)idx.size(), idx.data(), val.data()) == HighsStatus::kOk) {
                pool.insert(c);
                lp_cols.push_back(c);
                col_age.push_back(0);
                ++added;
            }
        }
        return added;
    };

    const double cg_loop_floor = std::max(1.5, 0.05 * params.time_limit);

    for (int round = 0; lp_ok; ++round) {
        if (seconds_left(deadline) < cg_loop_floor) break;
        for (int& a : col_age) ++a;
        highs.setOptionValue("time_limit", seconds_left(deadline));
        TimePoint tlp = Clock::now();
        highs.run();
        lp_sec += std::chrono::duration<double>(Clock::now() - tlp).count();
        if (highs.getModelStatus() != HighsModelStatus::kOptimal) break;
        HighsSolution sol = highs.getSolution();
        if (!sol.dual_valid || (int)sol.row_dual.size() < num_rows) break;
        const double lp_obj = highs.getInfo().objective_function_value;

        if ((int)sol.col_value.size() == (int)lp_cols.size()) {
            last_support.clear();
            for (int i = 0; i < (int)lp_cols.size(); ++i)
                if (sol.col_value[i] > kSupportEps) last_support.push_back(lp_cols[i]);
        }

        if (round % 8 == 0) {
            std::vector<Component> r = greedy_round(n, lp_cols, q1, q2, &sol.col_value);
            if (forest_is_valid(n, q1, q2, r)) set_best_forest(r);
        }

        if (lp_cols.size() > kLpCap) {
            HighsBasis basis = highs.getBasis();
            const std::vector<double>& rc = sol.col_dual;
            if (basis.col_status.size() == lp_cols.size() && rc.size() == lp_cols.size()) {
                std::vector<int> cand;
                cand.reserve(lp_cols.size());
                for (int i = 0; i < (int)lp_cols.size(); ++i) {
                    HighsBasisStatus s = basis.col_status[i];
                    if ((s == HighsBasisStatus::kLower || s == HighsBasisStatus::kZero) && col_age[i] >= kMinAge) cand.push_back(i);
                }
                std::sort(cand.begin(), cand.end(), [&](int a, int b) { return rc[a] > rc[b]; });
                std::size_t want = lp_cols.size() - kLpTarget;
                if (cand.size() > want) cand.resize(want);
                if (!cand.empty()) {
                    std::sort(cand.begin(), cand.end());
                    if (highs.deleteCols((HighsInt)cand.size(), cand.data()) == HighsStatus::kOk) {
                        std::vector<char> del(lp_cols.size(), 0);
                        for (int i : cand) { del[i] = 1; pool.erase(lp_cols[i]); }
                        std::vector<Component> nc;
                        std::vector<int> na;
                        for (int i = 0; i < (int)lp_cols.size(); ++i) if (!del[i]) { nc.push_back(std::move(lp_cols[i])); na.push_back(col_age[i]); }
                        lp_cols.swap(nc);
                        col_age.swap(na);
                        aged += (int)cand.size();
                    }
                }
            }
        }

        TimePoint tpr = Clock::now();
        std::vector<Component> priced = pricer->price(sol.row_dual, pool, deadline, kAddPerRound, kCoverCap);
        bool exact_improving = pricer->found_improving();

        double max_profit = pricer->max_profit();
        double lb_frac = lp_obj - max_profit * (n / 2.0);
        int lb = (int)std::ceil(lb_frac - 1e-6);
        if (lb > g_lower_bound) g_lower_bound = lb;

        if (kStabAlpha > 0.0) {
            if (stab_dual.size() != sol.row_dual.size()) stab_dual = sol.row_dual;
            else for (std::size_t i = 0; i < stab_dual.size(); ++i)
                stab_dual[i] = kStabAlpha * stab_dual[i] + (1.0 - kStabAlpha) * sol.row_dual[i];
            std::vector<Component> p2 = pricer->price(stab_dual, pool, deadline, kAddPerRound, kCoverCap);
            priced.insert(priced.end(), std::make_move_iterator(p2.begin()), std::make_move_iterator(p2.end()));
        }
        int added = add_columns(priced);
        price_sec += std::chrono::duration<double>(Clock::now() - tpr).count();
        total_priced += added;
        ++rounds;

        if (q1.restriction_cache.size() + q1.used_edge_cache.size() > 50000) {
            q1.clear_caches();
            q2.clear_caches();
        }

        if (added == 0) {
            if (!exact_improving) { converged = true; conv_lp = lp_obj; }
            break;
        }

        if (!params.quiet && rounds % 50 == 1)
            log_out() << "CG round " << rounds << ": LP " << lp_obj << ", +" << added
                      << " cols, pool " << lp_cols.size() << ", aged " << aged << "\n";
    }

    // Baseline incumbent from the converged pool BEFORE diving. The dive's LP
    // re-solves grow with the enriched pool and can be slow at large n, so a single
    // re-solve may run into the deadline and be SIGTERM'd mid-dive; establishing the
    // no-dive incumbent first means that case can never regress below the plain
    // pipeline -- the dive only ever ADDS columns and better forests (monotonic via
    // set_best_forest). Cheap and exact when the pool is small/converged.
    if (converged && lp_ok && seconds_left(deadline) > 0.5) {
        IlpResult base = solve_master_ilp(n, lp_cols, q1, q2,
                                          std::min(seconds_left(deadline), 0.25 * params.time_limit), params.quiet);
        if (base.ok && forest_is_valid(n, q1, q2, base.forest)) set_best_forest(base.forest);
    }

    // Bounded branch-and-price (always ON). The integrality gap on converged off-by-few
    // instances is column COVERAGE: the converged pool's integer optimum is k+1 yet
    // the LP proves k, because the residual-optimal columns have reduced cost >=0 at
    // the converged duals so pricing never asks for them. Dive enriches along ONE
    // primal path; branch-and-price enriches systematically. Variable branching
    // x_i in {0,1} is complete and pricer-compatible: [1,1] forces the up-branch,
    // [0,0] forces the down-branch (the pricer may re-find component i but add_columns
    // skips it as already-in-pool, so the LP honours the fix). Each node reprices the
    // residual under the branch-perturbed duals -> generates the missing columns,
    // which feed the integral leaves AND the post-CG masters. Monotonic (set_best_forest
    // never regresses below the pre-dive baseline master), best-bound pruned against the
    // live incumbent, node/time budgeted. Up-branch first (deepens toward an integral
    // assembly fast); down-branch diversifies coverage.
    if (converged && lp_ok && pricer->feasible()) {
        const double bnp_budget = 0.70 * seconds_left(deadline);
        const TimePoint bnp_deadline =
            Clock::now() + std::chrono::duration_cast<Clock::duration>(std::chrono::duration<double>(bnp_budget));
        const long node_budget = std::max(64L, 200000L / (long)(lp_cols.size() / 64 + 1));
        long nodes = 0, bnp_priced = 0, bnp_solves = 0, bnp_int = 0;
        auto try_incumbent = [&](const HighsSolution& sol) {
            std::vector<Component> forest;
            std::vector<char> covered(n + 1, 0);
            const int lim = std::min((int)lp_cols.size(), (int)sol.col_value.size());
            for (int i = 0; i < lim; ++i)
                if (lp_cols[i].size() > 1 && sol.col_value[i] > 0.5) {
                    forest.push_back(lp_cols[i]);
                    for (int l : lp_cols[i].leaves) if (l >= 1 && l <= n) covered[l] = 1;
                }
            for (int l = 1; l <= n; ++l) if (!covered[l]) forest.emplace_back(std::vector<int>{l});
            if (forest_is_valid(n, q1, q2, forest)) set_best_forest(forest);
        };
        std::function<void()> bnp = [&]() {
            if (++nodes > node_budget) return;
            if (seconds_left(bnp_deadline) < 0.1 || seconds_left(deadline) < 0.8) return;
            highs.setOptionValue("time_limit", seconds_left(deadline));
            highs.run(); ++bnp_solves;
            if (highs.getModelStatus() != HighsModelStatus::kOptimal) return;
            HighsSolution sol = highs.getSolution();
            if (!sol.dual_valid || (int)sol.col_value.size() != (int)lp_cols.size()) return;
            const double lp_obj = highs.getInfo().objective_function_value;
            // LP objective == forest-size lower bound (offset n, costs -(size-1)).
            if ((int)std::ceil(lp_obj - 1e-6) >= (int)g_best_forest.size()) return;  // prune
            std::vector<Component> priced = pricer->price(sol.row_dual, pool, bnp_deadline, kAddPerRound, kCoverCap);
            bnp_priced += add_columns(priced);
            int bi = -1; double bf = 1e-4;
            for (int i = 0; i < (int)sol.col_value.size(); ++i) {
                double v = sol.col_value[i], f = std::min(v, 1.0 - v);
                if (f > bf) { bf = f; bi = i; }
            }
            if (bi < 0) { ++bnp_int; try_incumbent(sol); return; }  // integral leaf
            highs.changeColBounds((HighsInt)bi, 1.0, 1.0); bnp(); highs.changeColBounds((HighsInt)bi, 0.0, 1.0);
            if (seconds_left(bnp_deadline) < 0.1 || nodes > node_budget) return;
            highs.changeColBounds((HighsInt)bi, 0.0, 0.0); bnp(); highs.changeColBounds((HighsInt)bi, 0.0, 1.0);
        };
        bnp();
        if (!params.quiet)
            log_out() << "Branch-and-price: " << nodes << " nodes, " << bnp_solves << " LP solves, "
                      << bnp_int << " integral, +" << bnp_priced << " cols enriched, pool "
                      << lp_cols.size() << ", incumbent " << g_best_forest.size() << "\n";
    }

    pricer.reset();
    pool.clear();
    pool.rehash(0);
    col_age.clear();
    col_age.shrink_to_fit();
    stab_dual.clear();
    stab_dual.shrink_to_fit();
    idx.clear();
    idx.shrink_to_fit();
    val.clear();
    val.shrink_to_fit();
    es.clear();
    es.shrink_to_fit();
    q1.clear_caches();
    q2.clear_caches();

    if (!last_support.empty() && seconds_left(deadline) > 0.5) {
        IlpResult ilp = solve_master_ilp(n, last_support, q1, q2, 0.6 * seconds_left(deadline), params.quiet);
        if (ilp.ok && forest_is_valid(n, q1, q2, ilp.forest)) set_best_forest(ilp.forest);
        if (!params.quiet)
            log_out() << "Support master: " << last_support.size() << "/" << lp_cols.size()
                      << " cols -> " << (ilp.ok ? (long)ilp.forest.size() : -1L)
                      << " (incumbent " << g_best_forest.size() << ")\n";
    }

    double cap = converged ? seconds_left(deadline) : 0.5 * seconds_left(deadline);
    if (cap > 0.0) {
        IlpResult ilp = solve_master_ilp(n, lp_cols, q1, q2, cap, params.quiet);
        if (ilp.ok && forest_is_valid(n, q1, q2, ilp.forest)) set_best_forest(ilp.forest);
    }

    if (!params.quiet) {
        if (converged) {
            long lb = (long)std::ceil(conv_lp - 1e-6);
            log_out() << "CG: " << rounds << " rounds, " << total_priced << " cols, " << aged << " aged; converged, exact branch-LP "
                      << conv_lp << " (MAF >= " << lb << "), incumbent " << g_best_forest.size() << "\n";
        } else {
            log_out() << "CG: " << rounds << " rounds, " << total_priced << " cols, " << aged << " aged; not converged, incumbent " << g_best_forest.size() << "\n";
        }
        log_out() << "CG timing: LP " << lp_sec << "s, pricing " << price_sec << "s over " << rounds << " rounds\n";
    }
}

// ---------------------------------------------------------------------
// Monotonic greedy merge floor
// ---------------------------------------------------------------------
struct EdgeOwners { std::vector<int> tree1, tree2; };
static EdgeOwners build_edge_owners(const std::vector<Component>& forest, TreeQueries& q1, TreeQueries& q2) {
    EdgeOwners o;
    o.tree1.assign(q1.info.edge_nodes.size(), -1);
    o.tree2.assign(q2.info.edge_nodes.size(), -1);
    for (int i = 0; i < (int)forest.size(); ++i) {
        for (int u : q1.used_edge_nodes(forest[i])) { int r = q1.info.edge_row[u]; if (r >= 0) o.tree1[r] = i; }
        for (int u : q2.used_edge_nodes(forest[i])) { int r = q2.info.edge_row[u]; if (r >= 0) o.tree2[r] = i; }
    }
    return o;
}

static std::vector<Component> greedy_merge_improvement(
    int n, TreeQueries& q1, TreeQueries& q2, const std::vector<Component>& input, TimePoint deadline,
    std::mt19937* rng = nullptr
) {
    if (!forest_is_valid(n, q1, q2, input)) return input;
    std::vector<Component> forest = input;
    std::vector<char> reserved1(q1.info.edge_nodes.size(), 0), reserved2(q2.info.edge_nodes.size(), 0);
    while (seconds_left(deadline) > 0.05) {
        EdgeOwners owners = build_edge_owners(forest, q1, q2);
        const int full = (int)forest.size();
        std::vector<int> order(full);
        std::iota(order.begin(), order.end(), 0);
        if (rng) std::shuffle(order.begin(), order.end(), *rng);
        else std::sort(order.begin(), order.end(), [&](int a, int b) {
            if (forest[a].min_leaf() != forest[b].min_leaf()) return forest[a].min_leaf() < forest[b].min_leaf();
            return forest[a].leaves < forest[b].leaves;
        });
        std::fill(reserved1.begin(), reserved1.end(), 0);
        std::fill(reserved2.begin(), reserved2.end(), 0);
        std::vector<char> matched(full, 0);
        std::vector<Component> merges;
        const int window = std::min(full, std::max(1, capped_int(std::ceil(std::sqrt(static_cast<double>(full))))));
        long long scans = 0;
        bool any = false;

        auto fits = [&](const std::vector<int>& u1, const std::vector<int>& u2, int i, int j) {
            for (int u : u1) { int r = q1.info.edge_row[u]; if (r < 0) continue; int o = owners.tree1[r]; if ((o >= 0 && o != i && o != j) || reserved1[r]) return false; }
            for (int u : u2) { int r = q2.info.edge_row[u]; if (r < 0) continue; int o = owners.tree2[r]; if ((o >= 0 && o != i && o != j) || reserved2[r]) return false; }
            return true;
        };

        for (int oi = 0; oi < full; ++oi) {
            if ((oi & 255) == 0) check_time(deadline);
            int i = order[oi];
            if (matched[i]) continue;
            int best_j = -1, best_size = -1;
            Component best_merged;
            const std::vector<int>* bu1 = nullptr;
            const std::vector<int>* bu2 = nullptr;
            for (int oj = oi + 1; oj < full && oj <= oi + window; ++oj) {
                if ((++scans & 1023LL) == 0) check_time(deadline);
                int j = order[oj];
                if (matched[j]) continue;
                Component merged = component_union(forest[i], forest[j]);
                if (!is_valid_component(q1, q2, merged)) continue;
                const auto& u1 = q1.used_edge_nodes(merged);
                const auto& u2 = q2.used_edge_nodes(merged);
                if (!fits(u1, u2, i, j)) continue;
                if (merged.size() > best_size) { best_size = merged.size(); best_j = j; best_merged = merged; bu1 = &u1; bu2 = &u2; }
            }
            if (best_j < 0) continue;
            for (int u : *bu1) { int r = q1.info.edge_row[u]; if (r >= 0) reserved1[r] = 1; }
            for (int u : *bu2) { int r = q2.info.edge_row[u]; if (r >= 0) reserved2[r] = 1; }
            matched[i] = matched[best_j] = 1;
            merges.push_back(std::move(best_merged));
            any = true;
        }

        if (!any) break;
        std::vector<Component> next;
        next.reserve(full);
        for (int idx = 0; idx < full; ++idx) if (!matched[idx]) next.push_back(std::move(forest[idx]));
        for (Component& m : merges) next.push_back(std::move(m));
        if (!forest_is_valid(n, q1, q2, next)) break;
        forest = std::move(next);
        set_best_forest(forest);
    }
    return forest;
}

// ---------------------------------------------------------------------
// Cherry-picking constructive multi-start
// ---------------------------------------------------------------------
static std::vector<Component> multistart_cherry_pick(
    int n, TreeQueries& q1, TreeQueries& q2, TimePoint deadline, int max_pool_add, bool quiet, int seed_offset = 0
) {
    const TreeInfo& T1 = q1.info;
    const TreeInfo& T2 = q2.info;
    std::vector<int> tplLeaf1(n + 1, -1), tplLeaf2(n + 1, -1);
    CherryMutForest tpl1, tpl2;
    cherry_build_template(T1, tpl1, tplLeaf1);
    cherry_build_template(T2, tpl2, tplLeaf2);
    const int maxblk = 2 * n + 2;
    std::vector<std::vector<int>> blockleaves(maxblk);
    std::vector<char> blockalive(maxblk, 0);
    std::vector<int> blockLeaf1(maxblk, -1), blockLeaf2(maxblk, -1);

    CherryMutForest f1, f2;
    std::vector<int> wl;
    std::mt19937 rng(0xC4E55Eu ^ (std::uint32_t)n * 2654435761u ^ (std::uint32_t)seed_offset);
    std::vector<Component> harvested;
    std::unordered_set<Component, ComponentHash> seen;

    int runs = 0;
    std::size_t best_local = std::numeric_limits<std::size_t>::max();

    while (harvested.size() < static_cast<std::size_t>(max_pool_add) && seconds_left(deadline) > 0.05) {
        f1 = tpl1; f2 = tpl2;
        for (int L = 1; L <= n; ++L) {
            blockLeaf1[L] = tplLeaf1[L]; blockLeaf2[L] = tplLeaf2[L];
            blockleaves[L].assign(1, L); blockalive[L] = 1;
        }
        for (int b = n + 1; b < maxblk; ++b) { blockleaves[b].clear(); blockalive[b] = 0; }
        int next_block = n + 1;

        const bool randomized = (runs > 0);
        wl.clear();
        for (int u = 0; u < (int)f1.par.size(); ++u)
            if (f1.alive[u] && !f1.leaf[u] && f1.c0[u] >= 0 && f1.c1[u] >= 0 && f1.leaf[f1.c0[u]] && f1.leaf[f1.c1[u]]) wl.push_back(u);
        if (randomized) std::shuffle(wl.begin(), wl.end(), rng);

        std::vector<Component> components;
        long guard = 0;
        while (!wl.empty()) {
            if ((++guard & 4095) == 0 && seconds_left(deadline) <= 0.02) break;
            const int u = wl.back(); wl.pop_back();
            if (!(f1.alive[u] && !f1.leaf[u])) continue;
            const int la = f1.c0[u], lb = f1.c1[u];
            if (la < 0 || lb < 0 || !f1.alive[la] || !f1.alive[lb] || !f1.leaf[la] || !f1.leaf[lb]) continue;
            const int a = f1.blk[la], b = f1.blk[lb];
            const int na = blockLeaf2[a], nb = blockLeaf2[b];
            const int pa = f2.par[na], pb = f2.par[nb];
            if (pa >= 0 && pa == pb) {
                const int c = next_block++;
                blockalive[a] = blockalive[b] = 0; blockalive[c] = 1;
                std::vector<int>& cl = blockleaves[c];
                cl = std::move(blockleaves[a]);
                cl.insert(cl.end(), blockleaves[b].begin(), blockleaves[b].end());
                blockleaves[b].clear();
                f1.alive[la] = f1.alive[lb] = 0;
                f1.leaf[u] = 1; f1.c0[u] = f1.c1[u] = -1; f1.blk[u] = c; blockLeaf1[c] = u;
                f2.alive[na] = f2.alive[nb] = 0;
                f2.leaf[pa] = 1; f2.c0[pa] = f2.c1[pa] = -1; f2.blk[pa] = c; blockLeaf2[c] = pa;
                if (f1.par[u] >= 0) wl.push_back(f1.par[u]);
            } else {
                const int sa = (int)blockleaves[a].size(), sb = (int)blockleaves[b].size();
                int cut;
                if (!randomized) cut = (sa <= sb) ? a : b;
                else { int r = (int)(rng() % 100); cut = (r < 55) ? ((sa <= sb) ? a : b) : (r < 82 ? ((sa <= sb) ? b : a) : ((rng() & 1) ? a : b)); }
                cherry_cut_node(f1, blockLeaf1[cut], &wl);
                cherry_cut_node(f2, blockLeaf2[cut], nullptr);
                components.emplace_back(std::move(blockleaves[cut]));
                blockalive[cut] = 0;
            }
        }
        for (int b = 1; b < next_block; ++b) if (blockalive[b]) components.emplace_back(std::move(blockleaves[b]));
        ++runs;

        for (const Component& c : components) {
            if (harvested.size() >= static_cast<std::size_t>(max_pool_add)) break;
            if (c.size() < 2 || !seen.insert(c).second) continue;
            if (is_valid_component(q1, q2, c)) harvested.push_back(c);
        }
        if (components.size() < best_local && (g_best_forest.empty() || components.size() < g_best_forest.size())) {
            if (forest_is_valid(n, q1, q2, components)) { best_local = components.size(); set_best_forest(components); }
        }
    }
    if (!quiet)
        log_out() << "Cherry multi-start: " << runs << " runs, harvested " << harvested.size()
                  << " blocks; best constructed " << (best_local == std::numeric_limits<std::size_t>::max() ? 0 : best_local)
                  << " (incumbent " << g_best_forest.size() << ")\n";
    return harvested;
}

// ---------------------------------------------------------------------
// Multi-Start Greedy Set Packing (Endgame Heuristic)
// ---------------------------------------------------------------------
static void multi_start_packing(
    int n, 
    std::vector<Component>& global_pool, 
    TreeQueries& q1, TreeQueries& q2, 
    TimePoint deadline,
    bool quiet
) {
    if (global_pool.empty()) return;

    std::vector<Component> pool;
    pool.reserve(global_pool.size());
    std::unordered_set<Component, ComponentHash> seen;
    for (auto& c : global_pool) {
        if (c.size() > 1 && seen.insert(c).second && is_valid_component(q1, q2, c)) {
            pool.push_back(c);
        }
    }
    if (pool.empty()) return;

    if (pool.size() > 150000) {
        std::sort(pool.begin(), pool.end(), [](const Component& a, const Component& b) {
            return a.size() > b.size();
        });
        pool.resize(100000);
    }

    int m = (int)pool.size();
    if (!quiet) log_out() << "Multi-start packing pool size: " << m << "\n";

    const int E1 = (int)q1.info.edge_nodes.size();
    const int E2 = (int)q2.info.edge_nodes.size();

    // Flatten the leaf- and edge-incidence of every pool column into CSR arrays
    // ONCE. The inner restart loop is then a tight scan over plain int arrays,
    // avoiding the per-column Component hashing through used_edge_nodes() that
    // dominated each restart. The search (column order, RNG, acceptance test) is
    // bit-identical to before, so in a fixed budget we simply run more restarts.
    std::vector<int> loff(m + 1, 0), e1off(m + 1, 0), e2off(m + 1, 0);
    std::vector<double> scores(m, 0.0);
    for (int i = 0; i < m; ++i) {
        int sz = (int)pool[i].leaves.size();
        int c1 = 0; for (int u : q1.used_edge_nodes(pool[i])) if (q1.info.edge_row[u] >= 0) ++c1;
        int c2 = 0; for (int u : q2.used_edge_nodes(pool[i])) if (q2.info.edge_row[u] >= 0) ++c2;
        loff[i + 1] = sz; e1off[i + 1] = c1; e2off[i + 1] = c2;
        scores[i] = 1000.0 * sz - 1.0 * (c1 + c2);
    }
    for (int i = 0; i < m; ++i) { loff[i + 1] += loff[i]; e1off[i + 1] += e1off[i]; e2off[i + 1] += e2off[i]; }
    std::vector<int> lidx(loff[m]), e1idx(e1off[m]), e2idx(e2off[m]);
    for (int i = 0; i < m; ++i) {
        int p = loff[i]; for (int l : pool[i].leaves) lidx[p++] = l;
        int p1 = e1off[i]; for (int u : q1.used_edge_nodes(pool[i])) { int r = q1.info.edge_row[u]; if (r >= 0) e1idx[p1++] = r; }
        int p2 = e2off[i]; for (int u : q2.used_edge_nodes(pool[i])) { int r = q2.info.edge_row[u]; if (r >= 0) e2idx[p2++] = r; }
    }
    // The restart loop below runs entirely off the flattened CSR arrays, so the
    // per-component restriction/edge caches populated during dedup and flatten
    // (which can hold hundreds of MB for a large pool) are no longer needed. Free
    // them before the compact master builds its model.
    q1.clear_caches();
    q2.clear_caches();

    std::vector<int> indices(m);
    std::iota(indices.begin(), indices.end(), 0);
    std::mt19937 rng(1337);
    std::sort(indices.begin(), indices.end(), [&](int a, int b) {
        return scores[a] > scores[b];
    });

    int iter = 0;
    int stalled = 0;
    const int stall_limit = std::min(4096, std::max(512, m / 8));
    size_t best_sz = g_best_forest.empty() ? n : g_best_forest.size();

    // A compact exact master over the best-scored columns often closes the last
    // few packing conflicts that random greedy restarts keep missing. Keep it
    // deliberately filtered and time-capped; the full pool remains available to
    // the restart heuristic below.
    if (seconds_left(deadline) > 20.0) {
        const int keep = std::min(m, std::max(2000, std::min(10000, 2 * n)));
        std::vector<Component> master_pool;
        master_pool.reserve(keep + g_best_forest.size());
        std::unordered_set<Component, ComponentHash> master_seen;
        for (const Component& c : g_best_forest)
            if (c.size() > 1 && master_seen.insert(c).second) master_pool.push_back(c);
        for (int pos = 0; pos < keep; ++pos) {
            const Component& c = pool[indices[pos]];
            if (master_seen.insert(c).second) master_pool.push_back(c);
        }
        IlpResult ilp = solve_master_ilp(n, master_pool, q1, q2,
                                         std::min(10.0, 0.08 * seconds_left(deadline)), quiet);
        if (ilp.ok && forest_is_valid(n, q1, q2, ilp.forest)) {
            set_best_forest(ilp.forest);
            best_sz = g_best_forest.empty() ? n : g_best_forest.size();
        }
    }

    // Scratch buffers reused across restarts (cleared, never reallocated).
    std::vector<char> leaf_used(n + 1, 0), used1(E1, 0), used2(E2, 0);
    std::vector<int> chosen;
    chosen.reserve(best_sz);

    while (seconds_left(deadline) > 0.2 && stalled < stall_limit) {
        iter++;

        if (iter == 1) {
            // strictly greedy
        } else if (iter % 20 == 0) {
            std::shuffle(indices.begin(), indices.end(), rng);
        } else {
            int top = m / 5;
            if (top > 0) {
                for (int i = 0; i < top / 2; ++i) {
                    int u = rng() % top;
                    int v = rng() % m;
                    std::swap(indices[u], indices[v]);
                }
            }
        }

        std::fill(leaf_used.begin(), leaf_used.end(), 0);
        std::fill(used1.begin(), used1.end(), 0);
        std::fill(used2.begin(), used2.end(), 0);
        chosen.clear();
        int covered = 0;

        for (int idx : indices) {
            bool ok = true;
            for (int p = loff[idx]; p < loff[idx + 1]; ++p) if (leaf_used[lidx[p]]) { ok = false; break; }
            if (!ok) continue;
            for (int p = e1off[idx]; p < e1off[idx + 1]; ++p) if (used1[e1idx[p]]) { ok = false; break; }
            if (!ok) continue;
            for (int p = e2off[idx]; p < e2off[idx + 1]; ++p) if (used2[e2idx[p]]) { ok = false; break; }
            if (!ok) continue;

            for (int p = loff[idx]; p < loff[idx + 1]; ++p) { leaf_used[lidx[p]] = 1; ++covered; }
            for (int p = e1off[idx]; p < e1off[idx + 1]; ++p) used1[e1idx[p]] = 1;
            for (int p = e2off[idx]; p < e2off[idx + 1]; ++p) used2[e2idx[p]] = 1;
            chosen.push_back(idx);
        }

        // Each uncovered leaf becomes its own singleton component.
        size_t fsize = chosen.size() + (size_t)(n - covered);
        if (fsize < best_sz) {
            best_sz = fsize;
            stalled = 0;
            std::vector<Component> forest;
            forest.reserve(fsize);
            for (int idx : chosen) forest.push_back(pool[idx]);
            for (int l = 1; l <= n; ++l) if (!leaf_used[l]) forest.emplace_back(std::vector<int>{l});
            set_best_forest(forest);
            if (!quiet) log_out() << "Packing iter " << iter << ": new best " << best_sz << "\n";
        } else {
            ++stalled;
        }

        if ((iter & 511) == 0) check_time(deadline);
    }
    if (!quiet) log_out() << "Multi-start packing: " << iter << " restarts, best " << best_sz
                          << (stalled >= stall_limit ? " (stalled)\n" : "\n");
}

// ---------------------------------------------------------------------
// Solve driver
// ---------------------------------------------------------------------
namespace astdp { enum : unsigned char { C_NONE, C_LEAF, C_UL, C_UR, C_VL, C_VR, C_SS, C_SC }; }

static void harvest_agreement_subtrees(const TreeInfo& T1, const TreeInfo& T2,
                                       size_t cell_cap, int max_harvest,
                                       TimePoint deadline, std::vector<Component>& out,
                                       const std::vector<double>& leaf_w = {}) {
    const int N1 = (int)T1.nodes.size(), N2 = (int)T2.nodes.size();
    auto build_post = [&](const TreeInfo& T, std::vector<int>& post) {
        post.clear(); post.reserve(T.nodes.size());
        std::vector<int> st{T.root};
        while (!st.empty()) { int u = st.back(); st.pop_back(); post.push_back(u);
            if (!T.nodes[u].is_leaf) { st.push_back(T.nodes[u].left); st.push_back(T.nodes[u].right); } }
        std::reverse(post.begin(), post.end());
    };
    std::vector<int> post1, post2; build_post(T1, post1); build_post(T2, post2);
    std::vector<int> rank2(N2, 0);
    for (int i = 0; i < N2; ++i) rank2[post2[i]] = i;
    std::vector<int> rank1(N1, 0);
    for (int i = 0; i < N1; ++i) rank1[post1[i]] = i;

    // Cell keys rank1(u)*N2 + rank2(v), generated in globally increasing order
    // (post1 order outer, increasing rank2 inner) so no sort is needed and the
    // DP can be filled in a single forward pass.
    std::vector<long long> keys;
    try {
        std::vector<std::vector<int>> S(N1);
        for (int u : post1) {
            if (T1.nodes[u].is_leaf) {
                int l = T1.nodes[u].label, v = T2.leaf_node[l];
                for (int cur = v; cur >= 0; cur = T2.nodes[cur].parent) S[u].push_back(rank2[cur]);
            } else {
                int a = T1.nodes[u].left, b = T1.nodes[u].right;
                S[u].reserve(S[a].size() + S[b].size());
                std::set_union(S[a].begin(), S[a].end(), S[b].begin(), S[b].end(), std::back_inserter(S[u]));
                std::vector<int>().swap(S[a]); std::vector<int>().swap(S[b]);
            }
            long long base = (long long)rank1[u] * N2;
            for (int rv : S[u]) { keys.push_back(base + rv); if (keys.size() > cell_cap) return; }
        }
    } catch (const std::bad_alloc&) { return; }
    const int M = (int)keys.size();
    if (M == 0) return;

    auto look = [&](int u, int v) -> int {
        long long k = (long long)rank1[u] * N2 + rank2[v];
        auto it = std::lower_bound(keys.begin(), keys.end(), k);
        return (it != keys.end() && *it == k) ? (int)(it - keys.begin()) : -1;
    };
    std::vector<float> Vv; std::vector<unsigned char> ch;
    try { Vv.assign(M, 0.0f); ch.assign(M, astdp::C_NONE); }
    catch (const std::bad_alloc&) { return; }
    const bool weighted = !leaf_w.empty();

    try {
        for (int i = 0; i < M; ++i) {
            int u = post1[(int)(keys[i] / N2)], v = post2[(int)(keys[i] % N2)];
            bool ul = T1.nodes[u].is_leaf, vl = T2.nodes[v].is_leaf;
            float best = 0.0f; unsigned char bc = astdp::C_NONE;
            if (ul && vl) { best = weighted ? (float)leaf_w[T1.nodes[u].label] : 1.0f; bc = astdp::C_LEAF; }
            else {
                auto dep = [&](int c) -> float { return c >= 0 ? Vv[c] : 0.0f; };
                if (!ul) {
                    float a = dep(look(T1.nodes[u].left, v)); if (a > best) { best = a; bc = astdp::C_UL; }
                    float b = dep(look(T1.nodes[u].right, v)); if (b > best) { best = b; bc = astdp::C_UR; }
                }
                if (!vl) {
                    float a = dep(look(u, T2.nodes[v].left)); if (a > best) { best = a; bc = astdp::C_VL; }
                    float b = dep(look(u, T2.nodes[v].right)); if (b > best) { best = b; bc = astdp::C_VR; }
                }
                if (!ul && !vl) {
                    int lu = T1.nodes[u].left, ru = T1.nodes[u].right, lv = T2.nodes[v].left, rv = T2.nodes[v].right;
                    float s = dep(look(lu, lv)) + dep(look(ru, rv)); if (s > best) { best = s; bc = astdp::C_SS; }
                    float c = dep(look(lu, rv)) + dep(look(ru, lv)); if (c > best) { best = c; bc = astdp::C_SC; }
                }
            }
            Vv[i] = best; ch[i] = bc;
            if ((i & 131071) == 0) check_time(deadline);
        }
    } catch (const TimeBudgetExceeded&) { return; }

    std::vector<int> cand;
    for (int i = 0; i < M; ++i) if ((ch[i] == astdp::C_SS || ch[i] == astdp::C_SC) && Vv[i] >= 1.5f) cand.push_back(i);
    std::sort(cand.begin(), cand.end(), [&](int a, int b) { return Vv[a] > Vv[b]; });

    std::unordered_set<Component, ComponentHash> seen;
    std::vector<int> stk, leaves;
    try {
        for (int idx : cand) {
            if ((int)out.size() >= max_harvest) break;
            leaves.clear(); stk.clear(); stk.push_back(idx);
            while (!stk.empty()) {
                int i = stk.back(); stk.pop_back(); if (i < 0) continue;
                int u = post1[(int)(keys[i] / N2)], v = post2[(int)(keys[i] % N2)];
                switch (ch[i]) {
                    case astdp::C_LEAF: leaves.push_back(T1.nodes[u].label); break;
                    case astdp::C_UL: stk.push_back(look(T1.nodes[u].left, v)); break;
                    case astdp::C_UR: stk.push_back(look(T1.nodes[u].right, v)); break;
                    case astdp::C_VL: stk.push_back(look(u, T2.nodes[v].left)); break;
                    case astdp::C_VR: stk.push_back(look(u, T2.nodes[v].right)); break;
                    case astdp::C_SS: stk.push_back(look(T1.nodes[u].left, T2.nodes[v].left));
                                      stk.push_back(look(T1.nodes[u].right, T2.nodes[v].right)); break;
                    case astdp::C_SC: stk.push_back(look(T1.nodes[u].left, T2.nodes[v].right));
                                      stk.push_back(look(T1.nodes[u].right, T2.nodes[v].left)); break;
                    default: break;
                }
            }
            if ((int)leaves.size() < 2) continue;
            Component c(leaves);
            if (seen.insert(c).second) out.push_back(std::move(c));
            if ((out.size() & 2047) == 0) check_time(deadline);
        }
    } catch (const TimeBudgetExceeded&) {}
}

static void solve(int n, TreeQueries& q1, TreeQueries& q2, const Params& params, TimePoint deadline) {
    std::vector<Component> global_pool;
    try {
        g_lower_bound = 1;
        for (const Component& c : g_seed_chains) global_pool.push_back(c);
        // 1. Fast greedy-merge floor, seeded from whole chains (kept intact)
        std::vector<Component> floor = greedy_merge_improvement(n, q1, q2, seed_forest_impl(n, g_seed_chains), deadline);
        if (forest_is_valid(n, q1, q2, floor)) {
            set_best_forest(floor);
            for(const auto& c : floor) if(c.size() > 1) global_pool.push_back(c);
        }

        // 1b. MAST harvest (grafted from minimal_hitting_set.cpp): a fast sparse
        // rooted-MAST DP that yields large valid agreement subtrees. It seeds CG
        // and, critically, the packing endgame -- on large instances where CG
        // cannot converge in the budget this supplies the big blocks qwen's
        // cherry harvester misses, which is exactly where qwen was collapsing.
        {
            std::vector<Component> ast;
            harvest_agreement_subtrees(q1.info, q2.info, 40000000, 400000, deadline, ast);
            for (const auto& c : ast) if (c.size() > 1) global_pool.push_back(c);
        }
        q1.clear_caches(); q2.clear_caches();

        if ((int)g_best_forest.size() <= g_lower_bound) return;

        // 2. Edge column generation (full deadline). The harvested big blocks are
        // already in global_pool, so they seed CG and -- best-kept-only -- can only
        // help the packing endgame; they never steal branch-and-price time.
        if (seconds_left(deadline) > std::max(2.0, 0.05 * params.time_limit)) {
            column_generation(n, q1, q2, params, deadline, global_pool);
        }
        q1.clear_caches(); q2.clear_caches();

        if ((int)g_best_forest.size() <= g_lower_bound) return;

        // 3. Cherry-picking constructive multi-start. We keep harvesting columns
        //    as long as cherry keeps improving the incumbent; the moment a full
        //    iteration yields no improvement we stop and hand the rest of the
        //    budget to the global-pool packing endgame (step 5), which draws on a
        //    strictly richer column set than cherry constructs on its own.
        int seed_offset = 0;
        std::size_t prev_best = g_best_forest.size();
        while (seconds_left(deadline) > 2.0 && (int)g_best_forest.size() > g_lower_bound) {
            TimePoint iter_deadline = Clock::now() + std::chrono::duration_cast<Clock::duration>(std::chrono::duration<double>(0.75 * seconds_left(deadline)));
            const int rows = static_cast<int>(q1.info.edge_nodes.size() + q2.info.edge_nodes.size());
            int cap = capped_int(adaptive_column_budget(n, rows));
            std::vector<Component> harvested = multistart_cherry_pick(n, q1, q2, iter_deadline, cap, params.quiet, seed_offset++);
            for(const auto& c : harvested) global_pool.push_back(c);

            for (const Component& c : g_best_forest) if (c.size() > 1) global_pool.push_back(c);

            if (!harvested.empty() && seconds_left(deadline) > 1.0) {
                std::vector<Component> pool = harvested;
                for (const Component& c : g_best_forest) if (c.size() > 1) pool.push_back(c);
                if (pool.size() <= 20000) {
                    IlpResult ilp = solve_master_ilp(n, pool, q1, q2,
                                                     std::min(8.0, 0.25 * seconds_left(deadline)), params.quiet);
                    if (ilp.ok && forest_is_valid(n, q1, q2, ilp.forest)) set_best_forest(ilp.forest);
                }
            }
            if (g_best_forest.size() >= prev_best) break;  // stalled: hand off to packing
            prev_best = g_best_forest.size();
        }
        q1.clear_caches(); q2.clear_caches();

        if ((int)g_best_forest.size() <= g_lower_bound) return;

        // 4. Final merge polish
        if (seconds_left(deadline) > 0.05) {
            std::vector<Component> merged = greedy_merge_improvement(n, q1, q2, g_best_forest, deadline);
            if (forest_is_valid(n, q1, q2, merged)) set_best_forest(merged);
        }

        // 5. Global Multi-Start Packing Endgame
        for (const Component& c : g_best_forest) if (c.size() > 1) global_pool.push_back(c);
        if (seconds_left(deadline) > 0.5 && !global_pool.empty()) {
            multi_start_packing(n, global_pool, q1, q2, deadline, params.quiet);
        }

    } catch (const TimeBudgetExceeded&) {
        if (!params.quiet) log_out() << "Compute deadline reached.\n";
    }
}

static void solve_multi_tree(
    int n, const std::vector<TreeQueries*>& qs, const Params& params, TimePoint deadline
) {
    try {
        std::vector<Component> floor = greedy_merge_improvement_all(n, qs, singleton_forest(n), deadline);
        if (forest_is_valid_all(n, qs, floor)) set_best_forest(floor);

        if (n <= 22 && seconds_left(deadline) > 0.05) {
            TimePoint enum_deadline =
                Clock::now() + std::chrono::duration_cast<Clock::duration>(
                    std::chrono::duration<double>(std::max(0.01, 0.45 * seconds_left(deadline))));
            std::vector<Component> cols = enumerate_multi_tree_columns(n, qs, enum_deadline);
            if (!params.quiet)
                log_out() << "Multi-tree exact pool: " << cols.size() << " common components\n";
            if (!cols.empty() && seconds_left(deadline) > 0.05) {
                IlpResult ilp = solve_master_ilp_all(n, cols, qs, seconds_left(deadline), params.quiet);
                if (ilp.ok && forest_is_valid_all(n, qs, ilp.forest)) set_best_forest(ilp.forest);
            }
        }

        if (seconds_left(deadline) > 0.05) {
            std::vector<Component> merged = greedy_merge_improvement_all(n, qs, g_best_forest, deadline);
            if (forest_is_valid_all(n, qs, merged)) set_best_forest(merged);
        }
    } catch (const TimeBudgetExceeded&) {
        if (!params.quiet) log_out() << "Multi-tree compute deadline reached.\n";
    }
}

// ---------------------------------------------------------------------
// Cluster decomposition
// ---------------------------------------------------------------------
static const int RHO_MARK = std::numeric_limits<int>::min();
static constexpr double DECOMP_WORK_EXP = 2.0;
static int g_decomp_rep_counter = 0;
static std::uint64_t decomp_splitmix(std::uint64_t x) {
    x ^= x >> 30; x *= 0xbf58476d1ce4e5b9ULL;
    x ^= x >> 27; x *= 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}

static std::vector<std::uint64_t> decomp_node_hashes(const TreeInfo& t, const std::vector<std::uint64_t>& leafval) {
    std::vector<std::uint64_t> h(t.nodes.size(), 0ULL);
    std::vector<int> order, st{t.root};
    order.reserve(t.nodes.size());
    while (!st.empty()) {
        int u = st.back(); st.pop_back();
        order.push_back(u);
        if (!t.nodes[u].is_leaf) { st.push_back(t.nodes[u].left); st.push_back(t.nodes[u].right); }
    }
    for (int i = (int)order.size() - 1; i >= 0; --i) {
        int u = order[i];
        h[u] = t.nodes[u].is_leaf ? leafval[t.nodes[u].label] : (h[t.nodes[u].left] ^ h[t.nodes[u].right]);
    }
    return h;
}

struct DecompCtx {
    const TreeInfo& t1;
    const TreeInfo& t2;
    std::vector<std::uint64_t> h1, h2;
    std::unordered_map<std::uint64_t, int> node_of_hash2;
    Params params;
    TimePoint global_deadline;
    double remaining_work = 0.0;
};

static std::vector<std::pair<int, int>> decomp_find_clusters(const DecompCtx& ctx, int node1) {
    std::vector<std::pair<int, int>> out;
    if (ctx.t1.nodes[node1].is_leaf) return out;
    std::vector<int> st{ctx.t1.nodes[node1].left, ctx.t1.nodes[node1].right};
    while (!st.empty()) {
        int u = st.back(); st.pop_back();
        if (ctx.t1.nodes[u].is_leaf) continue;
        if (ctx.t1.nodes[u].subtree_size >= 2) {
            auto it = ctx.node_of_hash2.find(ctx.h1[u]);
            if (it != ctx.node_of_hash2.end() && ctx.t2.nodes[it->second].subtree_size == ctx.t1.nodes[u].subtree_size) {
                out.push_back({u, it->second});
                continue;
            }
        }
        st.push_back(ctx.t1.nodes[u].left);
        st.push_back(ctx.t1.nodes[u].right);
    }
    return out;
}

static std::string decomp_build_newick(
    const TreeInfo& t, int node, const std::vector<std::uint64_t>& h,
    const std::unordered_map<std::uint64_t, int>& contract,
    std::unordered_map<int, int>& src2consec, std::vector<int>& inv
) {
    auto get_consec = [&](int src) {
        auto it = src2consec.find(src);
        if (it != src2consec.end()) return it->second;
        int c = (int)inv.size();
        inv.push_back(src);
        src2consec.emplace(src, c);
        return c;
    };
    std::string out;
    struct Frame { int node, stage; };
    std::vector<Frame> st{{node, 0}};
    while (!st.empty()) {
        Frame& f = st.back();
        int u = f.node;
        auto cit = contract.find(h[u]);
        bool is_rep = (cit != contract.end());
        if (is_rep || t.nodes[u].is_leaf) {
            out += std::to_string(get_consec(is_rep ? cit->second : t.nodes[u].label));
            st.pop_back();
            continue;
        }
        if (f.stage == 0) { out += '('; f.stage = 1; st.push_back({t.nodes[u].left, 0}); continue; }
        if (f.stage == 1) { out += ','; f.stage = 2; st.push_back({t.nodes[u].right, 0}); continue; }
        out += ')';
        st.pop_back();
    }
    return out;
}

static std::vector<Component> decomp_solve_subinstance(
    const std::string& nw1, const std::string& nw2, int m, Params params, TimePoint deadline
) {
    TreeInfo t1 = NewickParser(nw1).parse(m);
    TreeInfo t2 = NewickParser(nw2).parse(m);
    std::vector<Component> sv_bf = std::move(g_best_forest);
    std::string sv_bo = std::move(g_best_output);
    std::vector<std::vector<int>> sv_exp = std::move(g_leaf_expansion);
    std::vector<Component> sv_forced = std::move(g_forced_components);
    TreeQueries* sv_oq = g_output_query;
    bool sv_sup = g_suppress_publish;
    std::vector<Component> sv_sc = std::move(g_seed_chains);

    std::vector<Component> result;
    try {
        g_best_forest.clear(); g_best_output.clear();
        g_leaf_expansion.clear(); g_forced_components.clear();
        g_suppress_publish = true;
        g_seed_chains.clear();
        params.quiet = true;
        TreeQueries q1(t1), q2(t2);
        g_output_query = &q1;
        set_best_forest(singleton_forest(m));
        solve(m, q1, q2, params, deadline);
        if (g_best_forest.empty()) set_best_forest(singleton_forest(m));
        result = g_best_forest;
    } catch (...) {
        g_best_forest = std::move(sv_bf); g_best_output = std::move(sv_bo);
        g_leaf_expansion = std::move(sv_exp); g_forced_components = std::move(sv_forced);
        g_output_query = sv_oq; g_suppress_publish = sv_sup;
        g_seed_chains = std::move(sv_sc);
        throw;
    }
    g_best_forest = std::move(sv_bf); g_best_output = std::move(sv_bo);
    g_leaf_expansion = std::move(sv_exp); g_forced_components = std::move(sv_forced);
    g_output_query = sv_oq; g_suppress_publish = sv_sup;
    g_seed_chains = std::move(sv_sc);
    return result;
}

struct DecompResult {
    std::vector<Component> forest;
    Component root;
};

static DecompResult decomp_solve(DecompCtx& ctx, int node1, int node2, bool with_rho) {
    auto clusters = decomp_find_clusters(ctx, node1);
    std::unordered_map<std::uint64_t, int> contract;
    std::unordered_map<int, Component> rep_root;
    std::vector<Component> forced;
    for (auto& c : clusters) {
        DecompResult sub = decomp_solve(ctx, c.first, c.second, true);
        for (auto& b : sub.forest) forced.push_back(std::move(b));
        int rep_src = -(++g_decomp_rep_counter);
        rep_root.emplace(rep_src, std::move(sub.root));
        contract.emplace(ctx.h1[c.first], rep_src);
    }
    std::unordered_map<int, int> src2consec;
    std::vector<int> inv{0};
    std::string nw1 = decomp_build_newick(ctx.t1, node1, ctx.h1, contract, src2consec, inv);
    std::string nw2 = decomp_build_newick(ctx.t2, node2, ctx.h2, contract, src2consec, inv);
    int m = (int)inv.size() - 1;
    if (with_rho) {
        int rho = (int)inv.size();
        inv.push_back(RHO_MARK);
        nw1 = "(" + std::to_string(rho) + "," + nw1 + ")";
        nw2 = "(" + std::to_string(rho) + "," + nw2 + ")";
        m += 1;
    }

    double work = std::pow((double)std::max(1, m), DECOMP_WORK_EXP);
    double rem_secs = seconds_left(ctx.global_deadline);
    double frac = (ctx.remaining_work > 1e-9) ? (work / ctx.remaining_work) : 1.0;
    if (frac > 1.0) frac = 1.0;
    double piece_secs = std::min(rem_secs, std::max(1.0, rem_secs * frac));
    ctx.remaining_work = std::max(0.0, ctx.remaining_work - work);
    TimePoint piece_deadline = Clock::now() + std::chrono::duration_cast<Clock::duration>(std::chrono::duration<double>(piece_secs));

    std::vector<Component> blocks = decomp_solve_subinstance(nw1, nw2, m, ctx.params, piece_deadline);

    DecompResult result;
    for (auto& b : blocks) {
        std::vector<int> leaves;
        bool is_root = false;
        for (int consec : b.leaves) {
            if (consec < 1 || consec >= (int)inv.size()) continue;
            int src = inv[consec];
            if (src == RHO_MARK) { is_root = true; continue; }
            if (src < 0) { auto it = rep_root.find(src); if (it != rep_root.end()) for (int x : it->second.leaves) leaves.push_back(x); }
            else leaves.push_back(src);
        }
        if (leaves.empty()) continue;
        Component comp(std::move(leaves));
        if (is_root && with_rho) result.root = std::move(comp);
        else result.forest.push_back(std::move(comp));
    }
    for (auto& b : forced) result.forest.push_back(std::move(b));
    return result;
}

static std::vector<Component> cluster_decompose_solve(
    const TreeInfo& t1, const TreeInfo& t2, int n, const Params& params, TimePoint deadline, bool quiet
) {
    std::vector<std::uint64_t> leafval(n + 1, 0ULL);
    for (int i = 1; i <= n; ++i) leafval[i] = decomp_splitmix((std::uint64_t)i * 0x9e3779b97f4a7c15ULL + 1);
    DecompCtx ctx{t1, t2, decomp_node_hashes(t1, leafval), decomp_node_hashes(t2, leafval), {}, params, deadline, 0.0};
    for (int u = 0; u < (int)t2.nodes.size(); ++u)
        if (!t2.nodes[u].is_leaf && t2.nodes[u].subtree_size >= 2) ctx.node_of_hash2.emplace(ctx.h2[u], u);
    
    std::vector<int> piece_sizes;
    {
        std::vector<int> st{t1.root};
        while (!st.empty()) {
            int u = st.back(); st.pop_back();
            auto cl = decomp_find_clusters(ctx, u);
            int covered = 0;
            for (auto& c : cl) { covered += t1.nodes[c.first].subtree_size; st.push_back(c.first); }
            piece_sizes.push_back(t1.nodes[u].subtree_size - covered + (int)cl.size());
        }
    }
    std::sort(piece_sizes.begin(), piece_sizes.end(), std::greater<int>());
    int max_piece = piece_sizes.empty() ? n : piece_sizes.front();

    double total_work = 0.0, max_work = 0.0;
    for (int s : piece_sizes) {
        double w = std::pow((double)std::max(1, s), DECOMP_WORK_EXP);
        total_work += w;
        if (s == max_piece) max_work = std::max(max_work, w);
    }
    const int backbone_budget = wmast_leaf_budget();
    bool concentrated = (total_work <= 1.4 * max_work);
    bool will_decompose = (max_piece <= backbone_budget && max_piece < n && concentrated);
    if (!quiet)
        log_out() << "Cluster decomposition: largest piece " << max_piece << "/" << n << ", pieces "
                  << piece_sizes.size() << ", work ratio " << (max_work > 0 ? total_work / max_work : 0.0)
                  << (will_decompose ? " -> DECOMPOSE\n" : (max_piece > backbone_budget ? " -> skip (backbone too large for memory budget)\n" : " -> skip (not concentrated)\n"));
    if (!will_decompose) return {};

    ctx.remaining_work = total_work;
    g_decomp_rep_counter = 0;
    return std::move(decomp_solve(ctx, t1.root, t2.root, false).forest);
}

// ---------------------------------------------------------------------
// CLI + main
// ---------------------------------------------------------------------
static Params parse_args(int argc, char** argv, std::string& instance_path) {
    Params p;
    instance_path = "-";
    bool path_set = false;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i] ? argv[i] : "";
        if (a.empty()) continue;
        auto val = [&](const std::string& name) {
            while (i + 1 < argc) { std::string v = argv[++i] ? argv[i] : ""; if (!v.empty()) return v; }
            throw std::runtime_error("Missing value for " + name);
        };
        if (a == "--time-limit") p.time_limit = std::stod(val(a));
        else if (a == "--disable-kernel") p.disable_kernel = true;
        else if (a == "--quiet") p.quiet = true;
        else if (a == "-h" || a == "--help") {
            std::cout << "Usage: " << argv[0] << " [--time-limit S] [--disable-kernel] [--quiet] [instance]\n";
            std::exit(0);
        } else if (a[0] != '-') { if (!path_set) { instance_path = a; path_set = true; } }
        else throw std::runtime_error("Unknown option: " + a);
    }
    if (p.time_limit <= 0.0) throw std::runtime_error("--time-limit must be positive.");
    return p;
}

int main(int argc, char** argv) {
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);
    try {
        std::string instance_path;
        Params params = parse_args(argc, argv, instance_path);
        TimePoint deadline = Clock::now() + std::chrono::duration_cast<Clock::duration>(std::chrono::duration<double>(params.time_limit));
        Instance inst = read_instance(instance_path);

        if (inst.trees.size() != 2) {
            g_leaf_expansion.clear();
            g_forced_components.clear();
            std::vector<std::unique_ptr<TreeQueries>> owned_queries;
            std::vector<TreeQueries*> qs;
            owned_queries.reserve(inst.trees.size());
            qs.reserve(inst.trees.size());
            for (const TreeInfo& t : inst.trees) {
                owned_queries.push_back(std::make_unique<TreeQueries>(t));
                qs.push_back(owned_queries.back().get());
            }
            g_output_query = qs.front();
            set_best_forest(singleton_forest(inst.n));
            install_termination_handlers();

            if (!params.quiet) {
                log_out() << "Leaves: " << inst.n << ", trees " << inst.trees.size()
                          << " (multi-tree exact set-packing path)\n";
            }

            solve_multi_tree(inst.n, qs, params, deadline);
            if (g_best_forest.empty() || !forest_is_valid_all(inst.n, qs, g_best_forest)) {
                if (!params.quiet) log_out() << "Multi-tree forest invalid; using singletons.\n";
                g_best_forest = singleton_forest(inst.n);
                g_best_output = format_forest(g_best_forest);
                publish_output(g_best_output);
            }
            if (!params.quiet) {
                log_out() << "Final solution size: " << g_best_forest.size() << "\n";
                log_out() << "Valid forest: " << (forest_is_valid_all(inst.n, qs, g_best_forest) ? "true" : "false") << "\n";
            }
            emit_final_output_and_exit(g_best_output, 0);
        }

        const int orig_n = inst.n;
        TreeInfo orig_t1 = inst.t1, orig_t2 = inst.t2;

        SubtreeReduction red = params.disable_kernel
            ? SubtreeReduction{}
            : compute_subtree_reduction(orig_t1, orig_t2, orig_n, true, true);
        const bool kernelized = red.changed;
        if (kernelized) {
            inst.t1 = NewickParser(red.newick1).parse(red.reduced_n);
            inst.t2 = NewickParser(red.newick2).parse(red.reduced_n);
            inst.n = red.reduced_n;
            g_leaf_expansion = std::move(red.expansion);
            g_forced_components = std::move(red.forced_components);
        } else {
            g_leaf_expansion.clear();
            g_forced_components.clear();
        }

        TreeQueries q1(inst.t1), q2(inst.t2);
        TreeQueries orig_q1(orig_t1), orig_q2(orig_t2);
        g_output_query = kernelized ? &orig_q1 : &q1;

        g_seed_chains.clear();
        for (const auto& ch : red.chains) {
            std::vector<int> ls;
            for (int l : ch) if (l >= 1 && l <= inst.n) ls.push_back(l);
            if (ls.size() >= 2) g_seed_chains.emplace_back(std::move(ls));
        }

        set_best_forest(seed_forest_impl(inst.n, g_seed_chains));
        install_termination_handlers();

        if (!params.quiet) {
            if (kernelized) log_out() << "Kernelization: " << orig_n << " -> " << inst.n << " leaves ("
                                      << red.subtree_contractions << " subtree, " << red.three_two_reductions
                                      << " 3-2 chains, " << red.chain_reductions << " common chains (-"
                                      << red.chain_leaves_removed << " leaves), " << g_forced_components.size() << " forced)\n";
            log_out() << "Leaves: " << inst.n << ", T1 nodes " << inst.t1.nodes.size() << ", T2 nodes " << inst.t2.nodes.size() << "\n";
        }

        if (inst.n > wmast_leaf_budget() && seconds_left(deadline) > 5.0) {
            TimePoint decomp_deadline = Clock::now() + std::chrono::duration_cast<Clock::duration>(std::chrono::duration<double>(0.85 * seconds_left(deadline)));
            std::vector<Component> decomp_forest = cluster_decompose_solve(inst.t1, inst.t2, inst.n, params, decomp_deadline, params.quiet);
            if (!decomp_forest.empty() && forest_is_valid(inst.n, q1, q2, decomp_forest)) {
                set_best_forest(decomp_forest);
                if (!params.quiet) log_out() << "Cluster decomposition forest: " << decomp_forest.size() << " (best " << g_best_forest.size() << ")\n";
            }
        }

        solve(inst.n, q1, q2, params, deadline);

        if (g_best_forest.empty()) set_best_forest(singleton_forest(inst.n));

        if (kernelized) {
            std::vector<Component> lifted = lift_forest(g_best_forest);
            if (!forest_is_valid(orig_n, orig_q1, orig_q2, lifted)) {
                log_out() << "Lifted forest invalid; using singletons.\n";
                g_leaf_expansion.clear();
                g_forced_components.clear();
                g_best_forest = singleton_forest(orig_n);
                g_best_output = format_forest(g_best_forest);
            }
        }

        if (!params.quiet) {
            log_out() << "Final solution size: " << g_best_forest.size() + g_forced_components.size()
                      << " (reduced " << g_best_forest.size() << ")\n";
            log_out() << "Valid forest: " << (forest_is_valid(inst.n, q1, q2, g_best_forest) ? "true" : "false") << "\n";
        }
        emit_final_output_and_exit(g_best_output, 0);
    } catch (const std::exception& e) {
        log_out() << "Fatal error: " << e.what() << "\n";
        if (!g_best_output.empty()) emit_final_output_and_exit(g_best_output, 0);
        return 1;
    }
}
