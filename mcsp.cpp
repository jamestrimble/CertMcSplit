#include "graph.h"

#include <algorithm>
#include <atomic>
#include <chrono>
#include <condition_variable>
#include <fstream>
#include <iostream>
#include <mutex>
#include <numeric>
#include <optional>
#include <set>
#include <string>
#include <thread>
#include <utility>
#include <vector>

#include <argp.h>

using std::vector;
using std::cout;
using std::endl;

static void fail(std::string msg) {
    std::cerr << msg << std::endl;
    exit(1);
}

/*******************************************************************************
                             Command-line arguments
*******************************************************************************/

static char doc[] = "Find a maximum common subgraph of two graphs";
static char args_doc[] = "FILENAME1 FILENAME2";
static struct argp_option options[] = {
    {"verbose", 'v', 0, 0, "Verbose output"},
    {"dimacs", 'd', 0, 0, "Read DIMACS format"},
    {"lad", 'l', 0, 0, "Read LAD format"},
    {"connected", 'c', "version", 0, "Solve MCCS (with PB model version 1, 2 or 3)"},
    {"vertex-labelled", 'V', 0, 0, "Use vertex labels"},
    {"count-solutions", 'C', 0, 0, "(For the decision problem only) count solutions"},
    {"decision", 'D', "size", 0, "Solve the decision problem"},
    {"timeout", 't', "timeout", 0, "Specify a timeout (seconds)"},
    {"opb-filename", 'o', "FILENAME", 0, "Write OPB to FILENAME (decision problem only)"},
    {"proof-filename", 'p', "FILENAME", 0, "Write proof to FILENAME (decision problem only)"},
    { 0 }
};

static struct {
    bool verbose;
    bool dimacs;
    bool lad;
    int connected;
    bool vertex_labelled;
    bool count_solutions;
    char *filename1;
    char *filename2;
    char *opb_filename;
    char *proof_filename;
    int timeout;
    int decision_size;
    int arg_num;
} arguments;

static std::atomic<bool> abort_due_to_timeout;

void set_default_arguments() {
    arguments.verbose = false;
    arguments.dimacs = false;
    arguments.lad = false;
    arguments.connected = 0;
    arguments.vertex_labelled = false;
    arguments.count_solutions = false;
    arguments.filename1 = NULL;
    arguments.filename2 = NULL;
    arguments.opb_filename = NULL;
    arguments.proof_filename = NULL;
    arguments.timeout = 0;
    arguments.decision_size = -1;
    arguments.arg_num = 0;
}

static error_t parse_opt (int key, char *arg, struct argp_state *state) {
    switch (key) {
        case 'd':
            if (arguments.lad)
                fail("The -d and -l options cannot be used together.\n");
            arguments.dimacs = true;
            break;
        case 'l':
            if (arguments.dimacs)
                fail("The -d and -l options cannot be used together.\n");
            arguments.lad = true;
            break;
        case 'v':
            arguments.verbose = true;
            break;
        case 'c':
            arguments.connected = std::stoi(arg);
            break;
        case 'V':
            arguments.vertex_labelled = true;
            break;
        case 'C':
            arguments.count_solutions = true;
            break;
        case 'D':
            arguments.decision_size = std::stoi(arg);
            break;
        case 't':
            arguments.timeout = std::stoi(arg);
            break;
        case 'o':
            arguments.opb_filename = arg;
            break;
        case 'p':
            arguments.proof_filename = arg;
            break;
        case ARGP_KEY_ARG:
            if (arguments.arg_num == 0) {
                arguments.filename1 = arg;
            } else if (arguments.arg_num == 1) {
                arguments.filename2 = arg;
            } else {
                argp_usage(state);
            }
            arguments.arg_num++;
            break;
        case ARGP_KEY_END:
            if (arguments.arg_num != 2)
                argp_usage(state);
            break;
        default: return ARGP_ERR_UNKNOWN;
    }
    return 0;
}

static struct argp argp = { options, parse_opt, args_doc, doc };

/*******************************************************************************
                             OPB and proof logging
*******************************************************************************/

struct Literal
{
    std::string var;
    bool is_negated;

    Literal() : var {}, is_negated {} { }
    Literal(std::string var, bool is_negated=false) : var(var), is_negated(is_negated) { }

    Literal operator~()
    {
        Literal new_literal = *this;
        new_literal.is_negated = !is_negated;
        return new_literal;
    }
};

struct Term
{
    int coef;
    Literal literal;

    Term() : coef {}, literal {} {}
    Term(Literal literal) : coef(1), literal(literal) {}
    Term(int coef, Literal literal) : coef(coef), literal(literal) {}

    std::string to_string()
    {
        return std::to_string(coef) + " " + (literal.is_negated ? "~" : "") + literal.var;
    }
};

Term operator*(int coef, Literal literal)
{
    return Term(coef, literal);
}

struct InequalityGeq
{
    vector<Term> lhs;
    int rhs = 0;

    InequalityGeq() {}
    InequalityGeq(vector<Term> lhs, int rhs) : lhs(lhs), rhs(rhs) {}

    InequalityGeq & set_rhs(int rhs)
    {
        this->rhs = rhs;
        return *this;
    }

    InequalityGeq & add_term(Term term)
    {
        this->lhs.push_back(term);
        return *this;
    }

    std::string to_string()
    {
        std::string result;
        for (auto term : lhs) {
            result += term.to_string() + " ";
        }

        result += ">= " + std::to_string(rhs) + ";";
        return result;
    }
};

struct OpbComment
{
    std::string text;
    vector<InequalityGeq>::size_type position;
};

class PbModel
{
    vector<InequalityGeq> constraints;
    vector<OpbComment> comments;
    vector<Term> objective;  // no objective if this is empty

public:
    int last_constraint_number()
    {
        return constraints.size();
    }

    void add_objective_term(Term term)
    {
        objective.push_back(term);
    }

    void add_constraint(InequalityGeq constraint)
    {
        constraints.push_back(constraint);
    }

    void add_equality_constraint(InequalityGeq constraint)
    {
        constraints.push_back(constraint);
        // negate lhs and rhs
        constraint.rhs = -constraint.rhs;
        for (Term & term : constraint.lhs) {
            term.coef = -term.coef;
        }
        constraints.push_back(constraint);
    }

    void add_literal_iff_conjunction(Literal lit1, Literal lit2, Literal lit3)
    {
        add_constraint({{-1 * lit1, 1 * lit2}, 0});
        add_constraint({{-1 * lit1, 1 * lit3}, 0});
        add_constraint({{1 * lit1, -1 * lit2, -1 * lit3}, -1});
    }

    void add_comment(std::string text)
    {
        comments.push_back({text, constraints.size()});
    }

    void output_model(std::ostream & ostream)
    {
        std::set<std::string> vars;
        for (auto & constraint : constraints) {
            for (auto & term : constraint.lhs) {
                vars.insert(term.literal.var);
            }
        }

        ostream << "* #variable= " << vars.size() << " #constraint= "
                << constraints.size() << std::endl;

        if (!objective.empty()) {
            ostream << "min: ";
            for (auto term : objective) {
                ostream << term.to_string() << " ";
            }
            ostream << ";" << std::endl;
        }

        vector<InequalityGeq>::size_type constraint_num = 0;
        vector<OpbComment>::size_type pos_in_comments = 0;
        for (InequalityGeq & constraint : constraints) {
            while (pos_in_comments < comments.size() && comments[pos_in_comments].position == constraint_num) {
                ostream << "* " << comments[pos_in_comments].text << std::endl;
                ++pos_in_comments;
            }
            ostream << constraint.to_string() << std::endl;
            ++constraint_num;
        }
        while (pos_in_comments < comments.size()) {
            ostream << "* " << comments[pos_in_comments].text << std::endl;
            ++pos_in_comments;
        }
    }
};

Literal assignment_var(int p, int t)
{
    return "x" + std::to_string(p+1) + "_" + std::to_string(t+1);
}

Literal c_var(int k, int u, int w)
{
    return "xc" + std::to_string(k) + "_" + std::to_string(u+1) + "_"
            + std::to_string(w+1);
}

Literal c_var(int k, int u, int v, int w)
{
    return "xc" + std::to_string(k) + "_" + std::to_string(u+1) + "_"
            + std::to_string(v+1) + "_" + std::to_string(w+1);
}

// An equality constraint
InequalityGeq mapping_constraint(int p, int target_count)
{
    InequalityGeq constraint {};
    for (int t=-1; t<target_count; t++) {
        constraint.add_term(1 * assignment_var(p, t));
    }
    constraint.set_rhs(1);
    return constraint;
}

InequalityGeq injectivity_constraint(int t, int pattern_count)
{
    InequalityGeq constraint {};
    for (int p=0; p<pattern_count; p++) {
        constraint.add_term(-1 * assignment_var(p, t));
    }
    constraint.set_rhs(-1);
    return constraint;
}

InequalityGeq adjacency_constraint(int p, int q, int t,
        const Graph & pattern_g, const Graph & target_g)
{
    InequalityGeq constraint {};
    bool p_q_adjacent = pattern_g.adjmat[p][q];
    constraint.add_term(1 * ~assignment_var(p, t));
    for (int i=0; i<target_g.n; i++) {
        if (i != t && target_g.adjmat[t][i] == p_q_adjacent) {
            constraint.add_term(1 * assignment_var(q, i));
        }
    }
    constraint.add_term(1 * assignment_var(q, -1));
    constraint.set_rhs(1);
    return constraint;
}

InequalityGeq objective_constraint(int pattern_count, int target_count, int goal)
{
    InequalityGeq constraint {};
    for (int p=0; p<pattern_count; p++) {
        for (int t=0; t<target_count; t++) {
            constraint.add_term(1 * assignment_var(p, t));
        }
    }
    constraint.set_rhs(goal);
    return constraint;
}

InequalityGeq connectedness_inductive_case_b_part_1(int k, int u, int w, const Graph & pattern_g,
        bool exclude_u_and_w)
{
    InequalityGeq constraint {};
    constraint.add_term(1 * ~c_var(k, u, w));
    for (int v=0; v<pattern_g.n; v++) {
        if (exclude_u_and_w && (u==v || w==v)) {
            continue;
        }
        constraint.add_term(1 * c_var(k, u, v, w));
    }
    constraint.set_rhs(1);
    return constraint;
}

InequalityGeq connectedness_inductive_case_b_version_3_part_1(int k, int u, int w, const Graph & pattern_g)
{
    InequalityGeq constraint {};
    constraint.add_term(1 * ~c_var(k, u, w));
    for (int v=0; v<pattern_g.n; v++) {
        if (v == u || !pattern_g.adjmat[v][w]) {
            continue;
        }
        constraint.add_term(1 * c_var(k, u, v, w));
    }
    constraint.set_rhs(1);
    return constraint;
}

void add_connectedness_base_constraint_2vv(int u, int w, const Graph & pattern_g,
        int index_of_base_variable, PbModel & pb_model)
{
    pb_model.add_literal_iff_conjunction(c_var(index_of_base_variable, u, w),
            ~assignment_var(u, -1), ~assignment_var(w, -1));
}

// An equality constraint for A <===> B
InequalityGeq connectedness_base_constraint_1v(int k, int u, const Graph & pattern_g)
{
    return {{1 * ~c_var(k, u, u), 1 * ~assignment_var(u, -1)}, 1};
}

void add_connectivity_constraints(PbModel & pb_model, const Graph & g0, int K)
{
    for (int p=0; p<g0.n; p++) {
        for (int q=0; q<g0.n; q++) {
            if (p == q) {
                continue;
            }
            pb_model.add_comment("Connectedness constraint p=" + std::to_string(p) + " q=" + std::to_string(q));
            pb_model.add_constraint({{1 * c_var(K, p, q), 1 * assignment_var(p, -1), 1 * assignment_var(q, -1)}, 1});
        }
    }
}

int ceil_of_log_base_2(int x) {
    int K = 0;
    int two_to_K = 1;
    while (two_to_K < x) {
        ++K;
        two_to_K *= 2;
    }
    return K;
}

void add_connectivity_to_pb_model_version_1(PbModel & pb_model, const Graph & g0)
{
    // base case
    for (int u=0; u<g0.n; u++) {
        for (int w=0; w<g0.n; w++) {
            if (u == w) {
                pb_model.add_comment("Base connectedness constraint for vertex " + std::to_string(u));
                pb_model.add_equality_constraint(connectedness_base_constraint_1v(0, u, g0));
            } else if (g0.adjmat[u][w]) {
                pb_model.add_comment("Base connectedness constraint for vertices " + std::to_string(u) + " and " + std::to_string(w));
                add_connectedness_base_constraint_2vv(u, w, g0, 0, pb_model);
            } else {
                pb_model.add_comment("Base case non-connectedness constraint for vertices " + std::to_string(u) + " and " + std::to_string(w));
                pb_model.add_constraint({{-1 * c_var(0, u, w)}, 0});
            }
        }
    }

    // inductive case
    int K = ceil_of_log_base_2(g0.n - 1);
    for (int k=1; k<=K; k++) {
        for (int u=0; u<g0.n; u++) {
            pb_model.add_comment("Base connectedness constraint for vertex " + std::to_string(u));
            pb_model.add_equality_constraint(connectedness_base_constraint_1v(k, u, g0));
            for (int w=0; w<g0.n; w++) {
                if (u == w) {
                    continue;
                }
                for (int v=0; v<g0.n; v++) {
                    pb_model.add_comment("Inductive connectedness constraint part a for k=" + std::to_string(k)
                            + " u=" + std::to_string(u)
                            + " v=" + std::to_string(v)
                            + " w=" + std::to_string(w));
                    pb_model.add_literal_iff_conjunction(c_var(k, u, v, w), c_var(k-1, u, v), c_var(k-1, v, w));
                }
                pb_model.add_comment("Inductive connectedness constraint part b for k=" + std::to_string(k)
                        + " u=" + std::to_string(u)
                        + " w=" + std::to_string(w));
                pb_model.add_constraint(connectedness_inductive_case_b_part_1(k, u, w, g0, false));
                for (int v=0; v<g0.n; v++) {
                    pb_model.add_constraint({{1 * c_var(k, u, w), 1 * ~c_var(k, u, v, w)}, 1});
                }
            }
        }
    }

    add_connectivity_constraints(pb_model, g0, K);
}

void add_connectivity_to_pb_model_version_2(PbModel & pb_model, const Graph & g0)
{
    // base case
    for (int u=0; u<g0.n; u++) {
        for (int w=0; w<g0.n; w++) {
            if (u == w) {
                continue;
            }
            if (g0.adjmat[u][w]) {
                pb_model.add_comment("Base connectedness constraint for vertices " + std::to_string(u) + " and " + std::to_string(w));
                add_connectedness_base_constraint_2vv(u, w, g0, 0, pb_model);
            } else {
                pb_model.add_comment("Base case non-connectedness constraint for vertices " + std::to_string(u) + " and " + std::to_string(w));
                pb_model.add_constraint({{-1 * c_var(0, u, w)}, 0});
            }
        }
    }

    // inductive case
    int K = ceil_of_log_base_2(g0.n - 1);
    for (int k=1; k<=K; k++) {
        for (int u=0; u<g0.n; u++) {
            for (int w=0; w<g0.n; w++) {
                if (u == w) {
                    continue;
                }
                for (int v=0; v<g0.n; v++) {
                    if (u == v || w == v) {
                        continue;
                    }
                    pb_model.add_comment("Inductive connectedness constraint part a for k=" + std::to_string(k)
                            + " u=" + std::to_string(u)
                            + " v=" + std::to_string(v)
                            + " w=" + std::to_string(w));
                    pb_model.add_literal_iff_conjunction(c_var(k, u, v, w), c_var(k-1, u, v), c_var(k-1, v, w));
                }
                pb_model.add_comment("Inductive connectedness constraint part b for k=" + std::to_string(k)
                        + " u=" + std::to_string(u)
                        + " w=" + std::to_string(w));
                InequalityGeq constraint = connectedness_inductive_case_b_part_1(k, u, w, g0, true);
                constraint.add_term(1 * c_var(k-1, u, w));
                pb_model.add_constraint(constraint);
                for (int v=0; v<g0.n; v++) {
                    if (u == v || w == v) {
                        continue;
                    }
                    pb_model.add_constraint({{1 * c_var(k, u, w), 1 * ~c_var(k, u, v, w)}, 1});
                }
                pb_model.add_constraint({{1 * c_var(k, u, w), 1 * ~c_var(k-1, u, w)}, 1});
            }
        }
    }

    add_connectivity_constraints(pb_model, g0, K);
}

void add_connectivity_to_pb_model_version_3(PbModel & pb_model, const Graph & g0)
{
    // base case
    for (int u=0; u<g0.n; u++) {
        for (int w=0; w<g0.n; w++) {
            if (u == w) {
                continue;
            }
            if (g0.adjmat[u][w]) {
                pb_model.add_comment("Base connectedness constraint for vertices " + std::to_string(u) + " and " + std::to_string(w));
                add_connectedness_base_constraint_2vv(u, w, g0, 1, pb_model);
            } else {
                pb_model.add_comment("Base case non-connectedness constraint for vertices " + std::to_string(u) + " and " + std::to_string(w));
                pb_model.add_constraint({{-1 * c_var(1, u, w)}, 0});
            }
        }
    }

    // inductive case
    int K = g0.n - 1;
    for (int k=2; k<=K; k++) {
        for (int u=0; u<g0.n; u++) {
            for (int w=0; w<g0.n; w++) {
                if (u == w) {
                    continue;
                }
                for (int v=0; v<g0.n; v++) {
                    if (u == v || !g0.adjmat[v][w]) {
                        continue;
                    }
                    pb_model.add_comment("Inductive connectedness constraint part a for k=" + std::to_string(k)
                            + " u=" + std::to_string(u)
                            + " v=" + std::to_string(v)
                            + " w=" + std::to_string(w));
                    pb_model.add_literal_iff_conjunction(c_var(k, u, v, w), c_var(k-1, u, v), c_var(1, v, w));
                }
                pb_model.add_comment("Inductive connectedness constraint part b for k=" + std::to_string(k)
                        + " u=" + std::to_string(u)
                        + " w=" + std::to_string(w));
                InequalityGeq constraint = connectedness_inductive_case_b_version_3_part_1(k, u, w, g0);
                constraint.add_term(1 * c_var(k-1, u, w));
                pb_model.add_constraint(constraint);
                for (int v=0; v<g0.n; v++) {
                    if (u == v || !g0.adjmat[v][w]) {
                        continue;
                    }
                    pb_model.add_constraint({{1 * c_var(k, u, w), 1 * ~c_var(k, u, v, w)}, 1});
                }
                pb_model.add_constraint({{1 * c_var(k, u, w), 1 * ~c_var(k-1, u, w)}, 1});
            }
        }
    }

    add_connectivity_constraints(pb_model, g0, K);
}

PbModel build_pb_model(const Graph & g0, const Graph & g1, int target_subgraph_size,
        vector<int> & mapping_constraint_nums, vector<int> & injectivity_constraint_nums)
{
    PbModel pb_model;

    if (target_subgraph_size == -1) {
        // optimisation version
        for (int p=0; p<g0.n; p++) {
            for (int t=0; t<g0.n; t++) {
                pb_model.add_objective_term(1 * ~assignment_var(p, t));
            }
        }
    } else {
        pb_model.add_comment("Objective");
        pb_model.add_constraint(objective_constraint(g0.n, g1.n, target_subgraph_size));
    }

    if (arguments.vertex_labelled) {
        pb_model.add_comment("Vertex label constraints");
        for (int p=0; p<g0.n; p++) {
            for (int t=0; t<g1.n; t++) {
                if (g0.label[p] != g1.label[t]) {
                    // The labels of vertices p and t do not match, so p cannot be matched to t
                    pb_model.add_constraint({{-1 * assignment_var(p, t)}, 0});
                }
            }
        }
    }

    for (int i=0; i<g0.n; i++) {
        pb_model.add_comment("Mapping constraint for pattern vertex " + std::to_string(i));
        pb_model.add_equality_constraint(mapping_constraint(i, g1.n));
        mapping_constraint_nums[i] = pb_model.last_constraint_number();
    }
    for (int i=0; i<g1.n; i++) {
        pb_model.add_comment("Injectivity constraint for target vertex " + std::to_string(i));
        pb_model.add_constraint(injectivity_constraint(i, g0.n));
        injectivity_constraint_nums[i] = pb_model.last_constraint_number();
    }
    for (int p=0; p<g0.n; p++) {
        for (int q=0; q<g0.n; q++) {
            if (q==p) {
                continue;
            }
            pb_model.add_comment("Adjacency constraints for pattern edge or non-edge "
                    + std::to_string(p) + "," + std::to_string(q));
            for (int t=0; t<g1.n; t++) {
                pb_model.add_constraint(adjacency_constraint(p, q, t, g0, g1));
            }
        }
    }

    switch (arguments.connected) {
    case 1:
        add_connectivity_to_pb_model_version_1(pb_model, g0);
        break;
    case 2:
        add_connectivity_to_pb_model_version_2(pb_model, g0);
        break;
    case 3:
        add_connectivity_to_pb_model_version_3(pb_model, g0);
        break;
    }

    return pb_model;
}

/*******************************************************************************
                                     Stats
*******************************************************************************/

unsigned long long solution_count{ 0 };

/*******************************************************************************
                                 MCS functions
*******************************************************************************/

struct VtxPair {
    int v;
    int w;
};

struct Bidomain {
    int l,        r;        // start indices of left and right sets
    int left_len, right_len;
    bool is_adjacent;
    Bidomain(int l, int r, int left_len, int right_len, bool is_adjacent):
            l(l),
            r(r),
            left_len (left_len),
            right_len (right_len),
            is_adjacent (is_adjacent) { };
};

void show(const vector<VtxPair>& current, const vector<Bidomain> &domains,
        const vector<int>& left, const vector<int>& right)
{
    cout << "Length of current assignment: " << current.size() << std::endl;
    cout << "Current assignment:";
    for (unsigned int i=0; i<current.size(); i++) {
        cout << "  (" << current[i].v << " -> " << current[i].w << ")";
    }
    cout << std::endl;
    for (unsigned int i=0; i<domains.size(); i++) {
        struct Bidomain bd = domains[i];
        cout << "Left  ";
        for (int j=0; j<bd.left_len; j++)
            cout << left[bd.l + j] << " ";
        cout << std::endl;
        cout << "Right  ";
        for (int j=0; j<bd.right_len; j++)
            cout << right[bd.r + j] << " ";
        cout << std::endl;
    }
    cout << "\n" << std::endl;
}

bool check_sol(const Graph & g0, const Graph & g1 , const vector<VtxPair> & solution) {
    return true;
    vector<bool> used_left(g0.n, false);
    vector<bool> used_right(g1.n, false);
    for (unsigned int i=0; i<solution.size(); i++) {
        struct VtxPair p0 = solution[i];
        if (used_left[p0.v] || used_right[p0.w])
            return false;
        used_left[p0.v] = true;
        used_right[p0.w] = true;
        if (g0.label[p0.v] != g1.label[p0.w])
            return false;
        for (unsigned int j=i+1; j<solution.size(); j++) {
            struct VtxPair p1 = solution[j];
            if (g0.adjmat[p0.v][p1.v] != g1.adjmat[p0.w][p1.w])
                return false;
        }
    }
    return true;
}

int calc_bound(const vector<Bidomain>& domains) {
    int bound = 0;
    for (const Bidomain &bd : domains) {
        bound += std::min(bd.left_len, bd.right_len);
    }
    return bound;
}

int find_min_value(const vector<int>& arr, int start_idx, int len) {
    int min_v = INT_MAX;
    for (int i=0; i<len; i++)
        if (arr[start_idx + i] < min_v)
            min_v = arr[start_idx + i];
    return min_v;
}

int select_bidomain(const vector<Bidomain>& domains, const vector<int> & left,
        int current_matching_size)
{
    // Select the bidomain with the smallest max(leftsize, rightsize), breaking
    // ties on the smallest vertex index in the left set
    int min_size = INT_MAX;
    int min_tie_breaker = INT_MAX;
    int best = -1;
    for (unsigned int i=0; i<domains.size(); i++) {
        const Bidomain &bd = domains[i];
        if (arguments.connected && current_matching_size>0 && !bd.is_adjacent) continue;
        int len = std::max(bd.left_len, bd.right_len);
        if (len < min_size) {
            min_size = len;
            min_tie_breaker = find_min_value(left, bd.l, bd.left_len);
            best = i;
        } else if (len == min_size) {
            int tie_breaker = find_min_value(left, bd.l, bd.left_len);
            if (tie_breaker < min_tie_breaker) {
                min_tie_breaker = tie_breaker;
                best = i;
            }
        }
    }
    return best;
}

// Returns length of left half of array
int partition(vector<int>& all_vv, int start, int len, const vector<unsigned int> & adjrow) {
    int i=0;
    for (int j=0; j<len; j++) {
        if (adjrow[all_vv[start+j]]) {
            std::swap(all_vv[start+i], all_vv[start+j]);
            i++;
        }
    }
    return i;
}

vector<Bidomain> filter_domains(const vector<Bidomain> & d, vector<int> & left,
        vector<int> & right, const Graph & g0, const Graph & g1, int v, int w)
{
    vector<Bidomain> new_d;
    new_d.reserve(d.size());
    for (const Bidomain &old_bd : d) {
        int l = old_bd.l;
        int r = old_bd.r;
        // After these two partitions, left_len and right_len are the lengths of the
        // arrays of vertices with edges from v or w
        int left_len = partition(left, l, old_bd.left_len, g0.adjmat[v]);
        int right_len = partition(right, r, old_bd.right_len, g1.adjmat[w]);
        int left_len_noedge = old_bd.left_len - left_len;
        int right_len_noedge = old_bd.right_len - right_len;
        if (left_len_noedge && right_len_noedge) {
            new_d.push_back({l+left_len, r+right_len, left_len_noedge, right_len_noedge, old_bd.is_adjacent});
        }
        if (left_len && right_len) {
            new_d.push_back({l, r, left_len, right_len, true});
        }
    }
    return new_d;
}

// returns the index of the smallest value in arr that is >w.
// Assumption: such a value exists
// Assumption: arr contains no duplicates
// Assumption: arr has no values==INT_MAX
int index_of_next_smallest(const vector<int>& arr, int start_idx, int len, int w) {
    int idx = -1;
    int smallest = INT_MAX;
    for (int i=0; i<len; i++) {
        if (arr[start_idx + i]>w && arr[start_idx + i]<smallest) {
            smallest = arr[start_idx + i];
            idx = i;
        }
    }
    return idx;
}

void remove_vtx_from_left_domain(vector<int>& left, Bidomain& bd, int v)
{
    int i = 0;
    while(left[bd.l + i] != v) i++;
    std::swap(left[bd.l+i], left[bd.l+bd.left_len-1]);
    bd.left_len--;
}

void remove_bidomain(vector<Bidomain>& domains, int idx) {
    domains[idx] = domains[domains.size()-1];
    domains.pop_back();
}

void write_backtracking_constraint(const vector<Literal> & decisions, std::ostream & proof_stream)
{
    proof_stream << "u ";
    InequalityGeq constraint {};
    for (auto & decision : decisions) {
        constraint.add_term(-1 * decision);
    }
    constraint.set_rhs(-decisions.size() + 1);
    proof_stream << constraint.to_string();
    proof_stream << std::endl;
}

struct ProofLoggingData
{
    std::optional<std::ofstream> & proof_stream;
    const vector<int> & vtx_name0;
    const vector<int> & vtx_name1;
    const vector<int> & mapping_constraint_nums;
    const vector<int> & injectivity_constraint_nums;
    int & last_constraint_num;
    vector<Literal> & decisions;
    int number_of_most_recent_objective_constraint = 1;
};

void write_bound_constraint(
        const vector<Bidomain> & domains,
        vector<int> & left,
        vector<int> & right,
        ProofLoggingData & pld)
{
    if (domains.empty()) {
        return;
    }
    vector<int> constraint_nums;
    for (const Bidomain &bd : domains) {
        if (bd.left_len <= bd.right_len) {
            for (int i=0; i<bd.left_len; i++) {
                int v_in_sorted_graph = left[bd.l+i];
                int v_in_original_graph = pld.vtx_name0[v_in_sorted_graph];
                constraint_nums.push_back(pld.mapping_constraint_nums[v_in_original_graph]);
            }
        } else {
            for (int i=0; i<bd.right_len; i++) {
                int v_in_sorted_graph = right[bd.r+i];
                int v_in_original_graph = pld.vtx_name1[v_in_sorted_graph];
                constraint_nums.push_back(pld.injectivity_constraint_nums[v_in_original_graph]);
            }
        }
    }
    *pld.proof_stream << "p ";
    bool first = true;
    for (int constraint_num : constraint_nums) {
        *pld.proof_stream << constraint_num << " ";
        if (!first) {
            *pld.proof_stream << "+ ";
        }
        first = false;
    }
    *pld.proof_stream << pld.number_of_most_recent_objective_constraint << " + 0";
    *pld.proof_stream << std::endl;
    ++pld.last_constraint_num;
}

void write_solution(const vector<VtxPair> & current,
        const Graph & pattern_g,
        const Graph & target_g,
        char prefix,
        ProofLoggingData & pld)
{
    vector<vector<bool>> assignment_made(pattern_g.n, vector<bool>(target_g.n));
    for (auto assignment : current) {
        int v = pld.vtx_name0[assignment.v];
        int w = pld.vtx_name1[assignment.w];
        assignment_made[v][w] = true;
    }
    *pld.proof_stream << prefix;
    for (int v=0; v<pattern_g.n; v++) {
        for (int w=0; w<pattern_g.n; w++) {
            if (assignment_made[v][w]) {
                *pld.proof_stream << " " << assignment_var(v, w).var;
            } else {
                *pld.proof_stream << " ~" << assignment_var(v, w).var;
            }
        }
    }
    *pld.proof_stream << std::endl;
    ++pld.last_constraint_num;
    if (prefix == 'o')
        pld.number_of_most_recent_objective_constraint = pld.last_constraint_num;
}

void proof_level_set(int level, std::ostream & proof_stream)
{
    proof_stream << "# " << level << std::endl;
}

void proof_level_wipe(int level, std::ostream & proof_stream)
{
    proof_stream << "w " << level << std::endl;
}

void solve(const Graph & g0, const Graph & g1, vector<VtxPair> & incumbent,
        vector<VtxPair> & current, vector<Bidomain> & domains,
        vector<int> & left, vector<int> & right, unsigned int matching_size_goal,
        ProofLoggingData & pld)
{
    if (abort_due_to_timeout)
        return;

    int decisions_len_at_start_of_solve = pld.decisions.size();

    if (arguments.verbose) {
        show(current, domains, left, right);
    }

    if (current.size() > incumbent.size()) {
        incumbent = current;
        if (arguments.decision_size==-1 && pld.proof_stream) {
            proof_level_set(0, *pld.proof_stream);
            write_solution(current, g0, g1, 'o', pld);
            proof_level_set(current.size(), *pld.proof_stream);
        }
    }

    unsigned int bound = current.size() + calc_bound(domains);
    if ((!arguments.count_solutions && bound <= incumbent.size()) || bound < matching_size_goal) {
        if (pld.proof_stream) {
            write_bound_constraint(domains, left, right, pld);
        }
        return;
    }

    if ((arguments.decision_size != -1 && !arguments.count_solutions) && incumbent.size()==matching_size_goal)
        return;

    int bd_idx = select_bidomain(domains, left, current.size());
    if (bd_idx == -1)   // In the MCCS case, there may be nothing we can branch on
        return;
    Bidomain &bd = domains[bd_idx];

    int v = find_min_value(left, bd.l, bd.left_len);
    remove_vtx_from_left_domain(left, domains[bd_idx], v);

    // Try assigning v to each vertex w in the colour class beginning at bd.r, in turn
    int w = -1;
    bd.right_len--;
    for (int i=0; i<=bd.right_len; i++) {
        int idx = index_of_next_smallest(right, bd.r, bd.right_len+1, w);
        w = right[bd.r + idx];

        // swap w to the end of its colour class
        right[bd.r + idx] = right[bd.r + bd.right_len];
        right[bd.r + bd.right_len] = w;

        auto new_domains = filter_domains(domains, left, right, g0, g1, v, w);
        current.push_back({v, w});
        if (pld.proof_stream) {
            pld.decisions.push_back(assignment_var(pld.vtx_name0[v], pld.vtx_name1[w]));
            proof_level_set(current.size(), *pld.proof_stream);
        }

        if (arguments.count_solutions && current.size() >= matching_size_goal) {
            ++solution_count;
            if (pld.proof_stream) {
                write_solution(current, g0, g1, 'v', pld);
            }
        }

        solve(g0, g1, incumbent, current, new_domains, left, right, matching_size_goal, pld);
        if (arguments.decision_size != -1 && !arguments.count_solutions && incumbent.size()==matching_size_goal) {
            return;
        }
        current.pop_back();
        if (pld.proof_stream) {
            proof_level_set(current.size(), *pld.proof_stream);
            write_backtracking_constraint(pld.decisions, *pld.proof_stream);
            ++pld.last_constraint_num;
            proof_level_wipe(current.size() + 1, *pld.proof_stream);
            pld.decisions.pop_back();
            pld.decisions.push_back(~assignment_var(pld.vtx_name0[v], pld.vtx_name1[w]));
        }
    }
    bd.right_len++;
    if (bd.left_len == 0)
        remove_bidomain(domains, bd_idx);
    if (pld.proof_stream) {
        pld.decisions.resize(decisions_len_at_start_of_solve);
        pld.decisions.push_back(assignment_var(pld.vtx_name0[v], -1));
    }
    solve(g0, g1, incumbent, current, domains, left, right, matching_size_goal, pld);
    pld.decisions.resize(decisions_len_at_start_of_solve);
}

vector<VtxPair> mcs(const Graph & g0, const Graph & g1,
            const vector<int> & vtx_name0, const vector<int> & vtx_name1,
            int last_constraint_num,
            const vector<int> & mapping_constraint_nums,
            const vector<int> & injectivity_constraint_nums)
{
    vector<int> left;  // the buffer of vertex indices for the left partitions
    vector<int> right;  // the buffer of vertex indices for the right partitions

    auto domains = vector<Bidomain> {};

    std::set<unsigned int> left_labels;
    std::set<unsigned int> right_labels;
    for (unsigned int label : g0.label) left_labels.insert(label);
    for (unsigned int label : g1.label) right_labels.insert(label);
    std::set<unsigned int> labels;  // labels that appear in both graphs
    std::set_intersection(std::begin(left_labels),
                          std::end(left_labels),
                          std::begin(right_labels),
                          std::end(right_labels),
                          std::inserter(labels, std::begin(labels)));

    // Create a bidomain for each label that appears in both graphs
    for (unsigned int label : labels) {
        int start_l = left.size();
        int start_r = right.size();

        for (int i=0; i<g0.n; i++)
            if (g0.label[i]==label)
                left.push_back(i);
        for (int i=0; i<g1.n; i++)
            if (g1.label[i]==label)
                right.push_back(i);

        int left_len = left.size() - start_l;
        int right_len = right.size() - start_r;
        domains.push_back({start_l, start_r, left_len, right_len, false});
    }

    vector<VtxPair> incumbent;
    vector<Literal> decisions;

    if (arguments.proof_filename && !arguments.opb_filename) {
        std::cerr << "If -p options is used, -o option must be used also." << std::endl;
        exit(1);
    }

    auto proof_stream = arguments.proof_filename ?
            std::optional<std::ofstream> {arguments.proof_filename} :
            std::nullopt;
    if (proof_stream) {
        *proof_stream << "pseudo-Boolean proof version 1.0" << std::endl;
        *proof_stream << "f " << last_constraint_num << " 0" << std::endl;
        proof_level_set(0, *proof_stream);
    }

    vector<VtxPair> current;

    ProofLoggingData pld {proof_stream, vtx_name0, vtx_name1, mapping_constraint_nums, injectivity_constraint_nums,
                last_constraint_num, decisions};
    if (arguments.decision_size != -1) {
        if (arguments.count_solutions && 0 == arguments.decision_size) {
            ++solution_count;
            if (proof_stream) {
                write_solution(current, g0, g1, 'v', pld);
            }
        }
        solve(g0, g1, incumbent, current, domains, left, right, arguments.decision_size, pld);
    } else {
        auto domains_copy = domains;
        solve(g0, g1, incumbent, current, domains_copy, left, right, 1, pld);
    }
    if (proof_stream && (arguments.count_solutions || arguments.decision_size == -1 || int(incumbent.size()) < arguments.decision_size)) {
        *proof_stream << "u >= 1;" << std::endl;
        ++last_constraint_num;
        *proof_stream << "c " << last_constraint_num << " 0" << std::endl;
    }

    return incumbent;
}

vector<int> calculate_degrees(const Graph & g) {
    vector<int> degree(g.n, 0);
    for (int v=0; v<g.n; v++)
        for (int w=0; w<g.n; w++)
            if (g.adjmat[v][w])
                degree[v]++;
    return degree;
}

int sum(const vector<int> & vec) {
    return std::accumulate(std::begin(vec), std::end(vec), 0);
}

int main(int argc, char** argv) {
    set_default_arguments();
    argp_parse(&argp, argc, argv, 0, 0, 0);

    if (arguments.count_solutions && arguments.decision_size == -1) {
        std::cerr << "Solution counting is only supported for the decision problem" << std::endl;
        exit(1);
    }

    char format = arguments.dimacs ? 'D' : arguments.lad ? 'L' : 'B';
    struct Graph g0 = readGraph(arguments.filename1, format, false,
            false, arguments.vertex_labelled);
    struct Graph g1 = readGraph(arguments.filename2, format, false,
            false, arguments.vertex_labelled);

    std::thread timeout_thread;
    std::mutex timeout_mutex;
    std::condition_variable timeout_cv;
    abort_due_to_timeout.store(false);
    bool aborted = false;

    if (0 != arguments.timeout) {
        timeout_thread = std::thread([&] {
                auto abort_time = std::chrono::steady_clock::now() + std::chrono::seconds(arguments.timeout);
                {
                    /* Sleep until either we've reached the time limit,
                     * or we've finished all the work. */
                    std::unique_lock<std::mutex> guard(timeout_mutex);
                    while (! abort_due_to_timeout.load()) {
                        if (std::cv_status::timeout == timeout_cv.wait_until(guard, abort_time)) {
                            /* We've woken up, and it's due to a timeout. */
                            aborted = true;
                            break;
                        }
                    }
                }
                abort_due_to_timeout.store(true);
                });
    }

    auto start = std::chrono::steady_clock::now();

    vector<int> mapping_constraint_nums(g0.n);
    vector<int> injectivity_constraint_nums(g1.n);
    int last_constraint_num = 0;
    if (arguments.opb_filename) {
        std::ofstream opb_stream(arguments.opb_filename);
        auto pb_model = build_pb_model(g0, g1, arguments.decision_size,
                mapping_constraint_nums, injectivity_constraint_nums);
        pb_model.output_model(opb_stream);
        last_constraint_num = pb_model.last_constraint_number();
    }

    vector<int> g0_deg = calculate_degrees(g0);
    vector<int> g1_deg = calculate_degrees(g1);

    // Use the same ordering of vertices as in the IJCAI 2017 paper.
    vector<int> vv0(g0.n);
    std::iota(std::begin(vv0), std::end(vv0), 0);
    bool g1_dense = sum(g1_deg) > g1.n*(g1.n-1);
    std::stable_sort(std::begin(vv0), std::end(vv0), [&](int a, int b) {
        return g1_dense ? (g0_deg[a]<g0_deg[b]) : (g0_deg[a]>g0_deg[b]);
    });
    vector<int> vv1(g1.n);
    std::iota(std::begin(vv1), std::end(vv1), 0);
    bool g0_dense = sum(g0_deg) > g0.n*(g0.n-1);
    std::stable_sort(std::begin(vv1), std::end(vv1), [&](int a, int b) {
        return g0_dense ? (g1_deg[a]<g1_deg[b]) : (g1_deg[a]>g1_deg[b]);
    });

    struct Graph g0_sorted = induced_subgraph(g0, vv0);
    struct Graph g1_sorted = induced_subgraph(g1, vv1);

    vector<VtxPair> solution = mcs(g0_sorted, g1_sorted, vv0, vv1, last_constraint_num,
            mapping_constraint_nums, injectivity_constraint_nums);

    // Convert to indices from original, unsorted graphs
    for (auto& vtx_pair : solution) {
        vtx_pair.v = vv0[vtx_pair.v];
        vtx_pair.w = vv1[vtx_pair.w];
    }

    auto stop = std::chrono::steady_clock::now();
    auto time_elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start).count();

    /* Clean up the timeout thread */
    if (timeout_thread.joinable()) {
        {
            std::unique_lock<std::mutex> guard(timeout_mutex);
            abort_due_to_timeout.store(true);
            timeout_cv.notify_all();
        }
        timeout_thread.join();
    }

    if (!check_sol(g0, g1, solution))
        fail("*** Error: Invalid solution\n");

    if (arguments.decision_size != -1) {
        cout << "Satisfiable? " << (int(solution.size()) >= arguments.decision_size) << std::endl;
    } else {
        cout << "Solution size " << solution.size() << std::endl;
        for (int i=0; i<g0.n; i++)
            for (unsigned int j=0; j<solution.size(); j++)
                if (solution[j].v == i)
                    cout << "(" << solution[j].v << " -> " << solution[j].w << ") ";
        cout << std::endl;
    }

    if (arguments.count_solutions)
        cout << "Solutions counted:          " << solution_count << endl;
    cout << "CPU time (ms):              " << time_elapsed << endl;
    if (aborted)
        cout << "TIMEOUT" << endl;
}
