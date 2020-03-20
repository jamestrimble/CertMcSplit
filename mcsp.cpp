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

// FIXME: make this non-global!
int number_of_most_recent_objective_constraint = 1;

using std::vector;
using std::cout;
using std::endl;

static void fail(std::string msg) {
    std::cerr << msg << std::endl;
    exit(1);
}

enum Heuristic { min_max, min_product };

/*******************************************************************************
                             Command-line arguments
*******************************************************************************/

static char doc[] = "Find a maximum common subgraph of two graphs \vHEURISTIC can be min_max or min_product";
static char args_doc[] = "HEURISTIC FILENAME1 FILENAME2";
static struct argp_option options[] = {
    {"quiet", 'q', 0, 0, "Quiet output"},
    {"verbose", 'v', 0, 0, "Verbose output"},
    {"dimacs", 'd', 0, 0, "Read DIMACS format"},
    {"lad", 'l', 0, 0, "Read LAD format"},
    {"connected", 'c', "version", 0, "Solve MCCS (with PB model version 1, 2 or 3)"},
    {"directed", 'i', 0, 0, "Use directed graphs"},
    {"labelled", 'a', 0, 0, "Use edge and vertex labels"},
    {"vertex-labelled-only", 'x', 0, 0, "Use vertex labels, but not edge labels"},
    {"big-first", 'b', 0, 0, "First try to find an induced subgraph isomorphism, then decrement the target size"},
    {"count-solutions", 'C', 0, 0, "(For the decision problem only) count solutions"},
    {"decision", 'D', "size", 0, "Solve the decision problem"},
    {"timeout", 't', "timeout", 0, "Specify a timeout (seconds)"},
    {"opb-filename", 'o', "FILENAME", 0, "Write OPB to FILENAME (decision problem only)"},
    {"proof-filename", 'p', "FILENAME", 0, "Write proof to FILENAME (decision problem only)"},
    { 0 }
};

static struct {
    bool quiet;
    bool verbose;
    bool dimacs;
    bool lad;
    int connected;
    bool directed;
    bool edge_labelled;
    bool vertex_labelled;
    bool big_first;
    bool count_solutions;
    Heuristic heuristic;
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
    arguments.quiet = false;
    arguments.verbose = false;
    arguments.dimacs = false;
    arguments.lad = false;
    arguments.connected = 0;
    arguments.directed = false;
    arguments.edge_labelled = false;
    arguments.vertex_labelled = false;
    arguments.big_first = false;
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
        case 'q':
            arguments.quiet = true;
            break;
        case 'v':
            arguments.verbose = true;
            break;
        case 'c':
            if (arguments.directed)
                fail("The connected and directed options can't be used together.");
            arguments.connected = std::stoi(arg);
            break;
        case 'i':
            if (arguments.connected)
                fail("The connected and directed options can't be used together.");
            arguments.directed = true;
            break;
        case 'a':
            if (arguments.vertex_labelled)
                fail("The -a and -x options can't be used together.");
            arguments.edge_labelled = true;
            arguments.vertex_labelled = true;
            break;
        case 'x':
            if (arguments.edge_labelled)
                fail("The -a and -x options can't be used together.");
            arguments.vertex_labelled = true;
            break;
        case 'b':
            arguments.big_first = true;
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
                if (std::string(arg) == "min_max")
                    arguments.heuristic = min_max;
                else if (std::string(arg) == "min_product")
                    arguments.heuristic = min_product;
                else
                    fail("Unknown heuristic (try min_max or min_product)");
            } else if (arguments.arg_num == 1) {
                arguments.filename1 = arg;
            } else if (arguments.arg_num == 2) {
                arguments.filename2 = arg;
            } else {
                argp_usage(state);
            }
            arguments.arg_num++;
            break;
        case ARGP_KEY_END:
            if (arguments.arg_num != 3)
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

struct Term
{
    int coef;
    bool is_negated;
    std::string var;

    std::string to_string()
    {
        return std::to_string(coef) + " " + (is_negated ? "~" : "") + var;
    }
};

struct InequalityGeq
{
    std::string comment = {};
    vector<Term> lhs;
    int rhs = 0;

    InequalityGeq & set_comment(std::string comment)
    {
        this->comment = comment;
        return *this;
    }

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

class PbModel
{
    vector<InequalityGeq> constraints;
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

    void output_model(std::ostream & ostream)
    {
        std::set<std::string> vars;
        for (auto & constraint : constraints) {
            for (auto & term : constraint.lhs) {
                vars.insert(term.var);
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

        for (InequalityGeq & constraint : constraints) {
            if (!constraint.comment.empty()) {
                ostream << "* " << constraint.comment << std::endl;
            }
            ostream << constraint.to_string() << std::endl;
        }
    }
};

std::string assignment_var_name(int p, int t)
{
    return "x" + std::to_string(p+1) + "_" + std::to_string(t+1);
}

std::string c2_var_name(int k, int u, int w)
{
    return "xc" + std::to_string(k) + "_" + std::to_string(u+1) + "_"
            + std::to_string(w+1);
}

std::string c3_var_name(int k, int u, int v, int w)
{
    return "xc" + std::to_string(k) + "_" + std::to_string(u+1) + "_"
            + std::to_string(v+1) + "_" + std::to_string(w+1);
}

InequalityGeq mapping_constraint(int p, int target_count, bool direction)
{
    InequalityGeq constraint {};
    for (int t=-1; t<target_count; t++) {
        constraint.add_term({direction ? 1 : -1, false, assignment_var_name(p, t)});
    }
    constraint.set_rhs(direction ? 1 : -1);
    return constraint;
}

InequalityGeq injectivity_constraint(int t, int pattern_count)
{
    InequalityGeq constraint {};
    for (int p=0; p<pattern_count; p++) {
        constraint.add_term({-1, false, assignment_var_name(p, t)});
    }
    constraint.set_rhs(-1);
    return constraint;
}

InequalityGeq adjacency_constraint(int p, int q, int t,
        const Graph & pattern_g, const Graph & target_g)
{
    InequalityGeq constraint {};
    bool p_q_adjacent = pattern_g.adjmat[p][q];
    constraint.add_term({1, true, assignment_var_name(p, t)});
    for (int i=0; i<target_g.n; i++) {
        if (i != t && target_g.adjmat[t][i] == p_q_adjacent) {
            constraint.add_term({1, false, assignment_var_name(q, i)});
        }
    }
    constraint.add_term({1, false, assignment_var_name(q, -1)});
    constraint.set_rhs(1);
    return constraint;
}

InequalityGeq objective_constraint(int pattern_count, int target_count, int goal)
{
    InequalityGeq constraint {};
    for (int p=0; p<pattern_count; p++) {
        for (int t=0; t<target_count; t++) {
            constraint.add_term({1, false, assignment_var_name(p, t)});
        }
    }
    constraint.set_rhs(goal);
    return constraint;
}

// The A <===> B AND C decomposition has three parts.
// `part` is 1, 2, or 3
InequalityGeq constraint_A_implies_B_and_C(Term term1, Term term2, Term term3, int part)
{
    InequalityGeq constraint {};
    if (part == 1) {
        term1.coef = -1;
        constraint.add_term(term1);
        constraint.add_term(term2);
        constraint.set_rhs(0);
    } else if (part == 2) {
        term1.coef = -1;
        constraint.add_term(term1);
        constraint.add_term(term3);
        constraint.set_rhs(0);
    } else {
        term2.coef = -1;
        term3.coef = -1;
        constraint.add_term(term1);
        constraint.add_term(term2);
        constraint.add_term(term3);
        constraint.set_rhs(-1);
    }
    return constraint;
}

InequalityGeq connectedness_inductive_case_a(int k, int u, int v, int w, const Graph & pattern_g, int part)
{
    Term term1 {1, false, c3_var_name(k, u, v, w)};
    Term term2 {1, false, c2_var_name(k-1, u, v)};
    Term term3 {1, false, c2_var_name(k-1, v, w)};
    return constraint_A_implies_B_and_C(term1, term2, term3, part);
}

InequalityGeq connectedness_inductive_case_b_part_1(int k, int u, int w, const Graph & pattern_g,
        bool exclude_u_and_w)
{
    InequalityGeq constraint {};
    constraint.add_term({1, true, c2_var_name(k, u, w)});
    for (int v=0; v<pattern_g.n; v++) {
        if (exclude_u_and_w && (u==v || w==v)) {
            continue;
        }
        constraint.add_term({1, false, c3_var_name(k, u, v, w)});
    }
    constraint.set_rhs(1);
    return constraint;
}

InequalityGeq connectedness_inductive_case_b_part_2(int k, int u, int v, int w, const Graph & pattern_g)
{
    InequalityGeq constraint {};
    constraint.add_term({1, false, c2_var_name(k, u, w)});
    constraint.add_term({1, true, c3_var_name(k, u, v, w)});
    constraint.set_rhs(1);
    return constraint;
}

InequalityGeq connectedness_inductive_case_a_version_3(int k, int u, int v, int w, const Graph & pattern_g, int part)
{
    Term term1 {1, false, c3_var_name(k, u, v, w)};
    Term term2 {1, false, c2_var_name(k-1, u, v)};
    Term term3 {1, false, c2_var_name(1, v, w)};
    return constraint_A_implies_B_and_C(term1, term2, term3, part);
}

InequalityGeq connectedness_inductive_case_b_version_3_part_1(int k, int u, int w, const Graph & pattern_g)
{
    InequalityGeq constraint {};
    constraint.add_term({1, true, c2_var_name(k, u, w)});
    for (int v=0; v<pattern_g.n; v++) {
        if (v == u || !pattern_g.adjmat[v][w]) {
            continue;
        }
        constraint.add_term({1, false, c3_var_name(k, u, v, w)});
    }
    constraint.set_rhs(1);
    return constraint;
}

InequalityGeq connectedness_inductive_case_b_version_3_part_2(int k, int u, int v, int w, const Graph & pattern_g)
{
    InequalityGeq constraint {};
    constraint.add_term({1, false, c2_var_name(k, u, w)});
    constraint.add_term({1, true, c3_var_name(k, u, v, w)});
    constraint.set_rhs(1);
    return constraint;
}

InequalityGeq connectedness_base_constraint_2vv(int u, int w, const Graph & pattern_g,
        int index_of_base_variable, int part)
{
    Term term1 {1, false, c2_var_name(index_of_base_variable, u, w)};
    Term term2 {1, true, assignment_var_name(u, -1)};
    Term term3 {1, true, assignment_var_name(w, -1)};
    return constraint_A_implies_B_and_C(term1, term2, term3, part);
}

// The A <===> B decomposition has two parts.
// `part` is 1 or 2
InequalityGeq connectedness_base_constraint_1v(int k, int u, const Graph & pattern_g,
        int part)
{
    Term term1 {part==2 ? 1 : -1, true, c2_var_name(k, u, u)};
    Term term2 {part==2 ? 1 : -1, true, assignment_var_name(u, -1)};
    InequalityGeq constraint {};
    constraint.add_term(term1);
    constraint.add_term(term2);
    constraint.set_rhs(part == 2 ? 1 : -1);
    return constraint;
}

InequalityGeq connectedness_constraint(int K, int p, int q)
{
    Term term1 {1, false, c2_var_name(K, p, q)};
    Term term2 {1, false, assignment_var_name(p, -1)};
    Term term3 {1, false, assignment_var_name(q, -1)};
    InequalityGeq constraint;
    constraint.add_term(term1)
            .add_term(term2)
            .add_term(term3)
            .set_rhs(1);
    return constraint;
}

void add_connectivity_to_pb_model_version_1(PbModel & pb_model, const Graph & g0)
{
    // base case
    for (int u=0; u<g0.n; u++) {
        for (int w=0; w<g0.n; w++) {
            if (u == w) {
                for (int part=1; part<=2; part++) {
                    InequalityGeq constraint = connectedness_base_constraint_1v(0, u, g0, part);
                    if (part == 1) {
                        constraint.set_comment("Base connectedness constraint for vertex " + std::to_string(u));
                    }
                    pb_model.add_constraint(constraint);
                }
            } else if (g0.adjmat[u][w]) {
                for (int part=1; part<=3; part++) {
                    InequalityGeq constraint = connectedness_base_constraint_2vv(u, w, g0, 0, part);
                    if (part == 1) {
                        constraint.set_comment("Base connectedness constraint for vertices " + std::to_string(u) + " and " + std::to_string(w));
                    }
                    pb_model.add_constraint(constraint);
                }
            } else {
                InequalityGeq constraint;
                constraint.add_term({-1, false, c2_var_name(0, u, w)});
                constraint.set_rhs(0);
                constraint.set_comment("Base case non-connectedness constraint for vertices " + std::to_string(u) + " and " + std::to_string(w));
                pb_model.add_constraint(constraint);
            }
        }
    }

    // inductive case
    int K = 0;
    int two_to_K = 1;
    while (two_to_K < g0.n - 1) {
        ++K;
        two_to_K *= 2;
    }
    for (int k=1; k<=K; k++) {
        for (int u=0; u<g0.n; u++) {
            for (int part=1; part<=2; part++) {
                InequalityGeq constraint = connectedness_base_constraint_1v(k, u, g0, part);
                if (part == 1) {
                    constraint.set_comment("Base connectedness constraint for vertex " + std::to_string(u));
                }
                pb_model.add_constraint(constraint);
            }
            for (int w=0; w<g0.n; w++) {
                if (u == w) {
                    continue;
                }
                for (int v=0; v<g0.n; v++) {
                    for (int part=1; part<=3; part++) {
                        InequalityGeq constraint = connectedness_inductive_case_a(k, u, v, w, g0, part);
                        if (part == 1) {
                            constraint.set_comment("Inductive connectedness constraint part a for k=" + std::to_string(k)
                                    + " u=" + std::to_string(u)
                                    + " v=" + std::to_string(v)
                                    + " w=" + std::to_string(w));
                        }
                        pb_model.add_constraint(constraint);
                    }
                }
                InequalityGeq constraint = connectedness_inductive_case_b_part_1(k, u, w, g0, false);
                constraint.set_comment("Inductive connectedness constraint part b for k=" + std::to_string(k)
                        + " u=" + std::to_string(u)
                        + " w=" + std::to_string(w));
                pb_model.add_constraint(constraint);
                for (int v=0; v<g0.n; v++) {
                    InequalityGeq constraint = connectedness_inductive_case_b_part_2(k, u, v, w, g0);
                    pb_model.add_constraint(constraint);
                }
            }
        }
    }

    // connectivity constraints
    for (int p=0; p<g0.n; p++) {
        for (int q=0; q<g0.n; q++) {
            if (p == q) {
                continue;
            }
            InequalityGeq constraint = connectedness_constraint(K, p, q);
            constraint.set_comment("Connectedness constraint p=" + std::to_string(p)
                    + " q=" + std::to_string(q));
            pb_model.add_constraint(constraint);
        }
    }
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
                for (int part=1; part<=3; part++) {
                    InequalityGeq constraint = connectedness_base_constraint_2vv(u, w, g0, 0, part);
                    if (part == 1) {
                        constraint.set_comment("Base connectedness constraint for vertices " + std::to_string(u) + " and " + std::to_string(w));
                    }
                    pb_model.add_constraint(constraint);
                }
            } else {
                InequalityGeq constraint;
                constraint.add_term({-1, false, c2_var_name(0, u, w)});
                constraint.set_rhs(0);
                constraint.set_comment("Base case non-connectedness constraint for vertices " + std::to_string(u) + " and " + std::to_string(w));
                pb_model.add_constraint(constraint);
            }
        }
    }

    // inductive case
    int K = 0;
    int two_to_K = 1;
    while (two_to_K < g0.n - 1) {
        ++K;
        two_to_K *= 2;
    }
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
                    for (int part=1; part<=3; part++) {
                        InequalityGeq constraint = connectedness_inductive_case_a(k, u, v, w, g0, part);
                        if (part == 1) {
                            constraint.set_comment("Inductive connectedness constraint part a for k=" + std::to_string(k)
                                    + " u=" + std::to_string(u)
                                    + " v=" + std::to_string(v)
                                    + " w=" + std::to_string(w));
                        }
                        pb_model.add_constraint(constraint);
                    }
                }
                InequalityGeq constraint = connectedness_inductive_case_b_part_1(k, u, w, g0, true);
                constraint.add_term({1, false, c2_var_name(k-1, u, w)});
                constraint.set_comment("Inductive connectedness constraint part b for k=" + std::to_string(k)
                        + " u=" + std::to_string(u)
                        + " w=" + std::to_string(w));
                pb_model.add_constraint(constraint);
                for (int v=0; v<g0.n; v++) {
                    if (u == v || w == v) {
                        continue;
                    }
                    InequalityGeq constraint = connectedness_inductive_case_b_part_2(k, u, v, w, g0);
                    pb_model.add_constraint(constraint);
                }
                InequalityGeq extra_constraint {};
                extra_constraint.add_term({1, false, c2_var_name(k, u, w)});
                extra_constraint.add_term({1, true, c2_var_name(k-1, u, w)});
                extra_constraint.set_rhs(1);
                pb_model.add_constraint(extra_constraint);
            }
        }
    }

    // connectivity constraints
    for (int p=0; p<g0.n; p++) {
        for (int q=0; q<g0.n; q++) {
            if (p == q) {
                continue;
            }
            InequalityGeq constraint = connectedness_constraint(K, p, q);
            constraint.set_comment("Connectedness constraint p=" + std::to_string(p)
                    + " q=" + std::to_string(q));
            pb_model.add_constraint(constraint);
        }
    }
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
                for (int part=1; part<=3; part++) {
                    InequalityGeq constraint = connectedness_base_constraint_2vv(u, w, g0, 1, part);
                    if (part == 1) {
                        constraint.set_comment("Base connectedness constraint for vertices " + std::to_string(u) + " and " + std::to_string(w));
                    }
                    pb_model.add_constraint(constraint);
                }
            } else {
                InequalityGeq constraint;
                constraint.add_term({-1, false, c2_var_name(1, u, w)});
                constraint.set_rhs(0);
                constraint.set_comment("Base case non-connectedness constraint for vertices " + std::to_string(u) + " and " + std::to_string(w));
                pb_model.add_constraint(constraint);
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
                    for (int part=1; part<=3; part++) {
                        InequalityGeq constraint = connectedness_inductive_case_a_version_3(k, u, v, w, g0, part);
                        if (part == 1) {
                            constraint.set_comment("Inductive connectedness constraint part a for k=" + std::to_string(k)
                                    + " u=" + std::to_string(u)
                                    + " v=" + std::to_string(v)
                                    + " w=" + std::to_string(w));
                        }
                        pb_model.add_constraint(constraint);
                    }
                }
                InequalityGeq constraint = connectedness_inductive_case_b_version_3_part_1(k, u, w, g0);
                constraint.add_term({1, false, c2_var_name(k-1, u, w)});
                constraint.set_comment("Inductive connectedness constraint part b for k=" + std::to_string(k)
                        + " u=" + std::to_string(u)
                        + " w=" + std::to_string(w));
                pb_model.add_constraint(constraint);
                for (int v=0; v<g0.n; v++) {
                    if (u == v || !g0.adjmat[v][w]) {
                        continue;
                    }
                    InequalityGeq constraint = connectedness_inductive_case_b_version_3_part_2(k, u, v, w, g0);
                    pb_model.add_constraint(constraint);
                }
                InequalityGeq extra_constraint {};
                extra_constraint.add_term({1, false, c2_var_name(k, u, w)});
                extra_constraint.add_term({1, true, c2_var_name(k-1, u, w)});
                extra_constraint.set_rhs(1);
                pb_model.add_constraint(extra_constraint);
            }
        }
    }

    // connectivity constraints
    for (int p=0; p<g0.n; p++) {
        for (int q=0; q<g0.n; q++) {
            if (p == q) {
                continue;
            }
            InequalityGeq constraint = connectedness_constraint(K, p, q);
            constraint.set_comment("Connectedness constraint p=" + std::to_string(p)
                    + " q=" + std::to_string(q));
            pb_model.add_constraint(constraint);
        }
    }
}

PbModel build_pb_model(const Graph & g0, const Graph & g1, int target_subgraph_size,
        vector<int> & mapping_constraint_nums, vector<int> & injectivity_constraint_nums)
{
    PbModel pb_model;

    if (target_subgraph_size == -1) {
        // optimisation version
        for (int p=0; p<g0.n; p++) {
            for (int t=0; t<g0.n; t++) {
                pb_model.add_objective_term({1, true, assignment_var_name(p, t)});
            }
        }
    } else {
        pb_model.add_constraint(objective_constraint(g0.n, g1.n, target_subgraph_size)
                .set_comment("Objective"));
    }

    for (int i=0; i<g0.n; i++) {
        InequalityGeq constraint = mapping_constraint(i, g1.n, true);
        constraint.set_comment("Mapping constraint for pattern vertex "
                + std::to_string(i));
        pb_model.add_constraint(constraint);
        pb_model.add_constraint(mapping_constraint(i, g1.n, false));
        mapping_constraint_nums[i] = pb_model.last_constraint_number();
    }
    for (int i=0; i<g1.n; i++) {
        InequalityGeq constraint = injectivity_constraint(i, g0.n);
        constraint.set_comment("Injectivity constraint for target vertex "
                + std::to_string(i));
        pb_model.add_constraint(constraint);
        injectivity_constraint_nums[i] = pb_model.last_constraint_number();
    }
    for (int p=0; p<g0.n; p++) {
        for (int q=0; q<g0.n; q++) {
            if (q==p)
                continue;
            for (int t=0; t<g1.n; t++) {
                InequalityGeq constraint = adjacency_constraint(p, q, t, g0, g1);
                if (t == 0) {
                    constraint.set_comment("Adjacency constraints for pattern edge or non-edge "
                            + std::to_string(p) + "," + std::to_string(q));
                }
                pb_model.add_constraint(constraint);
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

unsigned long long nodes{ 0 };
unsigned long long solution_count{ 0 };

/*******************************************************************************
                                 MCS functions
*******************************************************************************/

struct VtxPair {
    int v;
    int w;
    VtxPair(int v, int w): v(v), w(w) {}
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
    cout << "Nodes: " << nodes << std::endl;
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
        int len = arguments.heuristic == min_max ?
                std::max(bd.left_len, bd.right_len) :
                bd.left_len * bd.right_len;
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

// multiway is for directed and/or labelled graphs
vector<Bidomain> filter_domains(const vector<Bidomain> & d, vector<int> & left,
        vector<int> & right, const Graph & g0, const Graph & g1, int v, int w,
        bool multiway)
{
    vector<Bidomain> new_d;
    new_d.reserve(d.size());
    for (const Bidomain &old_bd : d) {
        int l = old_bd.l;
        int r = old_bd.r;
        // After these two partitions, left_len and right_len are the lengths of the
        // arrays of vertices with edges from v or w (int the directed case, edges
        // either from or to v or w)
        int left_len = partition(left, l, old_bd.left_len, g0.adjmat[v]);
        int right_len = partition(right, r, old_bd.right_len, g1.adjmat[w]);
        int left_len_noedge = old_bd.left_len - left_len;
        int right_len_noedge = old_bd.right_len - right_len;
        if (left_len_noedge && right_len_noedge)
            new_d.push_back({l+left_len, r+right_len, left_len_noedge, right_len_noedge, old_bd.is_adjacent});
        if (multiway && left_len && right_len) {
            auto& adjrow_v = g0.adjmat[v];
            auto& adjrow_w = g1.adjmat[w];
            auto l_begin = std::begin(left) + l;
            auto r_begin = std::begin(right) + r;
            std::sort(l_begin, l_begin+left_len, [&](int a, int b)
                    { return adjrow_v[a] < adjrow_v[b]; });
            std::sort(r_begin, r_begin+right_len, [&](int a, int b)
                    { return adjrow_w[a] < adjrow_w[b]; });
            int l_top = l + left_len;
            int r_top = r + right_len;
            while (l<l_top && r<r_top) {
                unsigned int left_label = adjrow_v[left[l]];
                unsigned int right_label = adjrow_w[right[r]];
                if (left_label < right_label) {
                    l++;
                } else if (left_label > right_label) {
                    r++;
                } else {
                    int lmin = l;
                    int rmin = r;
                    do { l++; } while (l<l_top && adjrow_v[left[l]]==left_label);
                    do { r++; } while (r<r_top && adjrow_w[right[r]]==left_label);
                    new_d.push_back({lmin, rmin, l-lmin, r-rmin, true});
                }
            }
        } else if (left_len && right_len) {
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

void write_backtracking_constraint(const vector<Term> & decisions, std::ostream & proof_stream)
{
    proof_stream << "u ";
    InequalityGeq constraint {};
    for (auto & decision : decisions) {
        constraint.add_term(decision);
    }
    constraint.set_rhs(-decisions.size() + 1);
    proof_stream << constraint.to_string();
    proof_stream << std::endl;
}

void write_bound_constraint(
        const vector<Bidomain> & domains,
        vector<int> & left,
        vector<int> & right,
        const vector<int> & mapping_constraint_nums,
        const vector<int> & injectivity_constraint_nums,
        std::ostream & proof_stream,
        const vector<int> & vtx_name0,
        const vector<int> & vtx_name1,
        int & last_constraint_num)
{
    if (domains.empty()) {
        return;
    }
    vector<int> constraint_nums;
    for (const Bidomain &bd : domains) {
        if (bd.left_len <= bd.right_len) {
            for (int i=0; i<bd.left_len; i++) {
                int v_in_sorted_graph = left[bd.l+i];
                int v_in_original_graph = vtx_name0[v_in_sorted_graph];
                constraint_nums.push_back(mapping_constraint_nums[v_in_original_graph]);
            }
        } else {
            for (int i=0; i<bd.right_len; i++) {
                int v_in_sorted_graph = right[bd.r+i];
                int v_in_original_graph = vtx_name1[v_in_sorted_graph];
                constraint_nums.push_back(injectivity_constraint_nums[v_in_original_graph]);
            }
        }
    }
    proof_stream << "p ";
    bool first = true;
    for (int constraint_num : constraint_nums) {
        proof_stream << constraint_num << " ";
        if (!first) {
            proof_stream << "+ ";
        }
        first = false;
    }
    proof_stream << number_of_most_recent_objective_constraint << " + 0";
    proof_stream << std::endl;
    ++last_constraint_num;
}

void write_solution(std::ostream & proof_stream,
        const vector<VtxPair> & current,
        const Graph & pattern_g,
        const Graph & target_g,
        const vector<int> & vtx_name0,
        const vector<int> & vtx_name1,
        int & last_constraint_num,
        char prefix)
{
    vector<vector<bool>> assignment_made(pattern_g.n, vector<bool>(target_g.n));
    for (auto assignment : current) {
        int v = vtx_name0[assignment.v];
        int w = vtx_name1[assignment.w];
        assignment_made[v][w] = true;
    }
    proof_stream << prefix;
    for (int v=0; v<pattern_g.n; v++) {
        for (int w=0; w<pattern_g.n; w++) {
            if (assignment_made[v][w]) {
                proof_stream << " " << assignment_var_name(v, w);
            } else {
                proof_stream << " ~" << assignment_var_name(v, w);
            }
        }
    }
    proof_stream << std::endl;
    ++last_constraint_num;
    if (prefix == 'o')
        number_of_most_recent_objective_constraint = last_constraint_num;
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
        std::optional<std::ofstream> & proof_stream,
        const vector<int> & vtx_name0, const vector<int> & vtx_name1,
        const vector<int> & mapping_constraint_nums, const vector<int> & injectivity_constraint_nums,
        int & last_constraint_num, vector<Term> & decisions)
{
    int decisions_len_at_start_of_solve = decisions.size();

    if (abort_due_to_timeout)
        return;

    if (arguments.verbose) {
        show(current, domains, left, right);
    }
    nodes++;

    if (current.size() > incumbent.size()) {
        incumbent = current;
        if (!arguments.quiet) cout << "Incumbent size: " << incumbent.size() << endl;
        if (arguments.decision_size==-1 && proof_stream) {
            proof_level_set(0, proof_stream.value());
            write_solution(proof_stream.value(), current, g0, g1, vtx_name0, vtx_name1, last_constraint_num, 'o');
            proof_level_set(current.size(), proof_stream.value());
        }
    }

    unsigned int bound = current.size() + calc_bound(domains);
    if ((!arguments.count_solutions && bound <= incumbent.size()) || bound < matching_size_goal) {
        if (proof_stream) {
            write_bound_constraint(domains, left, right, mapping_constraint_nums,
                    injectivity_constraint_nums, proof_stream.value(), vtx_name0, vtx_name1,
                    last_constraint_num);
        }
        return;
    }

    if ((arguments.big_first || (arguments.decision_size != -1 && !arguments.count_solutions)) && incumbent.size()==matching_size_goal)
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

        auto new_domains = filter_domains(domains, left, right, g0, g1, v, w,
                arguments.directed || arguments.edge_labelled);
        current.push_back(VtxPair(v, w));
//        if (proof_stream)
//            proof_stream << "* decision " << v << " " << w << std::endl;
        if (proof_stream)
            decisions.push_back({-1, false, assignment_var_name(vtx_name0[v], vtx_name1[w])});
        if (proof_stream)
            proof_level_set(current.size(), proof_stream.value());

        if (arguments.count_solutions && current.size() >= matching_size_goal) {
            ++solution_count;
            if (proof_stream) {
                write_solution(proof_stream.value(), current, g0, g1, vtx_name0, vtx_name1, last_constraint_num, 'v');
            }
        }

        solve(g0, g1, incumbent, current, new_domains, left, right, matching_size_goal,
                proof_stream, vtx_name0, vtx_name1,
                mapping_constraint_nums, injectivity_constraint_nums, last_constraint_num,
                decisions);
        if (arguments.decision_size != -1 && !arguments.count_solutions && incumbent.size()==matching_size_goal) {
            return;
        }
        current.pop_back();
        if (proof_stream)
            proof_level_set(current.size(), proof_stream.value());
        if (proof_stream) {
            write_backtracking_constraint(decisions, proof_stream.value());
            ++last_constraint_num;
        }
//        if (proof_stream)
//            proof_stream << "* undo decision " << v << " " << w << std::endl;
        if (proof_stream)
            proof_level_wipe(current.size() + 1, proof_stream.value());
        if (proof_stream)
            decisions.pop_back();
//        if (proof_stream)
//            proof_stream << "* decision not" << v << " " << w << std::endl;
        if (proof_stream)
            decisions.push_back({-1, true, assignment_var_name(vtx_name0[v], vtx_name1[w])});
    }
    bd.right_len++;
    if (bd.left_len == 0)
        remove_bidomain(domains, bd_idx);
    if (proof_stream) {
        decisions.resize(decisions_len_at_start_of_solve);
        decisions.push_back({-1, false, assignment_var_name(vtx_name0[v], -1)});
    }
    solve(g0, g1, incumbent, current, domains, left, right, matching_size_goal,
            proof_stream, vtx_name0, vtx_name1,
            mapping_constraint_nums, injectivity_constraint_nums, last_constraint_num,
            decisions);
//    if (proof_stream) {
//        write_backtracking_constraint(decisions, proof_stream);
//        ++last_constraint_num;
//    }
    decisions.resize(decisions_len_at_start_of_solve);
}

vector<VtxPair> mcs(const Graph & g0, const Graph & g1,
            const vector<int> & vtx_name0, const vector<int> & vtx_name1,
            int last_constraint_num,
            const vector<int> & mapping_constraint_nums,
            const vector<int> & injectivity_constraint_nums) {
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
    vector<Term> decisions;

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

    if (arguments.decision_size != -1) {
        if (arguments.count_solutions && 0 == arguments.decision_size) {
            ++solution_count;
            if (proof_stream) {
                write_solution(proof_stream.value(), current, g0, g1, vtx_name0, vtx_name1, last_constraint_num, 'v');
            }
        }
        solve(g0, g1, incumbent, current, domains, left, right, arguments.decision_size, proof_stream,
                    vtx_name0, vtx_name1, mapping_constraint_nums, injectivity_constraint_nums,
                    last_constraint_num, decisions);
    } else if (arguments.big_first) {
        for (int k=0; k<g0.n; k++) {
            unsigned int goal = g0.n - k;
            auto left_copy = left;
            auto right_copy = right;
            auto domains_copy = domains;
            vector<VtxPair> current;
            solve(g0, g1, incumbent, current, domains_copy, left_copy, right_copy, goal, proof_stream,
                    vtx_name0, vtx_name1, {}, {}, last_constraint_num, decisions);
            if (incumbent.size() == goal || abort_due_to_timeout) break;
            if (!arguments.quiet) cout << "Upper bound: " << goal-1 << std::endl;
        }
    } else {
        auto domains_copy = domains;
        solve(g0, g1, incumbent, current, domains_copy, left, right, 1, proof_stream,
                vtx_name0, vtx_name1, mapping_constraint_nums, injectivity_constraint_nums, last_constraint_num, decisions);
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
    for (int v=0; v<g.n; v++) {
        for (int w=0; w<g.n; w++) {
            unsigned int mask = 0xFFFFu;
            if (g.adjmat[v][w] & mask) degree[v]++;
            if (g.adjmat[v][w] & ~mask) degree[v]++;  // inward edge, in directed case
        }
    }
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
    struct Graph g0 = readGraph(arguments.filename1, format, arguments.directed,
            arguments.edge_labelled, arguments.vertex_labelled);
    struct Graph g1 = readGraph(arguments.filename2, format, arguments.directed,
            arguments.edge_labelled, arguments.vertex_labelled);

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
        if (arguments.big_first) {
            std::cerr << "OPB output is currently only supported for the decision problem and BnB." << std::endl;
            exit(1);
        }
        std::ofstream opb_stream(arguments.opb_filename);
        auto pb_model = build_pb_model(g0, g1, arguments.decision_size,
                mapping_constraint_nums, injectivity_constraint_nums);
        pb_model.output_model(opb_stream);
        last_constraint_num = pb_model.last_constraint_number();
    }

    vector<int> g0_deg = calculate_degrees(g0);
    vector<int> g1_deg = calculate_degrees(g1);

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
    cout << "Nodes:                      " << nodes << endl;
    cout << "CPU time (ms):              " << time_elapsed << endl;
    if (aborted)
        cout << "TIMEOUT" << endl;
}
