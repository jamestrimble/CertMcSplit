#ifndef PROOF_LOGGING_H
#define PROOF_LOGGING_H

#include <iostream>
#include <set>
#include <string>
#include <vector>

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

inline Term operator*(int coef, Literal literal)
{
    return Term(coef, literal);
}

struct InequalityGeq
{
    std::vector<Term> lhs;
    int rhs = 0;

    InequalityGeq() {}
    InequalityGeq(std::vector<Term> lhs, int rhs) : lhs(lhs), rhs(rhs) {}

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
    std::vector<InequalityGeq>::size_type position;
};

class PbModel
{
    std::vector<InequalityGeq> constraints;
    std::vector<OpbComment> comments;
    std::vector<Term> objective;  // no objective if this is empty

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

        std::vector<InequalityGeq>::size_type constraint_num = 0;
        std::vector<OpbComment>::size_type pos_in_comments = 0;
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

#endif
