#include "Halide.h"

#include <fstream>

using namespace Halide;
using namespace Halide::Internal;

using std::string;
using std::vector;
using std::map;
using std::set;
using std::pair;
using std::ostringstream;
using std::tuple;

// Convert from a Halide Expr to SMT2 to pass to z3
string expr_to_smt2(const Expr &e) {
    class ExprToSMT2 : public IRVisitor {
    public:
        std::ostringstream formula;

    protected:

        void visit(const IntImm *imm) override {
            formula << imm->value;
        }

        void visit(const UIntImm *imm) override {
            formula << imm->value;
        }

        void visit(const FloatImm *imm) override {
            formula << imm->value;
        }

        void visit(const StringImm *imm) override {
            formula << imm->value;
        }

        void visit(const Variable *var) override {
            formula << var->name;
        }

        void visit(const Add *op) override {
            formula << "(+ ";
            op->a.accept(this);
            formula << " ";
            op->b.accept(this);
            formula << ")";
        }

        void visit(const Sub *op) override {
            formula << "(- ";
            op->a.accept(this);
            formula << " ";
            op->b.accept(this);
            formula << ")";
        }

        void visit(const Mul *op) override {
            formula << "(* ";
            op->a.accept(this);
            formula << " ";
            op->b.accept(this);
            formula << ")";
        }

        void visit(const Div *op) override {
            formula << "(div ";
            op->a.accept(this);
            formula << " ";
            op->b.accept(this);
            formula << ")";
        }

        void visit(const Mod *op) override {
            formula << "(mod ";
            op->a.accept(this);
            formula << " ";
            op->b.accept(this);
            formula << ")";
        }

        void visit(const Min *op) override {
            formula << "(my_min ";
            op->a.accept(this);
            formula << " ";
            op->b.accept(this);
            formula << ")";
        }

        void visit(const Max *op) override {
            formula << "(my_max ";
            op->a.accept(this);
            formula << " ";
            op->b.accept(this);
            formula << ")";
        }

        void visit(const EQ *op) override {
            formula << "(= ";
            op->a.accept(this);
            formula << " ";
            op->b.accept(this);
            formula << ")";
        }

        void visit(const NE *op) override {
            formula << "(not (= ";
            op->a.accept(this);
            formula << " ";
            op->b.accept(this);
            formula << "))";
        }

        void visit(const LT *op) override {
            formula << "(< ";
            op->a.accept(this);
            formula << " ";
            op->b.accept(this);
            formula << ")";
        }

        void visit(const LE *op) override {
            formula << "(<= ";
            op->a.accept(this);
            formula << " ";
            op->b.accept(this);
            formula << ")";
        }

        void visit(const GT *op) override {
            formula << "(> ";
            op->a.accept(this);
            formula << " ";
            op->b.accept(this);
            formula << ")";
        }

        void visit(const GE *op) override {
            formula << "(>= ";
            op->a.accept(this);
            formula << " ";
            op->b.accept(this);
            formula << ")";
        }

        void visit(const And *op) override {
            formula << "(and ";
            op->a.accept(this);
            formula << " ";
            op->b.accept(this);
            formula << ")";
        }

        void visit(const Or *op) override {
            formula << "(or ";
            op->a.accept(this);
            formula << " ";
            op->b.accept(this);
            formula << ")";
        }

        void visit(const Not *op) override {
            formula << "(not ";
            op->a.accept(this);
            formula << ")";
        }

        void visit(const Select *op) override {
            formula << "(ite ";
            op->condition.accept(this);
            formula << " ";
            op->true_value.accept(this);
            formula << " ";
            op->false_value.accept(this);
            formula << ")";
        }

        void visit(const Cast *op) override {
            assert(false && "unhandled");
        }

        void visit(const Ramp *op) override {
            /*
            Expr equiv = op->base + lane_var * op->stride;
            equiv.accept(this);
            */
            assert(false && "unhandled");
        }

        void visit(const Let *op) override {
            formula << "(let ((" << op->name << " ";
            op->value.accept(this);
            formula << ")) ";
            op->body.accept(this);
            formula << ")";
        }

        void visit(const Broadcast *op) override {
            op->value.accept(this);
        }

    } to_smt2;

    e.accept(&to_smt2);
    return to_smt2.formula.str();
}

// Make an expression which can act as any other small integer expression in
// the given leaf terms, depending on the values of the integer opcodes. Not all possible programs are valid (e.g. due to type errors), so also returns an Expr on the inputs opcodes that encodes whether or not the program is well-formed.
pair<Expr, Expr> interpreter_expr(vector<Expr> terms, vector<Expr> opcodes) {
    // Each opcode is an enum identifying the op, followed by the indices of the two args.
    assert(opcodes.size() % 3 == 0);

    Expr program_is_valid = const_true();

    for (size_t i = 0; i < opcodes.size(); i += 3) {
        Expr op = opcodes[i];
        Expr arg1_idx = opcodes[i+1];
        Expr arg2_idx = opcodes[i+2];

        // Get the args using a select tree. args are either the index of an existing value, or some constant.
        Expr arg1 = arg1_idx, arg2 = arg2_idx;
        for (size_t j = 0; j < terms.size(); j++) {
            arg1 = select(arg1_idx == (int)j, terms[j], arg1);
            arg2 = select(arg2_idx == (int)j, terms[j], arg2);
        }
        int s = (int)terms.size();
        arg1 = select(arg1_idx >= s, arg1_idx - s, arg1);
        arg2 = select(arg2_idx >= s, arg2_idx - s, arg2);

        // Perform the op.
        Expr result = arg1; // By default it's just equal to the first operand. This covers constants too.
        result = select(op == 1, arg1 + arg2, result);
        result = select(op == 2, arg1 - arg2, result);
        result = select(op == 3, arg1 * arg2, result);
        result = select(op == 4, select(arg1 < arg2, 1, 0), result);
        result = select(op == 5, select(arg1 <= arg2, 1, 0), result);
        result = select(op == 6, select(arg1 == arg2, 1, 0), result);
        result = select(op == 7, select(arg1 != arg2, 1, 0), result);
        result = select(op == 8, min(arg1, arg2), result);
        result = select(op == 9, max(arg1, arg2), result);

        // Type-check it
        program_is_valid = program_is_valid && op < 10 && op >= 0;

        // TODO: in parallel compute the op histogram, or at least the leading op strength

        terms.push_back(result);
    }

    return {terms.back(), program_is_valid};
}

// Returns the value of the predicate, whether the opcodes are valid,
// and whether or not the opcodes produce a predicate that's simpler
// (preferable to) some reference predicate.
tuple<Expr, Expr, Expr> predicate_expr(vector<Expr> lhs,
                                       vector<Expr> rhs,
                                       vector<Expr> opcodes,
                                       vector<Expr> opcodes_ref,
                                       map<string, Expr> *binding) {

    // For now we use explicit enumeration of combinations of
    // plausible constraints. We set up the list so that if A => B
    // then B occurs before A in the list. General possible things
    // come before specific things.

    // The values vector is sorted by complexity of the expression.

    vector<Expr> values, constraints;
    constraints.push_back(const_true());

    for (auto e1 : lhs) {
        values.push_back(e1);
        constraints.push_back(e1 != 0);
        constraints.push_back(e1 >= 0);
        constraints.push_back(e1 <= 0);
        constraints.push_back(e1 > 0);
        constraints.push_back(e1 < 0);
        constraints.push_back(e1 == 0);
    }

    for (auto e1 : lhs) {
        bool commutative_ok = true;
        for (auto e2 : lhs) {
            if (e1.same_as(e2)) {
                commutative_ok = false;
                continue;
            }
            constraints.push_back(e1 <= e2 + 1);
            constraints.push_back(e1 <= e2);
            constraints.push_back(e1 < e2);
            constraints.push_back(e1 < e2 - 1);

            constraints.push_back(e1 % e2 == 0 && e2 != 0);
            constraints.push_back(e1 / e2 == 0 && e2 != 0);
            constraints.push_back(e1 == e2 - 1);
            constraints.push_back(e1 == e2 + 1);

            constraints.push_back(e1 == e2);

            if (commutative_ok) {
                constraints.push_back(e1 + e2 <= 0);
                constraints.push_back(e1 + e2 >= 0);
                constraints.push_back(e1 + e2 < 0);
                constraints.push_back(e1 + e2 > 0);
                constraints.push_back(e1 + e2 == 0);
                values.push_back(e1 + e2);
                values.push_back(min(e1, e2));
                values.push_back(max(e1, e2));
            }
            values.push_back(e1 - e2);
            values.push_back(e1 / e2);
            values.push_back((e1 + e2 - 1) / e2);
            values.push_back(e1 % e2);
        }
    }

    values.push_back(-1);
    values.push_back(0);
    values.push_back(1);
    values.push_back(2);

    for (auto e1 : lhs) {
        for (auto e2 : lhs) {
            for (auto e3 : lhs) {
                if (e2.same_as(e2)) break;
                constraints.push_back(e1 == e2 + e3);
            }
        }
    }

    Expr more_general_constraints = const_true();
    Expr same_constraints = const_true();
    for (size_t i = 0; i < rhs.size() + lhs.size(); i++) {
        same_constraints = same_constraints && (opcodes[i] == opcodes_ref[i]);
        more_general_constraints = more_general_constraints && (opcodes[i] <= opcodes_ref[i]);
    }
    Expr strictly_more_general_constraints = !same_constraints && more_general_constraints;

    // Each rhs expr should equal some simple function of the lhs exprs
    Expr result = const_true();
    Expr valid = const_true();

    assert(opcodes.size() == lhs.size() + rhs.size());

    for (size_t i = 0; i < rhs.size(); i++) {
        Expr r = rhs[i];
        Expr val = values[0];
        Expr cond = values[0];
        Expr op = opcodes[i];
        vector<pair<Expr, Expr>> divs, mods;
        for (int j = 1; j < (int)values.size(); j++) {
            Expr c = (op == j);
            val = select(c, values[j], val);
            if (values[j].as<Div>()) {
                divs.emplace_back(c, values[j]);
            } else if (values[j].as<Mod>()) {
                mods.emplace_back(c, values[j]);
            } else {
                cond = select(c, values[j], cond);
            }
        }
        cond = (r == cond);
        // Handle the divs and mods with implicit conditions instead.
        for (auto p : divs) {
            const Div *d = p.second.as<Div>();
            Expr numerator = d->a;
            Expr denominator = d->b;
            assert(d);
            // We have r == d->a / d->b
            // Or r * d->b + residual == d->a, for some bounded residual
            Expr residual = numerator - r * denominator;
            // Only handle positive divisors for now
            cond = cond || (p.first && (d->b > 0) && residual >= 0 && residual < denominator);
        }
        for (auto p : mods) {
            const Mod *m = p.second.as<Mod>();
            assert(m);
            // We have r == m->a % m->b
            // Or in other words, r + t * m->b == m->a, for some unknown quotient
            Var t(unique_name('t'));

            cond = cond || (p.first && (m->b > 0) && (r + t * m->b == m->a) && (r >= 0) && (r < m->b));
        }

        result = result && cond;
        valid = valid && (op >= 0) && (op < (int)values.size());
        if (const Variable *var = r.as<Variable>()) {
            (*binding)[var->name] = val;
        }
    }

    // We have constraint per LHS expr. If we don't need that many,
    // one of the constraints in the list is "true".
    for (size_t i = 0; i < lhs.size(); i++) {
        Expr c = constraints[0];
        Expr op = opcodes[i + rhs.size()];
        for (int j = 1; j < (int)constraints.size(); j++) {
            c = select(op == j, constraints[j], c);
        }
        result = result && c;
        valid = valid && (op >= 0) && (op < (int)constraints.size());
    }

    return {result, valid, strictly_more_general_constraints};
}

bool is_whitespace(char c) {
    return c == ' '  || c == '\n' || c == '\t';
}

void consume_whitespace(char **cursor, char *end) {
    while (*cursor < end && is_whitespace(**cursor)) {
        (*cursor)++;
    }
}

bool consume(char **cursor, char *end, const char *expected) {
    char *tmp = *cursor;
    while (*tmp == *expected && tmp < end && *expected) {
        tmp++;
        expected++;
    }
    if ((*expected) == 0) {
        *cursor = tmp;
        return true;
    } else {
        return false;
    }
}

void expect(char **cursor, char *end, const char *pattern) {
    if (!consume(cursor, end, pattern)) {
        printf("Parsing failed. Expected %s, got %s\n",
               pattern, *cursor);
        abort();
    }
}

bool check(char **cursor, char *end, const char *pattern) {
    char *tmp_cursor = *cursor;
    return consume(&tmp_cursor, end, pattern);
}

string consume_token(char **cursor, char *end) {
    size_t sz = 0;
    while (*cursor + sz < end &&
           (std::isalnum((*cursor)[sz]) ||
            (*cursor)[sz] == '!' ||
            (*cursor)[sz] == '.' ||
            (*cursor)[sz] == '$' ||
            (*cursor)[sz] == '_')) sz++;
    string result{*cursor, sz};
    *cursor += sz;
    return result;
}

int64_t consume_int(char **cursor, char *end) {
    bool negative = consume(cursor, end, "-");
    int64_t n = 0;
    while (*cursor < end && **cursor >= '0' && **cursor <= '9') {
        n *= 10;
        n += (**cursor - '0');
        (*cursor)++;
    }
    return negative ? -n : n;
}

Expr consume_float(char **cursor, char *end) {
    bool negative = consume(cursor, end, "-");
    int64_t integer_part = consume_int(cursor, end);
    int64_t fractional_part = 0;
    int64_t denom = 1;
    if (consume(cursor, end, ".")) {
        while (*cursor < end && **cursor >= '0' && **cursor <= '9') {
            denom *= 10;
            fractional_part *= 10;
            fractional_part += (**cursor - '0');
            (*cursor)++;
        }
    }
    double d = integer_part + double(fractional_part) / denom;
    if (negative) {
        d = -d;
    }
    if (consume(cursor, end, "h")) {
        return make_const(Float(16), d);
    } else if (consume(cursor, end, "f")) {
        return make_const(Float(32), d);
    } else {
        return make_const(Float(64), d);
    }
}

bool parse_model(char **cursor, char *end, map<string, Expr> *bindings) {
    consume_whitespace(cursor, end);
    if (!consume(cursor, end, "(model")) return false;
    consume_whitespace(cursor, end);
    while (consume(cursor, end, "(define-fun")) {
        consume_whitespace(cursor, end);
        string name = consume_token(cursor, end);
        consume_whitespace(cursor, end);
        if (!consume(cursor, end, "()")) return false;
        consume_whitespace(cursor, end);
        if (consume(cursor, end, "Bool")) {
            // Don't care about this var
            consume_whitespace(cursor, end);
            if (!consume(cursor, end, "true)")) {
                if (!consume(cursor, end, "false)")) return false;
            }
            consume_whitespace(cursor, end);
        } else {
            if (!consume(cursor, end, "Int")) return false;
            consume_whitespace(cursor, end);
            if (consume(cursor, end, "(- ")) {
                string val = consume_token(cursor, end);
                if (!starts_with(name, "z3name!")) {
                    (*bindings)[name] = -std::atoi(val.c_str());
                }
                consume(cursor, end, ")");
            } else {
                string val = consume_token(cursor, end);
                if (!starts_with(name, "z3name!")) {
                    (*bindings)[name] = std::atoi(val.c_str());
                }
            }
            consume_whitespace(cursor, end);
            consume(cursor, end, ")");
            consume_whitespace(cursor, end);
        }
    }
    consume_whitespace(cursor, end);
    if (!consume(cursor, end, ")")) return false;
    return true;
}


class FindVars : public IRVisitor {
    Scope<> lets;

    void visit(const Variable *op) override {
        if (!lets.contains(op->name)) {
            vars.insert(op->name);
        }
    }

    void visit(const Let *op) override {
        op->value.accept(this);
        {
            ScopedBinding<> bind(lets, op->name);
            op->body.accept(this);
        }
    }
public:
    std::set<string> vars;
};

enum Z3Result {
    Sat, Unsat, Unknown
};
// hacked up for my purposes
Z3Result satisfy(string query) {

    TemporaryFile z3_file("query", "z3");
    TemporaryFile z3_output("output", "txt");
    write_entire_file(z3_file.pathname(), &query[0], query.size());

    std::string cmd = "z3 -T:10 " + z3_file.pathname() + " > " + z3_output.pathname();

    int ret = system(cmd.c_str());

    auto result_vec = read_entire_file(z3_output.pathname());
    string result(result_vec.begin(), result_vec.end());

    if (starts_with(result, "unknown") || starts_with(result, "timeout")) {
        std::cout << "z3 produced: " << result << "\n";
        return Unknown;
    }

    if (ret && !starts_with(result, "unsat")) {
        std::cout << "** z3 query failed with exit code " << ret << "\n"
                  << "** query was:\n" << query << "\n"
                  << "** output was:\n" << result << "\n";
        return Unknown;
    }

    if (starts_with(result, "unsat")) {
        return Unsat;
    } else {
        return Sat;
    }
}

Var v0("x"), v1("y"), v2("z"), v3("w"), v4("u"), v5("v5"), v6("v6"), v7("v7"), v8("v8"), v9("v9");
Var v10("v10"), v11("v11"), v12("v12"), v13("v13"), v14("v14"), v15("v15"), v16("v16"), v17("v17"), v18("v18"), v19("v19");
Var v20("v20"), v21("v21"), v22("v22"), v23("v23"), v24("v24"), v25("v25"), v26("v26"), v27("v27"), v28("v28"), v29("v29");

Expr reboolify(const Expr &e) {
    if (e.type().is_bool()) return e;
    // e is an integer expression encoding a bool. We want to convert it back to the bool
    if (const Min *op = e.as<Min>()) {
        return reboolify(op->a) && reboolify(op->b);
    } else if (const Max *op = e.as<Max>()) {
        return reboolify(op->a) || reboolify(op->b);
    } else if (const LE *op = e.as<LE>()) {
        return !reboolify(op->a) || reboolify(op->b);
    } else if (const LT *op = e.as<LT>()) {
        return !reboolify(op->a) && reboolify(op->b);
    } else {
        return e == 1;
    }
}

// Enumerate all possible patterns that would match any portion of the
// given expression.
vector<Expr> all_possible_lhs_patterns(const Expr &e) {
    // Convert the expression to a DAG
    class DAGConverter : public IRMutator {
    public:

        using IRMutator::mutate;

        int current_parent = -1;

        Expr mutate(const Expr &e) override {
            if (building.empty()) {
                int current_id = (int)id_for_expr.size();
                auto it = id_for_expr.emplace(e, current_id);
                bool unseen = it.second;
                current_id = it.first->second;

                if (unseen) {
                    if (expr_for_id.size() < id_for_expr.size()) {
                        expr_for_id.resize(id_for_expr.size());
                        children.resize(id_for_expr.size());
                    }
                    expr_for_id[current_id] = e;
                    int old_parent = current_parent;
                    current_parent = current_id;
                    IRMutator::mutate(e);
                    current_parent = old_parent;
                }

                if (current_parent != -1) {
                    children[current_parent].insert(current_id);
                }

                return e;
            } else {
                // Building a subexpr
                auto it = id_for_expr.find(e);
                assert(it != id_for_expr.end());
                if (building.count(it->second)) {
                    return IRMutator::mutate(e);
                } else {
                    int new_id = (int)renumbering.size();
                    new_id = renumbering.emplace(it->second, new_id).first->second;
                    // We're after end
                    const char *names[] = {"x", "y", "z", "w", "u", "v"};
                    string name = "v" + std::to_string(new_id);
                    if (new_id >= 0 && new_id < 6) {
                        name = names[new_id];
                    }
                    return Variable::make(e.type(), name);
                }
            }
        }

        // Map between exprs and node ids
        map<Expr, int, IRDeepCompare> id_for_expr;
        vector<Expr> expr_for_id;
        // The DAG structure. Every node has outgoing edges (child
        // nodes) and incoming edges (parent nodes).
        vector<set<int>> children;

        // The current expression being built
        set<int> building;
        map<int, int> renumbering;

        bool may_add_to_frontier(const set<int> &rejected, const set<int> &current, int n) {
            if (rejected.count(n)) return false;
            if (current.count(n)) return false;
            if (expr_for_id[n].as<Variable>()) return false;
            return true;
        }

        vector<Expr> result;
        void generate_subgraphs(const set<int> &rejected,
                                const set<int> &current,
                                const set<int> &frontier)  {
            // Pick an arbitrary frontier node to consider
            int v = -1;
            for (auto n : frontier) {
                if (may_add_to_frontier(rejected, current, n)) {
                    v = n;
                    break;
                }
            }

            if (v == -1) {
                if (!current.empty()) {
                    building = current;
                    renumbering.clear();
                    Expr pat = mutate(expr_for_id[*(building.begin())]);
                    // Apply some rejection rules
                    if (building.size() <= 1 || renumbering.size() > 6) {
                        // Too few inner nodes or too many wildcards
                    } else {
                        result.push_back(pat);
                    }
                }
                return;
            }

            const set<int> &ch = children[v];

            set<int> r = rejected, c = current, f = frontier;

            f.erase(v);

            bool must_include = false; //is_const(expr_for_id[v]);

            if (!must_include) {
                // Generate all subgraphs with this frontier node not
                // included (replaced with a variable).
                r.insert(v);

                // std::cout << "Excluding " << expr_for_id[v] << "\n";
                generate_subgraphs(r, c, f);
            }

            // Generate all subgraphs with this frontier node included
            if (must_include || c.size() < 10) { // Max out some number of unique nodes
                c.insert(v);
                for (auto n : ch) {
                    if (may_add_to_frontier(rejected, current, n)) {
                        f.insert(n);
                    }
                }
                // std::cout << "Including " << expr_for_id[v] << "\n";
                generate_subgraphs(rejected, c, f);
            }
        }
    } all_subexprs;

    all_subexprs.mutate(e);

    // Enumerate all sub-dags
    set<int> rejected, current, frontier;
    frontier.insert(0);
    for (int i = 0; i < (int)all_subexprs.children.size(); i++) {
        // Don't consider leaves for roots
        if (all_subexprs.children[i].empty()) continue;
        frontier.insert(i);
        all_subexprs.generate_subgraphs(rejected, current, frontier);
        frontier.clear();
    }

    return all_subexprs.result;
}

bool more_general_than(const Expr &a, const Expr &b, map<string, Expr> &bindings);

template<typename Op>
bool more_general_than(const Expr &a, const Op *b, map<string, Expr> &bindings) {
    map<string, Expr> backup = bindings;
    if (more_general_than(a, b->a, bindings)) {
        return true;
    }
    bindings = backup;

    if (more_general_than(a, b->b, bindings)) {
        return true;
    }
    bindings = backup;

    if (const Op *op_a = a.as<Op>()) {
        return (more_general_than(op_a->a, b->a, bindings) &&
                more_general_than(op_a->b, b->b, bindings));
    }
    return false;

}

bool more_general_than(const Expr &a, const Expr &b, map<string, Expr> &bindings) {
    if (const Variable *var = a.as<Variable>()) {
        const Variable *var_b = b.as<Variable>();
        auto it = bindings.find(var->name);
        if (it != bindings.end()) {
            return equal(it->second, b);
        } else {
            bool const_wild = var->name[0] == 'c';
            bool b_const_wild = var_b && (var_b->name[0] == 'c');
            bool b_const = is_const(b);
            bool may_bind = !const_wild || (const_wild && (b_const_wild || b_const));
            if (may_bind) {
                bindings[var->name] = b;
                return true;
            } else {
                return false;
            }
        }
    }

    if (const Min *op = b.as<Min>()) {
        return more_general_than(a, op, bindings);
    }

    if (const Min *op = b.as<Min>()) {
        return more_general_than(a, op, bindings);
    }

    if (const Max *op = b.as<Max>()) {
        return more_general_than(a, op, bindings);
    }

    if (const Add *op = b.as<Add>()) {
        return more_general_than(a, op, bindings);
    }

    if (const Sub *op = b.as<Sub>()) {
        return more_general_than(a, op, bindings);
    }

    if (const Mul *op = b.as<Mul>()) {
        return more_general_than(a, op, bindings);
    }

    if (const Div *op = b.as<Div>()) {
        return more_general_than(a, op, bindings);
    }

    if (const LE *op = b.as<LE>()) {
        return more_general_than(a, op, bindings);
    }

    if (const LT *op = b.as<LT>()) {
        return more_general_than(a, op, bindings);
    }

    if (const EQ *op = b.as<EQ>()) {
        return more_general_than(a, op, bindings);
    }

    if (const NE *op = b.as<NE>()) {
        return more_general_than(a, op, bindings);
    }

    if (const Not *op = b.as<Not>()) {
        map<string, Expr> backup = bindings;
        if (more_general_than(a, op->a, bindings)) {
            return true;
        }
        bindings = backup;

        const Not *op_a = a.as<Not>();
        return (op_a &&
                more_general_than(op_a->a, op->a, bindings));
    }

    if (const Select *op = b.as<Select>()) {
        map<string, Expr> backup = bindings;
        if (more_general_than(a, op->condition, bindings)) {
            return true;
        }
        bindings = backup;

        if (more_general_than(a, op->true_value, bindings)) {
            return true;
        }
        bindings = backup;

        if (more_general_than(a, op->false_value, bindings)) {
            return true;
        }
        bindings = backup;

        const Select *op_a = a.as<Select>();
        return (op_a &&
                more_general_than(op_a->condition, op->condition, bindings) &&
                more_general_than(op_a->true_value, op->true_value, bindings) &&
                more_general_than(op_a->false_value, op->false_value, bindings));
    }

    return false;
}

bool more_general_than(const Expr &a, const Expr &b) {
    map<string, Expr> bindings;
    return more_general_than(a, b, bindings);
}

class CountOps : public IRGraphVisitor {
    using IRGraphVisitor::visit;
    using IRGraphVisitor::include;

    void visit(const Variable *op) override {
        if (op->type != Int(32)) {
            has_unsupported_ir = true;
        } else if (vars_used.count(op->name)) {
            has_repeated_var = true;
        } else {
            vars_used.insert(op->name);
        }
    }

    void visit(const Div *op) override {
        has_div_mod = true;
    }

    void visit(const Mod *op) override {
        has_div_mod = true;
    }

    void visit(const Call *op) override {
        has_unsupported_ir = true;
    }

    void visit(const Cast *op) override {
        has_unsupported_ir = true;
    }

    void visit(const Load *op) override {
        has_unsupported_ir = true;
    }

    set<Expr, IRDeepCompare> unique_exprs;

public:

    void include(const Expr &e) override {
        if (is_const(e)) {
            num_constants++;
        } else {
            unique_exprs.insert(e);
            IRGraphVisitor::include(e);
        }
    }

    int count() {
        return unique_exprs.size() - (int)vars_used.size();
    }

    int num_constants = 0;

    bool has_div_mod = false;
    bool has_unsupported_ir = false;
    bool has_repeated_var = false;
    set<string> vars_used;
};

std::ostream &operator<<(std::ostream &s, IRNodeType t) {
    switch(t) {
    case IRNodeType::IntImm: return (s << "IntImm");
    case IRNodeType::UIntImm: return (s << "UIntImm");
    case IRNodeType::FloatImm: return (s << "FloatImm");
    case IRNodeType::StringImm: return (s << "StringImm");
    case IRNodeType::Broadcast: return (s << "Broadcast");
    case IRNodeType::Cast: return (s << "Cast");
    case IRNodeType::Variable: return (s << "Variable");
    case IRNodeType::Add: return (s << "Add");
    case IRNodeType::Sub: return (s << "Sub");
    case IRNodeType::Mod: return (s << "Mod");
    case IRNodeType::Mul: return (s << "Mul");
    case IRNodeType::Div: return (s << "Div");
    case IRNodeType::Min: return (s << "Min");
    case IRNodeType::Max: return (s << "Max");
    case IRNodeType::EQ: return (s << "EQ");
    case IRNodeType::NE: return (s << "NE");
    case IRNodeType::LT: return (s << "LT");
    case IRNodeType::LE: return (s << "LE");
    case IRNodeType::GT: return (s << "GT");
    case IRNodeType::GE: return (s << "GE");
    case IRNodeType::And: return (s << "And");
    case IRNodeType::Or: return (s << "Or");
    case IRNodeType::Not: return (s << "Not");
    case IRNodeType::Select: return (s << "Select");
    case IRNodeType::Load: return (s << "Load");
    case IRNodeType::Ramp: return (s << "Ramp");
    case IRNodeType::Call: return (s << "Call");
    case IRNodeType::Let: return (s << "Let");
    case IRNodeType::Shuffle: return (s << "Shuffle");
    case IRNodeType::LetStmt: return (s << "LetStmt");
    case IRNodeType::AssertStmt: return (s << "AssertStmt");
    case IRNodeType::ProducerConsumer: return (s << "ProducerConsumer");
    case IRNodeType::For: return (s << "For");
    case IRNodeType::Acquire: return (s << "Acquire");
    case IRNodeType::Store: return (s << "Store");
    case IRNodeType::Provide: return (s << "Provide");
    case IRNodeType::Allocate: return (s << "Allocate");
    case IRNodeType::Free: return (s << "Free");
    case IRNodeType::Realize: return (s << "Realize");
    case IRNodeType::Block: return (s << "Block");
    case IRNodeType::Fork: return (s << "Fork");
    case IRNodeType::IfThenElse: return (s << "IfThenElse");
    case IRNodeType::Evaluate: return (s << "Evaluate");
    case IRNodeType::Prefetch: return (s << "Prefetch");
    default: return s;
    }
};

Expr parse_halide_expr(char **cursor, char *end, Type expected_type) {
    consume_whitespace(cursor, end);

    struct TypePattern {
        const char *cast_prefix = nullptr;
        const char *constant_prefix = nullptr;
        Type type;
        string cast_prefix_storage, constant_prefix_storage;
        TypePattern(Type t) {
            ostringstream cast_prefix_stream, constant_prefix_stream;
            cast_prefix_stream << t << '(';
            cast_prefix_storage = cast_prefix_stream.str();
            cast_prefix = cast_prefix_storage.c_str();

            constant_prefix_stream << '(' << t << ')';
            constant_prefix_storage = constant_prefix_stream.str();
            constant_prefix = constant_prefix_storage.c_str();
            type = t;
        }
    };

    static TypePattern typenames[] = {
        {UInt(1)},
        {Int(8)},
        {UInt(8)},
        {Int(16)},
        {UInt(16)},
        {Int(32)},
        {UInt(32)},
        {Int(64)},
        {UInt(64)},
        {Float(64)},
        {Float(32)}};
    for (auto t : typenames) {
        if (consume(cursor, end, t.cast_prefix)) {
            Expr a = cast(t.type, parse_halide_expr(cursor, end, Type{}));
            expect(cursor, end, ")");
            return a;
        }
        if (consume(cursor, end, t.constant_prefix)) {
            return make_const(t.type, consume_int(cursor, end));
        }
    }
    if (consume(cursor, end, "(let ")) {
        string name = consume_token(cursor, end);
        consume_whitespace(cursor, end);
        expect(cursor, end, "=");
        consume_whitespace(cursor, end);

        Expr value = parse_halide_expr(cursor, end, Type{});

        consume_whitespace(cursor, end);
        expect(cursor, end, "in");
        consume_whitespace(cursor, end);

        Expr body = parse_halide_expr(cursor, end, expected_type);

        Expr a = Let::make(name, value, body);
        expect(cursor, end, ")");
        return a;
    }
    if (consume(cursor, end, "min(")) {
        Expr a = parse_halide_expr(cursor, end, expected_type);
        expect(cursor, end, ",");
        Expr b = parse_halide_expr(cursor, end, expected_type);
        consume_whitespace(cursor, end);
        expect(cursor, end, ")");
        return min(a, b);
    }
    if (consume(cursor, end, "max(")) {
        Expr a = parse_halide_expr(cursor, end, expected_type);
        expect(cursor, end, ",");
        Expr b = parse_halide_expr(cursor, end, expected_type);
        consume_whitespace(cursor, end);
        expect(cursor, end, ")");
        return max(a, b);
    }
    if (consume(cursor, end, "select(")) {
        Expr a = parse_halide_expr(cursor, end, Bool());
        expect(cursor, end, ",");
        Expr b = parse_halide_expr(cursor, end, expected_type);
        expect(cursor, end, ",");
        Expr c = parse_halide_expr(cursor, end, expected_type);
        consume_whitespace(cursor, end);
        expect(cursor, end, ")");
        return select(a, b, c);
    }
    Call::ConstString binary_intrinsics[] =
        {Call::bitwise_and,
         Call::bitwise_or,
         Call::shift_left,
         Call::shift_right};
    for (auto intrin : binary_intrinsics) {
        if (consume(cursor, end, intrin)) {
            expect(cursor, end, "(");
            Expr a = parse_halide_expr(cursor, end, expected_type);
            expect(cursor, end, ",");
            Expr b = parse_halide_expr(cursor, end, expected_type);
            consume_whitespace(cursor, end);
            expect(cursor, end, ")");
            return Call::make(a.type(), intrin, {a, b}, Call::PureIntrinsic);
        }
    }

    if (consume(cursor, end, "round_f32(")) {
        Expr a = parse_halide_expr(cursor, end, Float(32));
        expect(cursor, end, ")");
        return round(a);
    }
    if (consume(cursor, end, "ceil_f32(")) {
        Expr a = parse_halide_expr(cursor, end, Float(32));
        expect(cursor, end, ")");
        return ceil(a);
    }
    if (consume(cursor, end, "floor_f32(")) {
        Expr a = parse_halide_expr(cursor, end, Float(32));
        expect(cursor, end, ")");
        return floor(a);
    }

    if (consume(cursor, end, "(")) {
        Expr a = parse_halide_expr(cursor, end, Type{});
        Expr result;
        consume_whitespace(cursor, end);
        if (consume(cursor, end, "+")) {
            result = a + parse_halide_expr(cursor, end, expected_type);
        }
        if (consume(cursor, end, "*")) {
            result = a * parse_halide_expr(cursor, end, expected_type);
        }
        if (consume(cursor, end, "-")) {
            result = a - parse_halide_expr(cursor, end, expected_type);
        }
        if (consume(cursor, end, "/")) {
            result = a / parse_halide_expr(cursor, end, expected_type);
        }
        if (consume(cursor, end, "%")) {
            result = a % parse_halide_expr(cursor, end, expected_type);
        }
        if (consume(cursor, end, "<=")) {
            result = a <= parse_halide_expr(cursor, end, Type{});
        }
        if (consume(cursor, end, "<")) {
            result = a < parse_halide_expr(cursor, end, Type{});
        }
        if (consume(cursor, end, ">=")) {
            result = a >= parse_halide_expr(cursor, end, Type{});
        }
        if (consume(cursor, end, ">")) {
            result = a > parse_halide_expr(cursor, end, Type{});
        }
        if (consume(cursor, end, "==")) {
            result = a == parse_halide_expr(cursor, end, Type{});
        }
        if (consume(cursor, end, "!=")) {
            result = a != parse_halide_expr(cursor, end, Type{});
        }
        if (consume(cursor, end, "&&")) {
            result = a && parse_halide_expr(cursor, end, Bool());
        }
        if (consume(cursor, end, "||")) {
            result = a || parse_halide_expr(cursor, end, Bool());
        }
        if (result.defined()) {
            consume_whitespace(cursor, end);
            expect(cursor, end, ")");
            return result;
        }
    }
    if (consume(cursor, end, "v")) {
        if (expected_type == Type{}) {
            expected_type = Int(32);
        }
        Expr a = Variable::make(expected_type, "v" + std::to_string(consume_int(cursor, end)));
        return a;
    }
    if ((**cursor >= '0' && **cursor <= '9') || **cursor == '-') {
        Expr e = make_const(Int(32), consume_int(cursor, end));
        if (**cursor == '.') {
            e += consume_float(cursor, end);
        }
        return e;
    }
    if (consume(cursor, end, "true")) {
        return const_true();
    }
    if (consume(cursor, end, "false")) {
        return const_false();
    }
    if (consume(cursor, end, "!")) {
        return !parse_halide_expr(cursor, end, Bool());
    }

    if ((**cursor >= 'a' && **cursor <= 'z') || **cursor == '.') {
        char **tmp = cursor;
        string name = consume_token(tmp, end);
        if (consume(tmp, end, "[")) {
            *cursor = *tmp;
            Expr index = parse_halide_expr(cursor, end, Int(32));
            expect(cursor, end, "]");
            if (expected_type == Type{}) {
                expected_type = Int(32);
            }
            return Load::make(expected_type, name, index, Buffer<>(), Parameter(), const_true(), ModulusRemainder());
        } else {
            if (expected_type == Type{}) {
                expected_type = Int(32);
            }
            return Variable::make(expected_type, name);
        }
    }

    std::cerr << "Failed to parse Halide Expr starting at " << *cursor << "\n";
    abort();
    return Expr();
}

class RenameVariables : public IRMutator {
    map<string, string> varnames_map;
    string prefix;
    int counter = 0;

    using IRMutator::visit;
    Expr visit(const Variable *op) override {
        if (varnames_map.count(op->name) == 0) {
            varnames_map[op->name] = prefix + std::to_string(counter);
            counter++;  
        }
        return Variable::make(op->type, varnames_map[op->name]);
    }
public:
    RenameVariables(string prefix);
};
RenameVariables::RenameVariables(string p) {
    prefix = p;
}

Expr rename_variables(Expr e, string prefix) {
    // take 2 passes to avoid stepping on existing vars
    Expr pass1 = RenameVariables("VAR").mutate(e);
    return RenameVariables(prefix).mutate(e);
}

class ReplaceConstants : public IRMutator {
    map<int, string> constant_map;

    using IRMutator::visit;
    Expr visit (const IntImm *imm) override {
        if (constant_map.count(imm->value) == 1) {
            return Variable::make(imm->type, constant_map[imm->value]);
        } else {
            return IRMutator::visit(imm);
        }
    }
public:
    ReplaceConstants(map<int, string> constant_map);
};

ReplaceConstants::ReplaceConstants(map<int, string> cm) {
    constant_map = cm;
}

class ConstantMappings : public IRVisitor {
    int counter = 0;

    void update_map(int c) {
        if (constant_map.count(c) == 0) {
            constant_map[c] = "c" + std::to_string(counter);
            counter++;
        }
    }

    using IRVisitor::visit;
    void visit(const IntImm *imm) override {
        update_map(imm->value);
    }
    void visit(const UIntImm *imm) override {
        if (imm->type.bits() != 1)
            update_map(imm->value);
    }
public: 
    map<int, string> constant_map;
    ConstantMappings(Expr e);
};

ConstantMappings::ConstantMappings(Expr e) {
    e.accept(this);
}

Expr factor_constants(Expr e) {
    ConstantMappings cm = ConstantMappings(e);
    map<int, string> replaceable;

    // first check if all constants can be replaced
    Expr replace_all_e = ReplaceConstants(cm.constant_map).mutate(e);
    if (satisfy(z3query_verifytrue(replace_all_e)) == Z3Result::Unsat) {
        return rename_variables(replace_all_e, "v");
    }

    for (auto c : cm.constant_map) {
        map<int, string> one_const;
        one_const[c.first] = c.second;
        if (satisfy(z3query_verifytrue(ReplaceConstants(one_const).mutate(e))) == Z3Result::Unsat) {
            replaceable[c.first] = c.second;
        }
    }

    // check that all substitutions are safe together
    Expr replaced_const_e = rename_variables(ReplaceConstants(replaceable).mutate(e), "v");
    if (satisfy(z3query_verifytrue(replaced_const_e)) == Z3Result::Unsat) {
        return replaced_const_e;
    } else {
        return Variable::make(Type{}, "FAIL"); // super hacky, sorry
    }

}

class CountConstants : IRVisitor {
public:
    std::set<int> constant_set;
    int counter = 0;

    using IRVisitor::visit;
    void visit(const IntImm *imm) override {
       constant_set.insert(imm->value);
    }

    CountConstants(Expr e);
};

CountConstants::CountConstants(Expr e) {
    e.accept(this);
    counter = constant_set.size();
}

int main(int argc, char **argv) {
    vector<Expr> exprs;
    std::cout << "Reading expressions from file\n";
    std::ifstream input;
    input.open("/Users/mpu/research/termrewriting/factor2/xad");
    for (string line; std::getline(input, line);) {
        if (line.empty()) continue;
        // It's possible to comment out lines for debugging
        if (line[0] == '#') continue;

        // There are some extraneous newlines in some of the files. Balance parentheses...
        size_t open, close;
        while (1) {
            open = std::count(line.begin(), line.end(), '(');
            close = std::count(line.begin(), line.end(), ')');
            if (open == close) break;
            string next;
            assert(std::getline(input, next));
            line += next;
        }

        //std::cout << "Parsing expression: '" << line << "'\n";
        char *start = &line[0];
        char *end = &line[line.size()];
        Expr e = simplify(parse_halide_expr(&start, end, Type{}));
        Expr factored_e = factor_constants(e);
        //std::cout << "Simplified expression: " << e << "\n";
        //std::cout << "Constants factored expression: " << factor_constants(e) << "\n";
        std::ostringstream s;
        s << factored_e;
        if (s.str().compare("FAIL") == 0) {
            std::cout << "Constants are interrelated: " << e << "\n";
        } else {
            std::cout << "CONSTANT " << std::to_string(CountConstants(factored_e).counter) << " from " << std::to_string(CountConstants(e).counter) << " " << rename_variables(factored_e, "v") << "\n";
        }

    }

    return 0;
}
