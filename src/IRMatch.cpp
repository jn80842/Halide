#include <iostream>
#include <map>
#include <utility>

#include "IREquality.h"
#include "IRMatch.h"
#include "IROperator.h"
#include "IRVisitor.h"

namespace Halide {
namespace Internal {

using std::map;
using std::string;
using std::vector;

void expr_match_test() {
    vector<Expr> matches;
    Expr w = Variable::make(Int(32), "*");
    Expr fw = Variable::make(Float(32), "*");
    Expr x = Variable::make(Int(32), "x");
    Expr y = Variable::make(Int(32), "y");
    Expr fx = Variable::make(Float(32), "fx");
    Expr fy = Variable::make(Float(32), "fy");

    Expr vec_wild = Variable::make(Int(32, 4), "*");

    internal_assert(expr_match(w, 3, matches) &&
                    equal(matches[0], 3));

    internal_assert(expr_match(w + 3, (y * 2) + 3, matches) &&
                    equal(matches[0], y * 2));

    internal_assert(expr_match(fw * 17 + cast<float>(w + cast<int>(fw)),
                               (81.0f * fy) * 17 + cast<float>(x / 2 + cast<int>(x + 4.5f)), matches) &&
                    matches.size() == 3 &&
                    equal(matches[0], 81.0f * fy) &&
                    equal(matches[1], x / 2) &&
                    equal(matches[2], x + 4.5f));

    internal_assert(!expr_match(fw + 17, fx + 18, matches) &&
                    matches.empty());
    internal_assert(!expr_match((w * 2) + 17, fx + 17, matches) &&
                    matches.empty());
    internal_assert(!expr_match(w * 3, 3 * x, matches) &&
                    matches.empty());

    internal_assert(expr_match(vec_wild * 3, Ramp::make(x, y, 4) * 3, matches));

    std::cout << "expr_match test passed" << std::endl;
}

class IRMatch : public IRVisitor {
public:
    bool result;
    vector<Expr> *matches;
    map<string, Expr> *var_matches;
    Expr expr;

    IRMatch(Expr e, vector<Expr> &m)
        : result(true), matches(&m), var_matches(nullptr), expr(std::move(e)) {
    }
    IRMatch(Expr e, map<string, Expr> &m)
        : result(true), matches(nullptr), var_matches(&m), expr(std::move(e)) {
    }

    using IRVisitor::visit;

    bool types_match(Type pattern_type, Type expr_type) {
        bool bits_matches = (pattern_type.bits() == 0) || (pattern_type.bits() == expr_type.bits());
        bool lanes_matches = (pattern_type.lanes() == 0) || (pattern_type.lanes() == expr_type.lanes());
        bool code_matches = (pattern_type.code() == expr_type.code());
        return bits_matches && lanes_matches && code_matches;
    }

    void visit(const IntImm *op) override {
        const IntImm *e = expr.as<IntImm>();
        if (!e ||
            e->value != op->value ||
            !types_match(op->type, e->type)) {
            result = false;
        }
    }

    void visit(const UIntImm *op) override {
        const UIntImm *e = expr.as<UIntImm>();
        if (!e ||
            e->value != op->value ||
            !types_match(op->type, e->type)) {
            result = false;
        }
    }

    void visit(const FloatImm *op) override {
        const FloatImm *e = expr.as<FloatImm>();
        // Note we use uint64_t equality instead of double equality to
        // catch NaNs. We're checking for the same bits.
        if (!e ||
            reinterpret_bits<uint64_t>(e->value) !=
                reinterpret_bits<uint64_t>(op->value) ||
            !types_match(op->type, e->type)) {
            result = false;
        }
    }

    void visit(const Cast *op) override {
        const Cast *e = expr.as<Cast>();
        if (result && e && types_match(op->type, e->type)) {
            expr = e->value;
            op->value.accept(this);
        } else {
            result = false;
        }
    }

    void visit(const Variable *op) override {
        if (!result) {
            return;
        }

        if (!types_match(op->type, expr.type())) {
            result = false;
        } else if (matches) {
            if (op->name == "*") {
                matches->push_back(expr);
            } else {
                const Variable *e = expr.as<Variable>();
                result = e && (e->name == op->name);
            }
        } else if (var_matches) {
            Expr &match = (*var_matches)[op->name];
            if (match.defined()) {
                result = equal(match, expr);
            } else {
                match = expr;
            }
        }
    }

    template<typename T>
    void visit_binary_operator(const T *op) {
        const T *e = expr.as<T>();
        if (result && e) {
            expr = e->a;
            op->a.accept(this);
            expr = e->b;
            op->b.accept(this);
        } else {
            result = false;
        }
    }

    void visit(const Add *op) override {
        visit_binary_operator(op);
    }
    void visit(const Sub *op) override {
        visit_binary_operator(op);
    }
    void visit(const Mul *op) override {
        visit_binary_operator(op);
    }
    void visit(const Div *op) override {
        visit_binary_operator(op);
    }
    void visit(const Mod *op) override {
        visit_binary_operator(op);
    }
    void visit(const Min *op) override {
        visit_binary_operator(op);
    }
    void visit(const Max *op) override {
        visit_binary_operator(op);
    }
    void visit(const EQ *op) override {
        visit_binary_operator(op);
    }
    void visit(const NE *op) override {
        visit_binary_operator(op);
    }
    void visit(const LT *op) override {
        visit_binary_operator(op);
    }
    void visit(const LE *op) override {
        visit_binary_operator(op);
    }
    void visit(const GT *op) override {
        visit_binary_operator(op);
    }
    void visit(const GE *op) override {
        visit_binary_operator(op);
    }
    void visit(const And *op) override {
        visit_binary_operator(op);
    }
    void visit(const Or *op) override {
        visit_binary_operator(op);
    }

    void visit(const Not *op) override {
        const Not *e = expr.as<Not>();
        if (result && e) {
            expr = e->a;
            op->a.accept(this);
        } else {
            result = false;
        }
    }

    void visit(const Select *op) override {
        const Select *e = expr.as<Select>();
        if (result && e) {
            expr = e->condition;
            op->condition.accept(this);
            expr = e->true_value;
            op->true_value.accept(this);
            expr = e->false_value;
            op->false_value.accept(this);
        } else {
            result = false;
        }
    }

    void visit(const Load *op) override {
        const Load *e = expr.as<Load>();
        if (result && e && types_match(op->type, e->type) && e->name == op->name && e->alignment == op->alignment) {
            expr = e->predicate;
            op->predicate.accept(this);
            expr = e->index;
            op->index.accept(this);
        } else {
            result = false;
        }
    }

    void visit(const Ramp *op) override {
        const Ramp *e = expr.as<Ramp>();
        if (result && e && e->lanes == op->lanes) {
            expr = e->base;
            op->base.accept(this);
            expr = e->stride;
            op->stride.accept(this);
        } else {
            result = false;
        }
    }

    void visit(const Broadcast *op) override {
        const Broadcast *e = expr.as<Broadcast>();
        if (result && e && types_match(op->type, e->type)) {
            expr = e->value;
            op->value.accept(this);
        } else {
            result = false;
        }
    }

    void visit(const Call *op) override {
        const Call *e = expr.as<Call>();
        if (result && e &&
            types_match(op->type, e->type) &&
            e->name == op->name &&
            e->value_index == op->value_index &&
            e->call_type == op->call_type &&
            e->args.size() == op->args.size()) {
            for (size_t i = 0; result && (i < e->args.size()); i++) {
                expr = e->args[i];
                op->args[i].accept(this);
            }
        } else {
            result = false;
        }
    }

    void visit(const Let *op) override {
        const Let *e = expr.as<Let>();
        if (result && e && e->name == op->name) {
            expr = e->value;
            op->value.accept(this);
            expr = e->body;
            op->body.accept(this);
        } else {
            result = false;
        }
    }
};

bool expr_match(const Expr &pattern, const Expr &expr, vector<Expr> &matches) {
    matches.clear();
    if (!pattern.defined() && !expr.defined()) return true;
    if (!pattern.defined() || !expr.defined()) return false;

    IRMatch eq(expr, matches);
    pattern.accept(&eq);
    if (eq.result) {
        return true;
    } else {
        matches.clear();
        return false;
    }
}

bool expr_match(const Expr &pattern, const Expr &expr, map<string, Expr> &matches) {
    // Explicitly don't clear matches. This allows usages to pre-match
    // some variables.

    if (!pattern.defined() && !expr.defined()) return true;
    if (!pattern.defined() || !expr.defined()) return false;

    IRMatch eq(expr, matches);
    pattern.accept(&eq);
    if (eq.result) {
        return true;
    } else {
        matches.clear();
        return false;
    }
}

namespace IRMatcher {

HALIDE_ALWAYS_INLINE
bool equal_helper(const Expr &a, const Expr &b) {
    return equal(*a.get(), *b.get());
}

template<typename Op>
HALIDE_ALWAYS_INLINE bool equal_helper_binop(const BaseExprNode &a, const BaseExprNode &b) {
    return (equal_helper(((const Op &)a).a, ((const Op &)b).a) &&
            equal_helper(((const Op &)a).b, ((const Op &)b).b));
}

HALIDE_ALWAYS_INLINE
bool equal_helper(int a, int b) {
    return a == b;
}

template<typename T>
HALIDE_ALWAYS_INLINE bool equal_helper(const std::vector<T> &a, const std::vector<T> &b) {
    if (a.size() != b.size()) return false;
    for (size_t i = 0; i < a.size(); i++) {
        if (!equal_helper(a[i], b[i])) return false;
    }
    return true;
}

bool equal_helper(const BaseExprNode &a, const BaseExprNode &b) noexcept {
    switch (a.node_type) {
    case IRNodeType::IntImm:
        return ((const IntImm &)a).value == ((const IntImm &)b).value;
    case IRNodeType::UIntImm:
        return ((const UIntImm &)a).value == ((const UIntImm &)b).value;
    case IRNodeType::FloatImm:
        return ((const FloatImm &)a).value == ((const FloatImm &)b).value;
    case IRNodeType::StringImm:
        return ((const StringImm &)a).value == ((const StringImm &)b).value;
    case IRNodeType::Cast:
        return equal_helper(((const Cast &)a).value, ((const Cast &)b).value);
    case IRNodeType::Variable:
        return ((const Variable &)a).name == ((const Variable &)b).name;
    case IRNodeType::Add:
        return equal_helper_binop<Add>(a, b);
    case IRNodeType::Sub:
        return equal_helper_binop<Sub>(a, b);
    case IRNodeType::Mul:
        return equal_helper_binop<Mul>(a, b);
    case IRNodeType::Div:
        return equal_helper_binop<Div>(a, b);
    case IRNodeType::Mod:
        return equal_helper_binop<Mod>(a, b);
    case IRNodeType::Min:
        return equal_helper_binop<Min>(a, b);
    case IRNodeType::Max:
        return equal_helper_binop<Max>(a, b);
    case IRNodeType::EQ:
        return equal_helper_binop<EQ>(a, b);
    case IRNodeType::NE:
        return equal_helper_binop<NE>(a, b);
    case IRNodeType::LT:
        return equal_helper_binop<LT>(a, b);
    case IRNodeType::LE:
        return equal_helper_binop<LE>(a, b);
    case IRNodeType::GT:
        return equal_helper_binop<GT>(a, b);
    case IRNodeType::GE:
        return equal_helper_binop<GE>(a, b);
    case IRNodeType::And:
        return equal_helper_binop<And>(a, b);
    case IRNodeType::Or:
        return equal_helper_binop<Or>(a, b);
    case IRNodeType::Not:
        return equal_helper(((const Not &)a).a, ((const Not &)b).a);
    case IRNodeType::Select:
        return (equal_helper(((const Select &)a).condition, ((const Select &)b).condition) &&
                equal_helper(((const Select &)a).true_value, ((const Select &)b).true_value) &&
                equal_helper(((const Select &)a).false_value, ((const Select &)b).false_value));
    case IRNodeType::Load:
        return (((const Load &)a).name == ((const Load &)b).name &&
                equal_helper(((const Load &)a).index, ((const Load &)b).index));
    case IRNodeType::Ramp:
        return (equal_helper(((const Ramp &)a).base, ((const Ramp &)b).base) &&
                equal_helper(((const Ramp &)a).stride, ((const Ramp &)b).stride));
    case IRNodeType::Broadcast:
        return equal_helper(((const Broadcast &)a).value, ((const Broadcast &)b).value);
    case IRNodeType::Call:
        return (((const Call &)a).name == ((const Call &)b).name &&
                ((const Call &)a).call_type == ((const Call &)b).call_type &&
                ((const Call &)a).value_index == ((const Call &)b).value_index &&
                equal_helper(((const Call &)a).args, ((const Call &)b).args));
    case IRNodeType::Let:
        return (((const Let &)a).name == ((const Let &)b).name &&
                equal_helper(((const Let &)a).value, ((const Let &)b).value) &&
                equal_helper(((const Let &)a).body, ((const Let &)b).body));
    case IRNodeType::Shuffle:
        return (equal_helper(((const Shuffle &)a).vectors, ((const Shuffle &)b).vectors) &&
                equal_helper(((const Shuffle &)a).indices, ((const Shuffle &)b).indices));
    // Explicitly list all the Stmts instead of using a default
    // clause so that if new Exprs are added without being handled
    // here we get a compile-time error.
    case IRNodeType::LetStmt:
    case IRNodeType::AssertStmt:
    case IRNodeType::ProducerConsumer:
    case IRNodeType::For:
    case IRNodeType::Acquire:
    case IRNodeType::Store:
    case IRNodeType::Provide:
    case IRNodeType::Allocate:
    case IRNodeType::Free:
    case IRNodeType::Realize:
    case IRNodeType::Block:
    case IRNodeType::Fork:
    case IRNodeType::IfThenElse:
    case IRNodeType::Evaluate:
    case IRNodeType::Prefetch:
    case IRNodeType::Atomic:
        break;
    }
    return false;
}

void update_bfs_node_type_map(bfs_node_type_map &type_map, IRMatcherType t, int current_depth) {
    if (type_map.count(current_depth) == 0) {
        std::list<IRMatcherType> l = {t};
        type_map.insert({current_depth, l});
    } else {
        type_map[current_depth].push_back(t);
    }
}

void update_bfs_const_str_map(const_str_map &const_map, std::string s, int current_depth) {
    if (const_map.count(current_depth) == 0) {
        const_map.insert({current_depth, s});
    } else {
        const_map[current_depth] = const_map[current_depth] + s;
    }
}

std::string const_str_map_to_string(const_str_map &map1) {
    int largest_key = 0;
    for (auto it = map1.begin(); it != map1.end(); ++it) {
        if (it->first > largest_key) {
            largest_key = it->first;
        }
    }
    std::string s;
    for (int i = 0; i<=largest_key; i++) {
        if (map1.count(i) != 0) {
            s += map1[i];
        }
    }
    return s;
}

bool variable_counts_geq(variable_count_map &m1, variable_count_map &m2) {
    for (auto const& var : m2) {
        if (var.first[0] != 'c' && !(m1[var.first] >= var.second)) {
            debug(0) << "failed variable count geq: not " << m1[var.first] << " >= " << var.second << "\n";
            return false;
        }
    }
    return true;
}

void increment_term(IRMatcherType node_type, term_map &m) {
    if (m.count(node_type) == 0) {
        m[node_type] = 1;
    } else {
        m[node_type] = m[node_type] + 1;
    }
}

int get_total_op_count(term_map &t) {
    int total = 0;
    for (auto const& term_entry : t) {
        total += term_entry.second;
    }
    return total;
}

int get_expensive_arith_count(term_map &t) {
    return t[IRMatcherType::Div] + t[IRMatcherType::Mod] + t[IRMatcherType::Mul]; //+ t[IRMatcherType::MulByConstant];
}

int ternary_comp(int i1, int i2) {
    if (i1 == i2) {
        return 0;
    } else if (i1 > i2) {
        return 1;
    } else {
        return -1;
    }
}

int term_map_comp(term_map &m1, term_map &m2) {
    if (m1[IRMatcherType::Ramp] != m2[IRMatcherType::Ramp]) {
        return ternary_comp(m1[IRMatcherType::Ramp],m2[IRMatcherType::Ramp]);
    } else if (m1[IRMatcherType::Broadcast] != m2[IRMatcherType::Broadcast]) {
        return ternary_comp(m1[IRMatcherType::Broadcast], m2[IRMatcherType::Broadcast]);
    } else if (m1[IRMatcherType::Select] != m2[IRMatcherType::Select]) {
        return ternary_comp(m1[IRMatcherType::Select], m2[IRMatcherType::Select]);
    } else if (m1[IRMatcherType::SelectConstantBranch], m2[IRMatcherType::SelectConstantBranch]) {
        return ternary_comp(m1[IRMatcherType::SelectConstantBranch], m2[IRMatcherType::SelectConstantBranch]);
    } else if (m1[IRMatcherType::Div] != m2[IRMatcherType::Div]) {
        return ternary_comp(m1[IRMatcherType::Div], m2[IRMatcherType::Div]);
    } else if (m1[IRMatcherType::Mul] != m2[IRMatcherType::Mul]) {
        return ternary_comp(m1[IRMatcherType::Mul], m2[IRMatcherType::Mul]);
    } else if (m1[IRMatcherType::Mod] != m2[IRMatcherType::Mod]) {
        return ternary_comp(m1[IRMatcherType::Mod], m2[IRMatcherType::Mod]);
    } else if (m1[IRMatcherType::Sub] != m2[IRMatcherType::Sub]) { 
        return ternary_comp(m1[IRMatcherType::Sub], m2[IRMatcherType::Sub]);
    } else if (m1[IRMatcherType::Add] != m2[IRMatcherType::Add]) {
        return ternary_comp(m1[IRMatcherType::Add], m2[IRMatcherType::Add]);
    } else if (m1[IRMatcherType::Min] != m2[IRMatcherType::Min]) { // max ops go in this bucket too
        return ternary_comp(m1[IRMatcherType::Min], m2[IRMatcherType::Min]);
    } else if (m1[IRMatcherType::MinWithConstant] != m2[IRMatcherType::MinWithConstant]) {
        return ternary_comp(m1[IRMatcherType::MinWithConstant], m2[IRMatcherType::MinWithConstant]);
    } else if (m1[IRMatcherType::MulByConstant] != m2[IRMatcherType::MulByConstant]) {
        return ternary_comp(m1[IRMatcherType::MulByConstant], m2[IRMatcherType::MulByConstant]);
    } else if (m1[IRMatcherType::SubByConstant] != m2[IRMatcherType::SubByConstant]) { 
        return ternary_comp(m1[IRMatcherType::SubByConstant], m2[IRMatcherType::SubByConstant]);
    } else if (m1[IRMatcherType::AddByConstant] != m2[IRMatcherType::AddByConstant]) { 
        return ternary_comp(m1[IRMatcherType::AddByConstant], m2[IRMatcherType::AddByConstant]);
    } else if (m1[IRMatcherType::Or] != m2[IRMatcherType::Or]) {
        return ternary_comp(m1[IRMatcherType::Or], m2[IRMatcherType::Or]);
    } else if (m1[IRMatcherType::And] != m2[IRMatcherType::And]) {
        return ternary_comp(m1[IRMatcherType::And], m2[IRMatcherType::And]);
    } else if (m1[IRMatcherType::GE] != m2[IRMatcherType::GE]) {
        return ternary_comp(m1[IRMatcherType::GE], m2[IRMatcherType::GE]);
    } else if (m1[IRMatcherType::GT] != m2[IRMatcherType::GT]) {
         return ternary_comp(m1[IRMatcherType::GT], m2[IRMatcherType::GT]);
    } else if (m1[IRMatcherType::LE] != m2[IRMatcherType::LE]) {
        return ternary_comp(m1[IRMatcherType::LE], m2[IRMatcherType::LE]);
    } else if (m1[IRMatcherType::LT] != m2[IRMatcherType::LT]) {
        return ternary_comp(m1[IRMatcherType::LT], m2[IRMatcherType::LT]);
    } else if (m1[IRMatcherType::NE] != m2[IRMatcherType::NE]) {
        return ternary_comp(m1[IRMatcherType::NE], m2[IRMatcherType::NE]);
    } else if (m1[IRMatcherType::EQ] != m2[IRMatcherType::EQ]) {
        return ternary_comp(m1[IRMatcherType::EQ], m2[IRMatcherType::EQ]);
    } else if (m1[IRMatcherType::Not] != m2[IRMatcherType::Not]) {
        return ternary_comp(m1[IRMatcherType::Not], m2[IRMatcherType::Not]);
    } else {
        return 0; // two histograms are equiv
    }
}

node_type_ordering nto = {
    {IRMatcherType::Ramp,23},
    {IRMatcherType::Broadcast,22},
    {IRMatcherType::Select,21},
    {IRMatcherType::Div,20},
    {IRMatcherType::Mul,19},
    {IRMatcherType::MulByConstant,18},
    {IRMatcherType::Mod,17},
    {IRMatcherType::Sub,16},
    {IRMatcherType::SubByConstant,15},
    {IRMatcherType::Add,14},
    {IRMatcherType::Max,13},
    {IRMatcherType::Min,13},

    {IRMatcherType::Or,12},
    {IRMatcherType::And,11},
    {IRMatcherType::GE,10},
    {IRMatcherType::GT,9},
    {IRMatcherType::LE,8},
    {IRMatcherType::LT,7},
    {IRMatcherType::NE,6},
    {IRMatcherType::EQ,5},
    {IRMatcherType::Not,4},
};

// add and sub are least, all others are greatest
node_type_ordering nto_adds = {
    {IRMatcherType::Ramp,100},
    {IRMatcherType::Broadcast,100},
    {IRMatcherType::Select,100},
    {IRMatcherType::Div,100},
    {IRMatcherType::Mul,100},
    {IRMatcherType::MulByConstant,2},
    {IRMatcherType::Mod,100},
    {IRMatcherType::Sub,3},
    {IRMatcherType::SubByConstant,1},
    {IRMatcherType::Add,3},
    {IRMatcherType::AddByConstant,1},
    {IRMatcherType::Max,100},
    {IRMatcherType::Min,100},

    {IRMatcherType::Or,100},
    {IRMatcherType::And,100},
    {IRMatcherType::GE,100},
    {IRMatcherType::GT,100},
    {IRMatcherType::LE,100},
    {IRMatcherType::LT,100},
    {IRMatcherType::NE,100},
    {IRMatcherType::EQ,100},
    {IRMatcherType::Not,100},
};


int multiset_node_order(std::list<IRMatcherType> &m1, std::list<IRMatcherType> &m2, node_type_ordering &comparator) {
    int max_m1 = 0;
    int max_m2 = 0;
    for (IRMatcherType node_type : m1) {
        if (comparator[node_type] > max_m1)
            max_m1 = comparator[node_type];
    }
    for (IRMatcherType node_type : m2) {
        if (comparator[node_type] > max_m2) 
            max_m2 = comparator[node_type];
    }
    if (max_m1 > max_m2) {
        return 1;
    } else if (max_m1 < max_m2) {
        return -1;
    } else {
        return 0;
    }
}

// not implementing the full recursive checks; root and first layer should be sufficient
int mpo(bfs_node_type_map &map1, bfs_node_type_map &map2, node_type_ordering &comparator) {
    // if t2 is variable and t1 is not, t1 > t2
    if (!(map1.empty()) && map2.empty()) {
        return 1;
    }
    // if roots are different, compare roots
    if ((map1.count(0) != 0) && (map2.count(0) != 0)) {
        int root_status = multiset_node_order(map1[0],map2[0],comparator);
        if (!(root_status == 0)) {
            return root_status;
        }  
    }
    // compare first depth
    if ((map1.count(1) != 0) && (map2.count(1) != 0)) {
        return multiset_node_order(map1[1],map2[1],comparator);
    } else {
        return 0;
    }

}

int mpo_adds(bfs_node_type_map &map1, bfs_node_type_map &map2) {
    return mpo(map1,map2,nto_adds);
}

int mpo_full(bfs_node_type_map &map1, bfs_node_type_map &map2) {
    return mpo(map1,map1,nto);
}

}  // namespace IRMatcher
}  // namespace Internal
}  // namespace Halide
