#include <iostream>
#include <map>

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

    internal_assert(expr_match(w + 3, (y*2) + 3, matches) &&
                    equal(matches[0], y*2));

    internal_assert(expr_match(fw * 17 + cast<float>(w + cast<int>(fw)),
                               (81.0f * fy) * 17 + cast<float>(x/2 + cast<int>(x + 4.5f)), matches) &&
                    matches.size() == 3 &&
                    equal(matches[0], 81.0f * fy) &&
                    equal(matches[1], x/2) &&
                    equal(matches[2], x + 4.5f));

    internal_assert(!expr_match(fw + 17, fx + 18, matches) &&
                    matches.empty());
    internal_assert(!expr_match((w*2) + 17, fx + 17, matches) &&
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

    IRMatch(Expr e, vector<Expr> &m) : result(true), matches(&m), var_matches(nullptr), expr(e) {
    }
    IRMatch(Expr e, map<string, Expr> &m) : result(true), matches(nullptr), var_matches(&m), expr(e) {
    }

    using IRVisitor::visit;

    bool types_match(Type pattern_type, Type expr_type) {
        bool bits_matches  = (pattern_type.bits()  == 0) || (pattern_type.bits()  == expr_type.bits());
        bool lanes_matches = (pattern_type.lanes() == 0) || (pattern_type.lanes() == expr_type.lanes());
        bool code_matches  = (pattern_type.code()  == expr_type.code());
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

    void visit(const Add *op) override {visit_binary_operator(op);}
    void visit(const Sub *op) override {visit_binary_operator(op);}
    void visit(const Mul *op) override {visit_binary_operator(op);}
    void visit(const Div *op) override {visit_binary_operator(op);}
    void visit(const Mod *op) override {visit_binary_operator(op);}
    void visit(const Min *op) override {visit_binary_operator(op);}
    void visit(const Max *op) override {visit_binary_operator(op);}
    void visit(const EQ *op) override {visit_binary_operator(op);}
    void visit(const NE *op) override {visit_binary_operator(op);}
    void visit(const LT *op) override {visit_binary_operator(op);}
    void visit(const LE *op) override {visit_binary_operator(op);}
    void visit(const GT *op) override {visit_binary_operator(op);}
    void visit(const GE *op) override {visit_binary_operator(op);}
    void visit(const And *op) override {visit_binary_operator(op);}
    void visit(const Or *op) override {visit_binary_operator(op);}

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

bool expr_match(Expr pattern, Expr expr, vector<Expr> &matches) {
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

bool expr_match(Expr pattern, Expr expr, map<string, Expr> &matches) {
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

void update_bfs_node_type_map(bfs_node_type_map &type_map, IRNodeType t, int current_depth) {
    if (type_map.count(current_depth) == 0) {
        std::list<IRNodeType> l = {t};
        type_map.insert({current_depth, l});
    } else {
        type_map[current_depth].push_back(t);
    }
}

node_type_strings node_type_string_lookup = {
    {IRNodeType::Ramp,"Ramp "},
    {IRNodeType::Broadcast,"Broadcast "},
    {IRNodeType::Select,"Select "},
    {IRNodeType::Div,"Div "},
    {IRNodeType::Mul,"Mul "},
    {IRNodeType::Mod,"Mod "},
    {IRNodeType::Sub,"Sub "},
    {IRNodeType::Add,"Add "},
    {IRNodeType::Max,"Max "},
    {IRNodeType::Min,"Min "},
    {IRNodeType::Not,"Not "},
    {IRNodeType::Or,"Or "},
    {IRNodeType::And,"And "},
    {IRNodeType::GE,"GE "},
    {IRNodeType::GT,"GT "},
    {IRNodeType::LE,"LE "},
    {IRNodeType::LT,"LT "},
    {IRNodeType::NE,"NE "},
    {IRNodeType::EQ,"EQ "},
    {IRNodeType::Cast,"Cast "},
    {IRNodeType::Variable,"Variable "},
    {IRNodeType::FloatImm,"FloatImm "},
    {IRNodeType::UIntImm,"UIntImm "},
    {IRNodeType::IntImm,"IntImm "}
};

std::string print_bfs_node_type_map(bfs_node_type_map &type_map) {
    std::string retval;
    for (unsigned long i=0; i<type_map.size(); i++) {
        retval += std::to_string(i);
         for (auto it = type_map[i].cbegin(); it != type_map[i].cend(); it++)
            retval += node_type_string_lookup[*it];
    }
    return retval;
}

CompIRNodeTypeStatus compare_bfs_node_type_maps(bfs_node_type_map &map1, bfs_node_type_map &map2) {
    int map_size;
    if (map1.size() > map2.size()) {
        map_size = map2.size();
    } else {
        map_size = map1.size();
    }
    for (int i=0; i<map_size; i++) {
        for(auto it1 = map1[i].begin(), it2 = map2[i].begin(); it1 != map1[i].end() || it2 != map2[i].end(); ++it1, ++it2) {
            if (not (compare_node_types(*it1, *it2) == CompIRNodeTypeStatus::EQ)) {
                return compare_node_types(*it1, *it2);
            }
        }
    }
    return CompIRNodeTypeStatus::EQ;
}

node_type_ordering nto = {
    {IRNodeType::Ramp,23},
    {IRNodeType::Broadcast,22},
    {IRNodeType::Select,21},
    {IRNodeType::Div,20},
    {IRNodeType::Mul,19},
    {IRNodeType::Mod,18},
    {IRNodeType::Sub,17},
    {IRNodeType::Add,17},
    {IRNodeType::Max,14},
    {IRNodeType::Min,14},

    {IRNodeType::Or,12},
    {IRNodeType::And,11},
    {IRNodeType::GE,10},
    {IRNodeType::GT,9},
    {IRNodeType::LE,8},
    {IRNodeType::LT,7},
    {IRNodeType::NE,6},
    {IRNodeType::EQ,5},
    {IRNodeType::Not,4},
};

// lexico sort st. adds and subs are less than all other ops
CompIRNodeTypeStatus compare_bfs_node_adds(bfs_node_type_map &map1, bfs_node_type_map &map2) {
    int map_size;
    if (map1.size() > map2.size()) {
        map_size = map2.size();
    } else {
        map_size = map1.size();
    }
    for (int i=0; i<map_size; i++) {
        for(auto it1 = map1[i].begin(), it2 = map2[i].begin(); it1 != map1[i].end() || it2 != map2[i].end(); ++it1, ++it2) {
            if (not (compare_node_types(*it1, *it2) == CompIRNodeTypeStatus::EQ)) {
                if ((nto[*it1] != nto[IRNodeType::Add]) && (nto[*it2] == nto[IRNodeType::Add])) {
                    return CompIRNodeTypeStatus::GT;
                } else if ((nto[*it1] == nto[IRNodeType::Add]) && (nto[*it2] != nto[IRNodeType::Add])) {
                    return CompIRNodeTypeStatus::LT;
                }
            }
        }
    }
    return CompIRNodeTypeStatus::EQ;
}

void increment_term(IRNodeType node_type, term_map &m) {
    if (m.count(node_type) == 0) {
        m[node_type] = 1;
    } else {
        m[node_type] = m[node_type] + 1;
    }
}

node_type_ordering root_nto = {
    {IRNodeType::Ramp,23},
    {IRNodeType::Broadcast,22},
    {IRNodeType::Select,21},
    {IRNodeType::Div,20},
    {IRNodeType::Mul,19},
    {IRNodeType::Mod,18},

    {IRNodeType::Max,17},
    {IRNodeType::Min,17},
    {IRNodeType::Sub,15},
    {IRNodeType::Add,15},
    {IRNodeType::Or,12},
    {IRNodeType::And,11},
    {IRNodeType::GE,10},
    {IRNodeType::GT,9},
    {IRNodeType::LE,8},
    {IRNodeType::LT,7},
    {IRNodeType::NE,6},
    {IRNodeType::EQ,5},
    {IRNodeType::Not,4},
};

int get_total_op_count(term_map &t) {
    int total = 0;
    for (auto const& term_entry : t) {
        total += term_entry.second;
    }
    return total;
}

CompIRNodeTypeStatus compare_node_types(IRNodeType n1, IRNodeType n2) {
    if (nto[n1] == nto[n2]) {
        return CompIRNodeTypeStatus::EQ;
    } else if (nto[n1] > nto[n2]) {
        return CompIRNodeTypeStatus::GT;
    } else {
        return CompIRNodeTypeStatus::LT;
    }
}

CompIRNodeTypeStatus compare_root_node_types(IRNodeType n1, IRNodeType n2) {
    if (root_nto[n1] == root_nto[n2]) {
        return CompIRNodeTypeStatus::EQ;
    } else if (root_nto[n1] > root_nto[n2]) {
        return CompIRNodeTypeStatus::GT;
    } else {
        return CompIRNodeTypeStatus::LT;
    }
}

CompIRNodeTypeStatus ternary_comp(int i1, int i2) {
    if (i1 == i2) {
        return CompIRNodeTypeStatus::EQ;
    } else if (i1 > i2) {
        return CompIRNodeTypeStatus::GT;
    } else {
        return CompIRNodeTypeStatus::LT;
    }
}

std::string comp_to_s(CompIRNodeTypeStatus c) {
    if (c == CompIRNodeTypeStatus::EQ) {
        return "EQ";
    } else if (c == CompIRNodeTypeStatus::GT) {
        return "GT";
    } else {
        return "LT";
    }
}

bool compare_node_type_lists(node_type_list before_list, node_type_list after_list) {
    node_type_list::iterator it_before = before_list.begin();
    node_type_list::iterator it_after = after_list.begin();
    while(it_before != before_list.end() && it_after != after_list.end()) {
        if (*it_before != *it_after) {
            return compare_node_types(*it_before,*it_after) == CompIRNodeTypeStatus::GT;
        }
        ++it_before;
        ++it_after;
    }
    return false;
}

int get_expensive_arith_count(term_map &t) {
    return t[IRNodeType::Div] + t[IRNodeType::Mod] + t[IRNodeType::Mul];
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

bool variable_counts_gt(variable_count_map &m1, variable_count_map &m2) {
    for (auto const& var : m2) {
        if (var.first[0] != 'c' && !(m1[var.first] > var.second)) {
            return false;
        }
    }
    return true;
}

bool variable_counts_atleastone_gt(variable_count_map &m1, variable_count_map &m2) {
    for (auto const& var : m2) {
        if (var.first[0] != 'c' && (m1[var.first] > var.second)) {
            return true;
        }
    }
    return false;
}

bool term_map_gt(term_map &m1, term_map &m2) {
    if (m1[IRNodeType::Ramp] != m2[IRNodeType::Ramp]) {
        return m1[IRNodeType::Ramp] > m2[IRNodeType::Ramp];
    } else if (m1[IRNodeType::Broadcast] != m2[IRNodeType::Broadcast]) {
        return m1[IRNodeType::Broadcast] > m2[IRNodeType::Broadcast];
    } else if (m1[IRNodeType::Select] != m2[IRNodeType::Select]) {
        return m1[IRNodeType::Select] > m2[IRNodeType::Select];
    } else if (m1[IRNodeType::Div] != m2[IRNodeType::Div]) {
        return m1[IRNodeType::Div] > m2[IRNodeType::Div];
    } else if (m1[IRNodeType::Mul] != m2[IRNodeType::Mul]) {
        return m1[IRNodeType::Mul] > m2[IRNodeType::Mul];
    } else if (m1[IRNodeType::Mod] != m2[IRNodeType::Mod]) {
        return m1[IRNodeType::Mod] > m2[IRNodeType::Mod];
    } else if (m1[IRNodeType::Sub] != m2[IRNodeType::Sub]) {
        return m1[IRNodeType::Sub] > m2[IRNodeType::Sub];
    } else if (m1[IRNodeType::Add] != m2[IRNodeType::Add]) {
        return m1[IRNodeType::Add] > m2[IRNodeType::Add];
/*    } else if (m1[IRNodeType::Max] != m2[IRNodeType::Max]) {
        return m1[IRNodeType::Max] > m2[IRNodeType::Max];
    } else if (m1[IRNodeType::Min] != m2[IRNodeType::Min]) {
        return m1[IRNodeType::Min] > m2[IRNodeType::Min]; */
    } else if ((m1[IRNodeType::Max] + m1[IRNodeType::Min]) != (m2[IRNodeType::Max] + m2[IRNodeType::Min])) {
        return (m1[IRNodeType::Max] + m1[IRNodeType::Min]) > (m2[IRNodeType::Max] + m2[IRNodeType::Min]);
    } else if (m1[IRNodeType::Or] != m2[IRNodeType::Or]) {
        return m1[IRNodeType::Or] > m2[IRNodeType::Or];
    } else if (m1[IRNodeType::And] != m2[IRNodeType::And]) {
        return m1[IRNodeType::And] > m2[IRNodeType::And];
    } else if (m1[IRNodeType::GE] != m2[IRNodeType::GE]) {
        return m1[IRNodeType::GE] > m2[IRNodeType::GE];
    } else if (m1[IRNodeType::GT] != m2[IRNodeType::GT]) {
        return m1[IRNodeType::GT] > m2[IRNodeType::GT];
    } else if (m1[IRNodeType::LE] != m2[IRNodeType::LE]) {
        return m1[IRNodeType::LE] > m2[IRNodeType::LE];
    } else if (m1[IRNodeType::LT] != m2[IRNodeType::LT]) {
        return m1[IRNodeType::LT] > m2[IRNodeType::LT];
    } else if (m1[IRNodeType::NE] != m2[IRNodeType::NE]) {
        return m1[IRNodeType::NE] > m2[IRNodeType::NE];
    } else if (m1[IRNodeType::EQ] != m2[IRNodeType::EQ]) {
        return m1[IRNodeType::EQ] > m2[IRNodeType::EQ];
    } else if (m1[IRNodeType::Not] != m2[IRNodeType::Not]) {
        return m1[IRNodeType::Not] > m2[IRNodeType::Not];
    } else if (m1[IRNodeType::Cast] != m2[IRNodeType::Cast]) {
        return m1[IRNodeType::Cast] > m2[IRNodeType::Cast];
    } else if (m1[IRNodeType::FloatImm] != m2[IRNodeType::FloatImm]) {
        return m1[IRNodeType::FloatImm] > m2[IRNodeType::FloatImm];
    } else if (m1[IRNodeType::UIntImm] != m2[IRNodeType::UIntImm]) {
        return m1[IRNodeType::UIntImm] > m2[IRNodeType::UIntImm];
    } else if (m1[IRNodeType::IntImm] != m2[IRNodeType::IntImm]) {
        return m1[IRNodeType::IntImm] > m2[IRNodeType::IntImm];
    } else {
        return false; // two histograms are equiv
    }
}

CompIRNodeTypeStatus term_map_comp(term_map &m1, term_map &m2) {
    if (m1[IRNodeType::Ramp] != m2[IRNodeType::Ramp]) {
        debug(0) << "Terms count tie breaker " << " Ramp " << m1[IRNodeType::Ramp] << " " << m2[IRNodeType::Ramp] << " " << comp_to_s(ternary_comp(m1[IRNodeType::Ramp],m2[IRNodeType::Ramp])) << "\n";
        return ternary_comp(m1[IRNodeType::Ramp],m2[IRNodeType::Ramp]);
    } else if (m1[IRNodeType::Broadcast] != m2[IRNodeType::Broadcast]) {
        debug(0) << "Terms count tie breaker " << " Broadcast " << m1[IRNodeType::Broadcast] << " " << m2[IRNodeType::Broadcast] << " " << comp_to_s(ternary_comp(m1[IRNodeType::Broadcast],m2[IRNodeType::Broadcast])) << "\n";
        return ternary_comp(m1[IRNodeType::Broadcast], m2[IRNodeType::Broadcast]);
    } else if (m1[IRNodeType::Select] != m2[IRNodeType::Select]) {
        debug(0) << "Terms count tie breaker " << " Select " << m1[IRNodeType::Select] << " " << m2[IRNodeType::Select] << " " << comp_to_s(ternary_comp(m1[IRNodeType::Select],m2[IRNodeType::Select])) << "\n";
        return ternary_comp(m1[IRNodeType::Select], m2[IRNodeType::Select]);
    } else if (m1[IRNodeType::Div] != m2[IRNodeType::Div]) {
        debug(0) << "Terms count tie breaker " << " Div " << m1[IRNodeType::Div] << " " << m2[IRNodeType::Div] << " " << comp_to_s(ternary_comp(m1[IRNodeType::Div],m2[IRNodeType::Div])) << "\n";
        return ternary_comp(m1[IRNodeType::Div], m2[IRNodeType::Div]);
    } else if (m1[IRNodeType::Mul] != m2[IRNodeType::Mul]) {
        debug(0) << "Terms count tie breaker " << " Mul " << m1[IRNodeType::Mul] << " " << m2[IRNodeType::Mul] << " " << comp_to_s(ternary_comp(m1[IRNodeType::Mul],m2[IRNodeType::Mul])) << "\n";
        return ternary_comp(m1[IRNodeType::Mul], m2[IRNodeType::Mul]);
    } else if (m1[IRNodeType::Mod] != m2[IRNodeType::Mod]) {
        debug(0) << "Terms count tie breaker " << " Mod " << m1[IRNodeType::Mod] << " " << m2[IRNodeType::Mod] << " " << comp_to_s(ternary_comp(m1[IRNodeType::Mod],m2[IRNodeType::Mod])) << "\n";
        return ternary_comp(m1[IRNodeType::Mod], m2[IRNodeType::Mod]);
    } else if (m1[IRNodeType::Sub] != m2[IRNodeType::Sub]) { // Adds also go in this bucket
        debug(0) << "Terms count tie breaker " << " AddSub " << m1[IRNodeType::Sub] << " " << m2[IRNodeType::Sub] << " " << comp_to_s(ternary_comp(m1[IRNodeType::Sub],m2[IRNodeType::Sub])) << "\n";
        return ternary_comp(m1[IRNodeType::Sub], m2[IRNodeType::Sub]);
 //   } else if (m1[IRNodeType::Add] != m2[IRNodeType::Add]) {
 //       debug(0) << "Terms count tie breaker " << " Add " << m1[IRNodeType::Add] << " " << m2[IRNodeType::Add] << " " << comp_to_s(ternary_comp(m1[IRNodeType::Add],m2[IRNodeType::Add])) << "\n";
 //       return ternary_comp(m1[IRNodeType::Add], m2[IRNodeType::Add]);
    } else if (m1[IRNodeType::Min] != m2[IRNodeType::Min]) { // max ops go in this bucket too
        debug(0) << "Terms count tie breaker " << " MaxMin " << m1[IRNodeType::Min] << " " << m2[IRNodeType::Min] << " " << comp_to_s(ternary_comp(m1[IRNodeType::Min],m2[IRNodeType::Min])) << "\n";
        return ternary_comp(m1[IRNodeType::Min], m2[IRNodeType::Min]);
    } else if (m1[IRNodeType::Or] != m2[IRNodeType::Or]) {
        debug(0) << "Terms count tie breaker " << " Or " << m1[IRNodeType::Or] << " " << m2[IRNodeType::Or] << " " << comp_to_s(ternary_comp(m1[IRNodeType::Or],m2[IRNodeType::Or])) << "\n";
        return ternary_comp(m1[IRNodeType::Or], m2[IRNodeType::Or]);
    } else if (m1[IRNodeType::And] != m2[IRNodeType::And]) {
        debug(0) << "Terms count tie breaker " << " And " << m1[IRNodeType::And] << " " << m2[IRNodeType::And] << " " << comp_to_s(ternary_comp(m1[IRNodeType::And],m2[IRNodeType::And])) << "\n";
        return ternary_comp(m1[IRNodeType::And], m2[IRNodeType::And]);
    } else if (m1[IRNodeType::GE] != m2[IRNodeType::GE]) {
        debug(0) << "Terms count tie breaker " << " GE " << m1[IRNodeType::GE] << " " << m2[IRNodeType::GE] << " " << comp_to_s(ternary_comp(m1[IRNodeType::GE],m2[IRNodeType::GE])) << "\n";
        return ternary_comp(m1[IRNodeType::GE], m2[IRNodeType::GE]);
    } else if (m1[IRNodeType::GT] != m2[IRNodeType::GT]) {
        debug(0) << "Terms count tie breaker " << " GT " << m1[IRNodeType::GT] << " " << m2[IRNodeType::GT] << " " << comp_to_s(ternary_comp(m1[IRNodeType::GT],m2[IRNodeType::GT])) << "\n";
        return ternary_comp(m1[IRNodeType::GT], m2[IRNodeType::GT]);
    } else if (m1[IRNodeType::LE] != m2[IRNodeType::LE]) {
        debug(0) << "Terms count tie breaker " << " LE " << m1[IRNodeType::LE] << " " << m2[IRNodeType::LE] << " " << comp_to_s(ternary_comp(m1[IRNodeType::LE],m2[IRNodeType::LE])) << "\n";
        return ternary_comp(m1[IRNodeType::LE], m2[IRNodeType::LE]);
    } else if (m1[IRNodeType::LT] != m2[IRNodeType::LT]) {
        debug(0) << "Terms count tie breaker " << " LT " << m1[IRNodeType::LT] << " " << m2[IRNodeType::LT] << " " << comp_to_s(ternary_comp(m1[IRNodeType::LT],m2[IRNodeType::LT])) << "\n";
        return ternary_comp(m1[IRNodeType::LT], m2[IRNodeType::LT]);
    } else if (m1[IRNodeType::NE] != m2[IRNodeType::NE]) {
        debug(0) << "Terms count tie breaker " << " NE " << m1[IRNodeType::NE] << " " << m2[IRNodeType::NE] << " " << comp_to_s(ternary_comp(m1[IRNodeType::NE],m2[IRNodeType::NE])) << "\n";
        return ternary_comp(m1[IRNodeType::NE], m2[IRNodeType::NE]);
    } else if (m1[IRNodeType::EQ] != m2[IRNodeType::EQ]) {
        debug(0) << "Terms count tie breaker " << " EQ " << m1[IRNodeType::EQ] << " " << m2[IRNodeType::EQ] << " " << comp_to_s(ternary_comp(m1[IRNodeType::EQ],m2[IRNodeType::EQ])) << "\n";
        return ternary_comp(m1[IRNodeType::EQ], m2[IRNodeType::EQ]);
    } else if (m1[IRNodeType::Not] != m2[IRNodeType::Not]) {
        debug(0) << "Terms count tie breaker " << " Not " << m1[IRNodeType::Not] << " " << m2[IRNodeType::Not] << " " << comp_to_s(ternary_comp(m1[IRNodeType::Not],m2[IRNodeType::Not])) << "\n";
        return ternary_comp(m1[IRNodeType::Not], m2[IRNodeType::Not]);
        /*
    } else if (m1[IRNodeType::Cast] != m2[IRNodeType::Cast]) {
        debug(0) << "Terms count tie breaker " << " Cast " << m1[IRNodeType::Cast] << " " << m2[IRNodeType::Cast] << " " << comp_to_s(ternary_comp(m1[IRNodeType::Cast],m2[IRNodeType::Cast])) << "\n";
        return ternary_comp(m1[IRNodeType::Cast], m2[IRNodeType::Cast]);
    } else if (m1[IRNodeType::FloatImm] != m2[IRNodeType::FloatImm]) {
        debug(0) << "Terms count tie breaker " << " FloatImm " << m1[IRNodeType::FloatImm] << " " << m2[IRNodeType::FloatImm] << " " << comp_to_s(ternary_comp(m1[IRNodeType::FloatImm],m2[IRNodeType::FloatImm])) << "\n";
        return ternary_comp(m1[IRNodeType::FloatImm], m2[IRNodeType::FloatImm]);
    } else if (m1[IRNodeType::UIntImm] != m2[IRNodeType::UIntImm]) {
        debug(0) << "Terms count tie breaker " << " UIntImm " << m1[IRNodeType::UIntImm] << " " << m2[IRNodeType::UIntImm] << " " << comp_to_s(ternary_comp(m1[IRNodeType::UIntImm],m2[IRNodeType::UIntImm])) << "\n";
        return ternary_comp(m1[IRNodeType::UIntImm], m2[IRNodeType::UIntImm]);
    } else if (m1[IRNodeType::IntImm] != m2[IRNodeType::IntImm]) {
        debug(0) << "Terms count tie breaker " << " IntImm " << m1[IRNodeType::IntImm] << " " << m2[IRNodeType::IntImm] << " " << comp_to_s(ternary_comp(m1[IRNodeType::IntImm],m2[IRNodeType::IntImm])) << "\n";
        return ternary_comp(m1[IRNodeType::IntImm], m2[IRNodeType::IntImm]);
        */
    } else {
        return CompIRNodeTypeStatus::EQ; // two histograms are equiv
    }
}

HALIDE_ALWAYS_INLINE
bool equal_helper(const Expr &a, const Expr &b) {
    return equal(*a.get(), *b.get());
}

template<typename Op>
HALIDE_ALWAYS_INLINE
bool equal_helper_binop(const BaseExprNode &a, const BaseExprNode &b) {
    return (equal_helper(((const Op &)a).a, ((const Op &)b).a) &&
            equal_helper(((const Op &)a).b, ((const Op &)b).b));
}

HALIDE_ALWAYS_INLINE
bool equal_helper(int a, int b) {
    return a == b;
}

template<typename T>
HALIDE_ALWAYS_INLINE
bool equal_helper(const std::vector<T> &a, const std::vector<T> &b) {
    if (a.size() != b.size()) return false;
    for (size_t i = 0; i < a.size(); i++) {
        if (!equal_helper(a[i], b[i])) return false;
    }
    return true;
}

bool equal_helper(const BaseExprNode &a, const BaseExprNode &b) noexcept {
    switch(a.node_type) {
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
        ;
    }
    return false;
}

}  // namespace IRMatcher
}  // namespace Internal
}  // namespace Halide
