#include "SMT2.h"

namespace Halide {
namespace Internal {

class SMT2Formula : public IRVisitor {
public:
    std::string formula;
    Expr expr;
    SMT2Formula(Expr e);

    using IRVisitor::visit;
    void visit(const IntImm *imm) override {
        if (imm->type.bits() == 1) {
            if (imm->value == 1) {
                formula += "true";
            } else {
                formula += "false";
            }
        } else {
            formula += std::to_string(imm->type.bits());
        }
    }
    void visit(const UIntImm *imm) override {
        if (imm->type.bits() == 1) {
            if (imm->value == 1) {
                formula += "true";
            } else {
                formula += "false";
            }
        } else {
            formula += std::to_string(imm->type.bits());
        }
    }
    void visit(const FloatImm *imm) override {
        formula += imm->value;
    }
    void visit(const StringImm *imm) override {
        formula += imm->value;
    }
    void visit(const Variable *var) override {
        formula += var->name;
    }
    void visit(const Add *op) override {
        formula += "(+ ";
        op->a.accept(this);
        formula += " ";
        op->b.accept(this);
        formula += ")";
    }
    void visit(const Sub *op) override {
        formula += "(- ";
        op->a.accept(this);
        formula += " ";
        op->b.accept(this);
        formula += ")";
    }
    void visit(const Mul *op) override {
        formula += "(* ";
        op->a.accept(this);
        formula += " ";
        op->b.accept(this);
        formula += ")";
    }
    void visit(const Div *op) override {
        formula += "(div ";
        op->a.accept(this);
        formula += " ";
        op->b.accept(this);
        formula += ")";
    }
    void visit(const Mod *op) override {
        formula += "(mod ";
        op->a.accept(this);
        formula += " ";
        op->b.accept(this);
        formula += ")";
    }
    void visit(const Min *op) override {
        formula += "(min ";
        op->a.accept(this);
        formula += " ";
        op->b.accept(this);
        formula += ")";
    }
    void visit(const Max *op) override {
        formula += "(max ";
        op->a.accept(this);
        formula += " ";
        op->b.accept(this);
        formula += ")";
    }
    void visit(const EQ *op) override {
        formula += "(= ";
        op->a.accept(this);
        formula += " ";
        op->b.accept(this);
        formula += ")";
    }
    void visit(const NE *op) override {
        formula += "(not (= ";
        op->a.accept(this);
        formula += " ";
        op->b.accept(this);
        formula += "))";
    }
    void visit(const LT *op) override {
        formula += "(< ";
        op->a.accept(this);
        formula += " ";
        op->b.accept(this);
        formula += ")";
    }
    void visit(const LE *op) override {
        formula += "(<= ";
        op->a.accept(this);
        formula += " ";
        op->b.accept(this);
        formula += ")";
    }
    void visit(const GT *op) override {
        formula += "(> ";
        op->a.accept(this);
        formula += " ";
        op->b.accept(this);
        formula += ")";
    }
    void visit(const GE *op) override {
        formula += "(>= ";
        op->a.accept(this);
        formula += " ";
        op->b.accept(this);
        formula += ")";
    }
    void visit(const And *op) override {
        formula += "(and ";
        op->a.accept(this);
        formula += " ";
        op->b.accept(this);
        formula += ")";
    }
    void visit(const Or *op) override {
        formula += "(or ";
        op->a.accept(this);
        formula += " ";
        op->b.accept(this);
        formula += ")";
    }
    void visit(const Not *op) override {
        formula += "(not ";
        op->a.accept(this);
        formula += ")";
    }
    void visit(const Select *op) override {
        formula += "(ite ";
        op->condition.accept(this);
        formula += " ";
        op->true_value.accept(this);
        formula += " ";
        op->false_value.accept(this);
        formula += ")";
    }
    void visit(const Ramp *op) override {
        formula += "(+ ";
        op->base.accept(this);
        formula += " (* ";
        op->stride.accept(this);
        formula += " (- ";
        formula += std::to_string(op->lanes);
        formula += " 1)))";
    }
    void visit(const Broadcast *op) override {
        op->value.accept(this);
    }
};

SMT2Formula::SMT2Formula(Expr e) {
    formula = "";
    expr = e;
}

class SMT2Variables : public IRVisitor {
public:
    std::set<std::string> varset;
    std::string decls;
    SMT2Variables(Expr e);

    using IRVisitor::visit;
    void visit(const Variable *var) override {
        varset.insert(var->name);
    }
};

SMT2Variables::SMT2Variables(Expr e) {
    e.accept(this);
    for (auto v : varset) {
        // note assumption that all variables are of integer type
        decls += "(declare-const " + v + " Int)\n";
    }
}

void increment_term(IRNodeType node_type, term_map &m) {
    if (m.count(node_type) == 0) {
        m[node_type] = 1;
    } else {
        m[node_type] = m[node_type] + 1;
    }
}

class HistoReductionOrder : public IRVisitor {
public:
    term_map histo;
    HistoReductionOrder(Expr e);

    int get_histo_value(IRNodeType nt) {
        return histo[nt];
    }

    using IRVisitor::visit;
    // don't count immediates
    // we can't count variables, and if we count immediates, we de facto make immediates stronger than variables
    void visit(const Add *op) override {
        increment_term(IRNodeType::Add, histo);
        op->a.accept(this);
        op->b.accept(this);
    }
    void visit(const Sub *op) override {
        increment_term(IRNodeType::Sub, histo);
        op->a.accept(this);
        op->b.accept(this);
    }
    void visit(const Mul *op) override {
        increment_term(IRNodeType::Mul, histo);
        op->a.accept(this);
        op->b.accept(this);
    }
    void visit(const Div *op) override {
        increment_term(IRNodeType::Div, histo);
        op->a.accept(this);
        op->b.accept(this);
    }
    void visit(const Mod *op) override {
        increment_term(IRNodeType::Mod, histo);
        op->a.accept(this);
        op->b.accept(this);
    }
    // min and max are tabulated together
    void visit(const Min *op) override {
        increment_term(IRNodeType::Min, histo);
        op->a.accept(this);
        op->b.accept(this);
    }
    void visit(const Max *op) override {
        increment_term(IRNodeType::Min, histo);
        op->a.accept(this);
        op->b.accept(this);
    }
    void visit(const EQ *op) override {
        increment_term(IRNodeType::EQ, histo);
        op->a.accept(this);
        op->b.accept(this);
    }
    void visit(const LT *op) override {
        increment_term(IRNodeType::LT, histo);
        op->a.accept(this);
        op->b.accept(this);
    }
    // should NE, LE, GT, GE be counted, or desugared into 2 ops?
    void visit(const NE *op) override {
        increment_term(IRNodeType::NE,histo);
        op->a.accept(this);
        op->b.accept(this);
    }
    void visit(const LE *op) override {
        increment_term(IRNodeType::LE, histo);
        op->a.accept(this);
        op->b.accept(this);
    }
    void visit(const GT *op) override {
        increment_term(IRNodeType::GT, histo);
        op->a.accept(this);
        op->b.accept(this);
    }
    void visit(const GE *op) override {
        increment_term(IRNodeType::GE, histo);
        op->a.accept(this);
        op->b.accept(this);
    }
    void visit(const And *op) override {
        increment_term(IRNodeType::And, histo);
        op->a.accept(this);
        op->b.accept(this);
    }
    void visit(const Or *op) override {
        increment_term(IRNodeType::Or, histo);
        op->a.accept(this);
        op->b.accept(this);
    }
    void visit(const Not *op) override {
        increment_term(IRNodeType::Not, histo);
        op->a.accept(this);
    }
    void visit(const Select *op) override {
        increment_term(IRNodeType::Select, histo);
        op->condition.accept(this);
        op->true_value.accept(this);
        op->false_value.accept(this);
    }
    void visit(const Ramp *op) override {
        increment_term(IRNodeType::Ramp, histo);
        op->base.accept(this);
        op->stride.accept(this);
    }
    void visit(const Broadcast *op) override {
        increment_term(IRNodeType::Broadcast, histo);
        op->value.accept(this);
    }
};

HistoReductionOrder::HistoReductionOrder(Expr e) {
    e.accept(this);
}

class RootNodeReductionOrder : public IRVisitor {
public:
    IRNodeType root;
    RootNodeReductionOrder(Expr e);

    using IRVisitor::visit;
    // all immediates are IntImm
    void visit(const IntImm *imm) override {
        root = IRNodeType::IntImm;
    }
    void visit(const UIntImm *imm) override {
        root = IRNodeType::IntImm;
    }
    void visit(const FloatImm *imm) override {
        root = IRNodeType::IntImm;
    }
    void visit(const StringImm *imm) override {
        root = IRNodeType::IntImm;
    }
    void visit(const Add *op) override {
        root = IRNodeType::Add;
    }
    void visit(const Sub *op) override {
        root = IRNodeType::Sub;
    }
    void visit(const Mul *op) override {
        root = IRNodeType::Mul;
    }
    void visit(const Div *op) override {
        root = IRNodeType::Div;
    }
    void visit(const Mod *op) override {
        root = IRNodeType::Mod;
    }
    // min and max are ranked the same
    void visit(const Min *op) override {
        root = IRNodeType::Min;
    }
    void visit(const Max *op) override {
        root = IRNodeType::Min;
    }
    void visit(const EQ *op) override {
        root = IRNodeType::EQ;
    }
    void visit(const LT *op) override {
        root = IRNodeType::LT;
    }
    void visit(const NE *op) override {
        root = IRNodeType::NE;
    }
    void visit(const LE *op) override {
        root = IRNodeType::LE;
    }
    void visit(const GT *op) override {
        root = IRNodeType::GT;
    }
    void visit(const GE *op) override {
        root = IRNodeType::GE;
    }
    void visit(const And *op) override {
        root = IRNodeType::And;
    }
    void visit(const Or *op) override {
        root = IRNodeType::Or;
    }
    void visit(const Not *op) override {
        root = IRNodeType::Not;
    }
    void visit(const Select *op) override {
        root = IRNodeType::Select;
    }
    void visit(const Ramp *op) override {
        root = IRNodeType::Ramp;
    }
    void visit(const Broadcast *op) override {
        root = IRNodeType::Broadcast;
    }
};

RootNodeReductionOrder::RootNodeReductionOrder(Expr e) {
    e.accept(this);
}

bool expr_gt(Expr e1, Expr e2) {
    HistoReductionOrder h1 = HistoReductionOrder(e1);
    HistoReductionOrder h2 = HistoReductionOrder(e2);
    for (int i = nt_count; i > -1; --i) {
        if (h1.get_histo_value(node_strength[i]) != h2.get_histo_value(node_strength[i])) {
            return h1.get_histo_value(node_strength[i]) > h2.get_histo_value(node_strength[i]);
        }
    }
    return nto[RootNodeReductionOrder(e1).root] < nto[RootNodeReductionOrder(e2).root];
}

std::string smt2_declarations(Expr e) {
    SMT2Variables declarations = SMT2Variables(e);
    return declarations.decls;
}

std::string smt2formula(Expr e) {
	SMT2Formula phi = SMT2Formula(e);
	e.accept(&phi);
	return phi.formula;
}

std::string z3query_body(std::string assert_smt) {
    std::string phi = "(define-fun min ((x Int) (y Int)) Int (ite (> x y) x y))\n";
    phi += "(define-fun max ((x Int) (y Int)) Int (ite (> x y) y x))\n";
    phi += "(declare-const lanes Int)\n";
    phi += "(assert (> lanes 1))\n\n";
    phi += assert_smt;
    phi += "\n\n(check-sat)\n(get-model)";
    return phi;
}

std::string z3query_verifyequal(Expr e1, Expr e2) {
    // assumption 1: no variables in e2 that are not present in e1 (necessary for valid rule)
    // assumption 2: all variables are of Int type
    return smt2_declarations(e1) + z3query_body("(assert (not (= " + smt2formula(e1) + " " + smt2formula(e2) + ")))");
}

}
}
