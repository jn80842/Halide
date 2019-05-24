#include "SMT2.h"

namespace Halide {
namespace Internal {

// walk Expr and produce string in SMT2 format
// walk Expr and produce typed sets of variables to declare in SMT2 query

class SMT2Formula : public IRVisitor {
public:
    std::string formula;
    Expr expr;
    SMT2Formula(std::string, Expr e);

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


std::string smt2formula(Expr e) {
	SMT2Formula phi = SMT2Formula(e);
	e.accept(&phi);
	return phi.formula;
}

}
}
