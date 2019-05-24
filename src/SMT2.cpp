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
    void visit(const Add *op) override {
        formula += "(+ ";
        op->a.accept(this);
        formula += " ";
        op->b.accept(this);
        formula += " )";
    }
};

SMT2Formula::SMT2Formula(std::string s, Expr e) {
    formula = s;
    expr = e;
}


std::string smt2formula(Expr e) {
	SMT2Formula phi = SMT2Formula("hello",e);
	e.accept(&phi);
	return phi.formula;
}

}
}
