#include "Halide.h"

using std::vector;

using namespace Halide;
using namespace Halide::Internal;

#define internal_assert _halide_user_assert

Expr ramp(const Expr &base, const Expr &stride, int w) {
    return Ramp::make(base, stride, w);
}

Expr broadcast(const Expr &base, int w) {
    return Broadcast::make(base, w);
}

void print_smt2 (const Expr &a) {
    std::cout << smt2formula(a) << "\n";
}

void print_smt2_declarations(const Expr &a) {
    std::cout << smt2_declarations(a) << "\n";
}

void print_equal_formula(const Expr &a, const Expr &b) {
    std::cout << z3query_verifyequal(a, b) << "\n";
}

int main(int argc, char **argv) {
    Expr x = Var("x"), y = Var("y"), z = Var("z"), w = Var("w");
    Expr t = const_true(), f = const_false();
    Expr b1 = Variable::make(Bool(), "b1");
    Expr b2 = Variable::make(Bool(), "b2");
    Expr b3 = Variable::make(Bool(), "b3");
    Expr c0 = Var("c0"), c1 = Var("c1"), c2 = Var("c2");

    if (smt2formula(x + y) != "(+ x y)") {
        printf("Failed Expr x + y --> ");
        print_smt2(x + y);
        return -1;
    }

    if (smt2_declarations(x * x) != "(declare-const x Int) ") {
        printf("Failed x * x var declarations --> ");
        print_smt2_declarations(x * x);
        return -1;
    }

    if (not (expr_gt(x * x, x + x))) {
        printf("Failed: x * x should be greater than x + x\n");
        return -1;
    }

    if (not (expr_gt(select(b1, x, y) < y, select(b1, x < y, f)))) {
        printf("Failed: select(b1, x, y) < y should be greater than select(b1, x < y, f)\n");
        return -1;
    }

    if (!(query_equivalence(x + y, y + x))) {
        printf("Failed: z3 equivalent check of x + y and y + x failed\n");
        return -1;
    }

    if (!(query_equivalence(x * 2, x + x))) {
        printf("Failed: z3 equivalent check of x * 2 and x + y failed\n");
        return -1;
    }

    vector<Expr> ground_int_exprs;
    vector<Expr> ground_bool_exprs;
    ground_int_exprs.push_back(x);
    ground_int_exprs.push_back(2);

    vector<Expr> int_exprs = build_int_expressions(ground_int_exprs, ground_bool_exprs);

    std::cout << "int_exprs contains " << int_exprs.size() << " elements.\n";
    Expr working_expr;

    for (auto it = int_exprs.begin(); it != int_exprs.end(); ++it) {
        working_expr = *it;
        if (expr_gt(x * 2, working_expr)) {
            std::cout << "Less than x * 2: " << working_expr << "\n";
        }
       if (query_equivalence(x * 2, working_expr)) {
            std::cout << "Equivalent to x * 2: " << working_expr << "\n";
        }
    }

    printf("Success!\n");

    return 0;
}