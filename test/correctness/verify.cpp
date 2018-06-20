#include "Halide.h"

using namespace Halide;
using namespace Halide::Internal;

#define internal_assert _halide_user_assert

void check(const Expr &a, const Expr &b) {
    std::cout << "called expr check\n";
    Expr simpler = simplify(a);
    if (!equal(simpler, b)) {
        std::cerr
            << "\nSimplification failure:\n"
            << "Input: " << a << '\n'
            << "Output: " << simpler << '\n'
            << "Expected output: " << b << '\n';
        abort();
    }
}

void check(const Stmt &a, const Stmt &b) {
    std::cout << "called stmt check\n";
    Stmt simpler = simplify(a);
    if (!equal(simpler, b)) {
        std::cerr
            << "\nSimplification failure:\n"
            << "Input: " << a << '\n'
            << "Output: " << simpler << '\n'
            << "Expected output: " << b << '\n';
        abort();
    }
}

int main(int argc, char **argv) {
    Expr x = Var("x"), y = Var("y"), z = Var("z"), w = Var("w");
    Expr c0 = Var("c0"), c1 = Var("c1");
    Expr xf = cast<float>(x);
    Expr yf = cast<float>(y);
    Expr t = const_true(), f = const_false();
    Expr b1 = Variable::make(Bool(), "b1");
    Expr b2 = Variable::make(Bool(), "b2");

    check(x + y, 3); // all rules verified
    //check(x + x*y, x); // all rules verified except for those using division
    //check(b1 && b1, b1);
    //check(max(x, y + c0) + c1, max(x + c1, y)); // all rules verified except for those using division
    //check(select(b1, 0, y) == 0,f);
    //check(b1 && b2,b1);

    printf("Success!\n");

    return 0;
}