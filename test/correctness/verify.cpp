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
    Expr xf = cast<float>(x);
    Expr yf = cast<float>(y);
    Expr t = const_true(), f = const_false();
    Expr b1 = Variable::make(Bool(), "b1");
    Expr b2 = Variable::make(Bool(), "b2");

    check(x + x, 3);

    printf("Success!\n");

    return 0;
}