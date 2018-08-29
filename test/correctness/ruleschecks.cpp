#include "Halide.h"

using namespace Halide;
using namespace Halide::Internal;

#define internal_assert _halide_user_assert

Expr ramp(const Expr &base, const Expr &stride, int w) {
    return Ramp::make(base, stride, w);
}

Expr broadcast(const Expr &base, int w) {
    return Broadcast::make(base, w);
}

void check(const Expr &a, const Expr &b) {

    Expr simpler = simplify(a);
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
    Expr b3 = Variable::make(Bool(), "b3");

    check(x + y, 4);
    check(b1 && b2, 5);
    check(x / y, 5);
    check(xf / c0, 5);
    check(x == 1, true);
    check(b1 == b2, true);
    check(x < y, false);
    check(xf < yf, false);
    check(max(x,y),4);
    check(min(x,y),4);
    check(x % y, 5);
    check(x * y, 5);
    check(!b1, false);
    check(b1 || b2, false);
    check(select(b1,x,y),3);
    check(select(b1,b2,b3),false);
    check(x - y, 5);
    check(x > y, true);
    check(x + (y + (c0 - x)/c1)*c1, 5);

    printf("Finished!\n");

    return 0;
}