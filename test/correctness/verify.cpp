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

void check (const Expr &a) {
    std::cout << "called expr check " << a << "\n";
    simplify(a);
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

    check(x + y);
    check(b1 && b2);
    check(x / y);
    check(xf / c0);
    check(x == 1);
    check(b1 == b2);
    check(x < y);
    check(xf < yf);
    check(max(x,y));
    check(min(x,y));
    check(x % y);
    check(x * y);
    check(!b1);
    check(b1 || b2);
    check(select(b1,x,y));
    check(select(b1,b2,b3));
    check(x - y);
    check(x > y);
    check(x + (y + (c0 - x)/c1)*c1);

    printf("Success!\n");

    return 0;
}