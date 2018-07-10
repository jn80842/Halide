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
    Expr ci = int32(x);

//(((fold(((c0 + c1) - 1)) - _1) - ((_0 + fold((c1 % c0))) % c0)) / c0)
    //check(x + y, 3); // all rules verified
    //check(x + x*y, x); // all rules verified except for those using division
    //check(b1 && b1, b1);
    //check(max(x, y + c0) + c1, max(x + c1, y)); // all rules verified except for those using division
    //check(select(b1, 0, y) == 0,f);
    //check(b1 && b2,b1);
    //heck(x - y, 7);
    //check(select(broadcast(x), y, z), select(x, y, z));
    //check(select(Expr(broadcast(b1, 2)), y, z), select(b1, y, z));
    //check(Broadcast::make(x,3) + Broadcast::make(y,3), Broadcast::make(x + y, 3));
    //check(ramp(x, y,10) + ramp(z, w,10), ramp(x + z, y + w, 10));
    //check(broadcast(x,3) + broadcast(y,3), broadcast(x + 7, 3));
    //check(ramp(x, y, 3) + broadcast(z, 3), ramp(x + z, y, 3));
    //check(x - max(x,y), min(0,x-y));
    //check(x / y, x);
    //check(x + c0, c0 + x);
    check((x + ci) + y, (x + y) + ci);
    printf("Success!\n");

    return 0;
}