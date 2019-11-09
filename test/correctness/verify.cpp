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
    std::cout << "called expr check " << simplify(a) << "\n";
    simplify(a);
}

int main(int argc, char **argv) {
    Expr x = Var("x"), y = Var("y"), z = Var("z"), w = Var("w");
    Expr c0 = Var("c0"), c1 = Var("c1");
    Expr t = const_true(), f = const_false();
    Expr b1 = Variable::make(Bool(), "b1");
    Expr b2 = Variable::make(Bool(), "b2");
    Expr b3 = Variable::make(Bool(), "b3");
    Expr v0 = Var("v0"), v1 = Var("v1"), v2 = Var("v2"), v3 = Var("v3"), v4 = Var("v4");
    Expr v5 = Var("v5"), v6 = Var("v6"), v7 = Var("v7"), v8 = Var("v8"), v9 = Var("v9");
    Expr v10 = Var("v10"), v11 = Var("v11"), v12 = Var("v12"), v13 = Var("v13"), v14 = Var("v14");
    Expr v15 = Var("v15"), v16 = Var("v16"), v17 = Var("v17"), v18 = Var("v18"), v19 = Var("v19");

    check(x + y);
    
    check(b1 && b2);
    check(x / y);
    check(x == 1);
    check(b1 == b2);
    check(x < y);
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

   // check(((((((true && ((0 + ((min(((v1 - v2)/4), 0)*4) + v2)) <= (0 + ((min(((v1 - v2)/4), 0)*4) + v2)))) && ((3 + ((((v1 - v2)/4)*4) + v2)) >= (3 + ((((v1 - v2)/4)*4) + v2)))) && ((select((0 < v7), (min(((v6*17) + (v7*2)), ((v13 - v10) + 1)) + (v9 + v10)), (((v6*17) + (v7*2)) + (v9 + v10))) + -1) <= ((((v6*17) + (v7*2)) + (v9 + v10)) + -1))) && (((min((v13 - v10), ((min((v7*2), 15) + (v6*17)) + 1)) + (v9 + v10)) + -1) >= ((min((v13 - v10), ((min((v7*2), 15) + (v6*17)) + 1)) + (v9 + v10)) + -1))) && (0 <= 0)) && (2 >= 2)));
    printf("Success!\n");

    return 0;
}