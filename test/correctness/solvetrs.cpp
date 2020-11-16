
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

void exercise(const Expr &e, const std::string &v) {
	solve_trs_expression(e, v);
}

void check (const Expr &a, const std::string &v, const Expr &b) {
   Expr solved = solve_trs_expression(a, v);
   if (!equal(solved, b)) {
   	std::cerr
   		<< "\nSolveTRS failure:\n"
   		<< "Input: " << a << "\n"
   		<< "Output: " << solved << "\n"
   		<< "Expected output: " << b << "\n";
   }
}

int main(int argc, char **argv) {
    Expr x = Var("x"), y = Var("y"), z = Var("z"), w = Var("w");
    Expr c0 = Var("c0"), c1 = Var("c1");
    Expr t = const_true(), f = const_false();
    Expr b1 = Variable::make(Bool(), "b1");
    Expr b2 = Variable::make(Bool(), "b2");
    Expr b3 = Variable::make(Bool(), "b3");

    check(3 + x, "x", x + 3);
    check((x - y) + z, "x", x + (z - y));
    check((x + y) + z, "x", x + (y + z));
    check(y - (z - x), "x", x + (y - z));

    exercise(x + y, "x");
    exercise(y - x, "y");
    exercise(x * y, "x");
    exercise(x / y, "x");

    printf("Finished!\n");

    return 0;

}