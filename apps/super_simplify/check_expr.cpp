#include "Halide.h"
#include "parser.h"
#include "expr_util.h"
#include "synthesize_predicate.h"
#include "reduction_order.h"
#include "z3.h"

#include <fstream>

using namespace Halide;
using namespace Halide::Internal;

using std::vector;

void check_expr_via_z3(vector<Expr> &exprs) {
    for (const Expr &e : exprs) {
      Z3Result retval = z3_query(e);
      if (retval == Z3Result::Unsat) {
        debug(0) << "Z3TRUE: " << e << "\n";
      } else {
        debug(0) << "Z3UNPROVEN: " << e << "\n";
      }
    }
}

void check_expr_via_simplifer(vector<Expr> &exprs) {
  for (const Expr &e : exprs) {
    if (is_one(simplify(e))) {
      debug(0) << "STRUE: " << e << "\n";
    } else {
      debug(0) << "SUNPROVEN: " << e << "\n";
    }
  }
}

int main(int argc, char **argv) {
    if (argc < 2) {
        std::cout << "Usage: ./check_expr exprtocheck.txt\n";
        return 0;
    }

    vector<Expr> exprs_vec = parse_halide_exprs_from_file(argv[1]);

    check_expr_via_z3(exprs_vec);
    check_expr_via_simplifer(exprs_vec);

    debug(0) << "Done!\n";
}