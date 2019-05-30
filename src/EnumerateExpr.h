#ifndef HALIDE_ENUMEXPR_H
#define HALIDE_ENUMEXPR_H

#include "Expr.h"
#include "IR.h"

using std::vector;

namespace Halide {
namespace Internal {

vector<Expr> build_int_expressions(vector<Expr> int_exprs, vector<Expr> bool_exprs);
vector<Expr> build_bool_expressions(vector<Expr> int_exprs, vector<Expr> bool_exprs);

}
}

#endif
