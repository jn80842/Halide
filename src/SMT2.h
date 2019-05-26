#ifndef HALIDE_SMT2_H
#define HALIDE_SMT2_H

#include <string>
#include <set>
#include "Expr.h"
#include "IRVisitor.h"

namespace Halide {
namespace Internal {

std::string smt2formula(Expr e);
std::string smt2_declarations(Expr e);
std::string z3query_verifyequal(Expr e1, Expr e2);

}
}

#endif
