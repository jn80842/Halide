#ifndef HALIDE_SMT2_H
#define HALIDE_SMT2_H

//using std::string;
#include <string>
#include "Expr.h"
#include "IRVisitor.h"

namespace Halide {
namespace Internal {
/*
std::string smt2formula(Expr e);
*/




std::string smt2formula(Expr e);

}
}

#endif
