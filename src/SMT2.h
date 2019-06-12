#ifndef HALIDE_SMT2_H
#define HALIDE_SMT2_H

#include <string>
#include <set>
#include <map>
#include <cstdlib>
#include "Expr.h"
#include "IR.h"
#include "IRVisitor.h"

namespace Halide {
namespace Internal {

typedef std::map<IRNodeType, int> term_map;

int nt_count = 19;

IRNodeType node_strength[19] = {  IRNodeType::IntImm, IRNodeType::Add, IRNodeType::Sub, IRNodeType::Mul, IRNodeType::Div, IRNodeType::Mod, IRNodeType::Min, IRNodeType::EQ, IRNodeType::NE, IRNodeType::LT, IRNodeType::LE, IRNodeType::GT, IRNodeType::GE, IRNodeType::And, IRNodeType::Or, IRNodeType::Not, IRNodeType::Select, IRNodeType::Ramp, IRNodeType::Broadcast };

std::map<IRNodeType, int> nto = {
    {IRNodeType::Broadcast,18},
    {IRNodeType::Ramp,17},
    {IRNodeType::Select,16},
    {IRNodeType::Div,15},
    {IRNodeType::Mul,14},
    {IRNodeType::Mod,13},
    {IRNodeType::Sub,12},
    {IRNodeType::Add,11},
    {IRNodeType::Min,10}, // same strength as max
    {IRNodeType::Not,9},
    {IRNodeType::Or,8},
    {IRNodeType::And,7},
    {IRNodeType::GE,6},
    {IRNodeType::GT,5},
    {IRNodeType::LE,4},
    {IRNodeType::LT,3},
    {IRNodeType::NE,2},
    {IRNodeType::EQ,1},
    {IRNodeType::IntImm,0} // all immediates same strength
};

bool expr_gt(Expr e1, Expr e2);

std::string smt2formula(Expr e);
std::string smt2_declarations(Expr e);
std::string z3query_verifyequal(Expr e1, Expr e2);
std::string z3query_verifytrue(Expr e);

bool query_true(Expr e);
bool query_equivalence(Expr e1, Expr e2);

}
}

#endif
