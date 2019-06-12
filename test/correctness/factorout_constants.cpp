#include "Halide.h"

using namespace Halide;
using namespace Halide::Internal;

#define internal_assert _halide_user_assert

#include <iostream>
#include <fstream>

using std::map;
using std::string;
using std::to_string;

Expr ramp(const Expr &base, const Expr &stride, int w) {
    return Ramp::make(base, stride, w);
}

Expr broadcast(const Expr &base, int w) {
    return Broadcast::make(base, w);
}

class RenameVariables : public IRMutator {
    map<string, string> varnames_map;
    string prefix;
    int counter = 0;

    using IRMutator::visit;
    Expr visit(const Variable *op) override {
        if (varnames_map.count(op->name) == 0) {
            varnames_map[op->name] = prefix + to_string(counter);
            counter++;  
        }
        return Variable::make(op->type, varnames_map[op->name]);
    }
public:
    RenameVariables(string prefix);
};
RenameVariables::RenameVariables(string p) {
    prefix = p;
}

Expr rename_variables(Expr e, string prefix) {
    // take 2 passes to avoid stepping on existing vars
    Expr pass1 = RenameVariables("VAR").mutate(e);
    return RenameVariables(prefix).mutate(e);
}

class ReplaceConstants : public IRMutator {
    map<int, string> constant_map;

    using IRMutator::visit;
    Expr visit (const IntImm *imm) override {
        if (constant_map.count(imm->value) == 1) {
            return Variable::make(imm->type, constant_map[imm->value]);
        } else {
            return IRMutator::visit(imm);
        }
    }
public:
    ReplaceConstants(map<int, string> constant_map);
};

ReplaceConstants::ReplaceConstants(map<int, string> cm) {
    constant_map = cm;
}

class ConstantMappings : public IRVisitor {
    int counter = 0;

    void update_map(int c) {
        if (constant_map.count(c) == 0) {
            constant_map[c] = "c" + to_string(counter);
            counter++;
        }
    }

    using IRVisitor::visit;
    void visit(const IntImm *imm) override {
        update_map(imm->value);
    }
    void visit(const UIntImm *imm) override {
        if (imm->type.bits() != 1)
            update_map(imm->value);
    }
public: 
    map<int, string> constant_map;
    ConstantMappings(Expr e);
};

ConstantMappings::ConstantMappings(Expr e) {
    e.accept(this);
}


void check (const Expr &a) {
    std::cout << "called expr check " << simplify(a) << "\n";
    simplify(a);
}

Expr factor_constants(Expr e) {
    ConstantMappings cm = ConstantMappings(e);
    map<int, string> replaceable;

    for (auto c : cm.constant_map) {
        map<int, string> one_const;
        one_const[c.first] = c.second;
        if (query_true(ReplaceConstants(one_const).mutate(e))) {
            replaceable[c.first] = c.second;
        }
    }

    return rename_variables(ReplaceConstants(replaceable).mutate(e), "v");

}

int main(int argc, char **argv) {
    Expr x = Var("x"), y = Var("y"), z = Var("z"), w = Var("w");
    Expr c0 = Var("c0"), c1 = Var("c1"), c2 = Var("c2");
    Expr t = const_true(), f = const_false();
    Expr b1 = Variable::make(Bool(), "b1");
    Expr b2 = Variable::make(Bool(), "b2");
    Expr b3 = Variable::make(Bool(), "b3");
    Expr v0 = Var("v0"), v1 = Var("v1"), v2 = Var("v2"), v3 = Var("v3"), v4 = Var("v4");
    Expr v5 = Var("v5"), v6 = Var("v6"), v7 = Var("v7"), v8 = Var("v8"), v9 = Var("v9");
    Expr v10 = Var("v10"), v11 = Var("v11"), v12 = Var("v12"), v13 = Var("v13"), v14 = Var("v14");
    Expr v15 = Var("v15"), v16 = Var("v16"), v17 = Var("v17"), v18 = Var("v18"), v19 = Var("v19");

    Expr original = ((((((true && ((0 + ((min((((v4 + 3)/4)*4), -9) + ((v1*125) + v2)) + 4)) <= (0 + ((min((((v4 + 3)/4)*4), -9) + ((v1*125) + v2)) + 4)))) && ((3 + ((min((((v4 + 15)/4)*4), ((((v4 + 3)/4)*4) + 9)) + ((v1*125) + v2)) + -5)) >= (3 + (min(((((v4 + 15)/4)*4) + (((((((v4 + 3)/4)*4) + 12)/35)*35) + ((v1*125) + v2))), (((((v4 + 3)/4)*4) + ((v1*125) + v2)) + 9)) + -5)))) && (min((((v9*32) + ((v6*63) + v7)) + -2), (min((v9*32), v11) + ((v6*63) + v7))) <= (((v9*32) + ((v6*63) + v7)) + -2))) && (((min(((v9*32) + 32), v11) + ((v6*63) + v7)) + -1) >= ((min(((v9*32) + 32), v11) + ((v6*63) + v7)) + -1))) && (v12 <= v12)) && (v12 >= v12));
    Expr simplified_e = simplify(original);
    std::cout << factor_constants(simplified_e) << "\n";

    string line;
    std::ifstream myfile ("/Users/mpu/research/termrewriting/resimplify/10.txt");
    if (myfile.is_open()) {
        while (getline(myfile, line)) {
            std::cout << line << "\n";
        }
        myfile.close();
    }

    printf("Success!\n");

    return 0;
}