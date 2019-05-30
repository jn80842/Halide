#include "EnumerateExpr.h"

namespace Halide {
namespace Internal {

vector<Expr> build_int_expressions(vector<Expr> int_exprs,vector<Expr> bool_exprs) {
	vector<Expr> return_int_exprs;
	for (auto it1 = int_exprs.begin(); it1 != int_exprs.end(); ++it1) {
		for (auto it2 = int_exprs.begin(); it2 != int_exprs.end(); ++it2) {
			return_int_exprs.push_back(Add::make(*it1, *it2));
			return_int_exprs.push_back(Sub::make(*it1, *it2));
			return_int_exprs.push_back(Mul::make(*it1, *it2));
			return_int_exprs.push_back(Div::make(*it1, *it2));
			return_int_exprs.push_back(Mod::make(*it1, *it2));
			return_int_exprs.push_back(Min::make(*it1, *it2));
			return_int_exprs.push_back(Max::make(*it1, *it2));
			for (auto it3 = bool_exprs.begin(); it3 != bool_exprs.end(); ++it3) {
				return_int_exprs.push_back(Select::make(*it3, *it1, *it2));
			}
		}
	}
	return return_int_exprs;
}

vector<Expr> build_bool_expressions(vector<Expr> int_exprs, vector<Expr> bool_exprs) {
	vector<Expr> return_bool_exprs;
	for (auto it1 = int_exprs.begin(); it1 != int_exprs.end(); ++it1) {
		for (auto it2 = int_exprs.begin(); it2 != int_exprs.end(); ++it2) {
			return_bool_exprs.push_back(EQ::make(*it1, *it2));
			return_bool_exprs.push_back(LT::make(*it1, *it2));
		}
	}
	for (auto it1 = bool_exprs.begin(); it1 != bool_exprs.end(); ++it1) {
		return_bool_exprs.push_back(Not::make(*it1));
		for (auto it2 = bool_exprs.begin(); it2 != bool_exprs.end(); ++it2) {
			return_bool_exprs.push_back(And::make(*it1, *it2));
			return_bool_exprs.push_back(Or::make(*it1, *it2));
			for (auto it3 = bool_exprs.begin(); it3 != bool_exprs.end(); ++it3) {
				return_bool_exprs.push_back(Select::make(*it3, *it1, *it2));
			}
		}
	}
	return return_bool_exprs;
}

}
}