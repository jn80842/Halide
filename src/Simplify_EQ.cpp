#include "Simplify_Internal.h"

namespace Halide {
namespace Internal {

Expr Simplify::visit(const EQ *op, ExprInfo *bounds) {
    if (truths.count(op)) {
        return const_true(op->type.lanes());
    } else if (falsehoods.count(op)) {
        return const_false(op->type.lanes());
    }

    // Order commutative operations by node type
    Expr a = op->a;
    Expr b = op->b;
    if (should_commute(a, b)) {
        std::swap(a, b);
    }

    if (!may_simplify(a.type())) {
        a = mutate(a, nullptr);
        b = mutate(b, nullptr);
        if (a.same_as(op->a) && b.same_as(op->b)) {
            return op;
        } else {
            return EQ::make(a, b);
        }
    }

    if (op->a.type().is_bool()) {
        a = mutate(a, nullptr);
        b = mutate(b, nullptr);
        const int lanes = op->type.lanes();
        auto rewrite = IRMatcher::rewriter(IRMatcher::eq(a, b), op->type);
        if (rewrite(x == 1, x)) {
            return rewrite.result;
        } else if (rewrite(x == 0, !x)) {
            return mutate(std::move(rewrite.result), bounds);
        } else if (rewrite(x == x, const_true(lanes))) {
            return rewrite.result;
        } else if (a.same_as(op->a) && b.same_as(op->b)) {
            return op;
        } else {
            return EQ::make(a, b);
        }
    }

    ExprInfo delta_bounds;
    Expr delta = mutate(a - b, &delta_bounds);
    const int lanes = op->type.lanes();

    // If the delta is 0, then it's just x == x
    if (is_zero(delta)) {
        return const_true(lanes);
    }

    // Attempt to disprove using bounds analysis
    if (delta_bounds.min_defined && delta_bounds.min > 0) {
        return const_false(lanes);
    }

    if (delta_bounds.max_defined && delta_bounds.max < 0) {
        return const_false(lanes);
    }

    // Attempt to disprove using modulus remainder analysis
    if (delta_bounds.alignment.remainder != 0) {
        return const_false(lanes);
    }

    auto rewrite = IRMatcher::rewriter(IRMatcher::eq(delta, 0), op->type, delta.type());

    if (
        (get_rule_flag("eq74", rflag) && rewrite(broadcast(x) == 0, broadcast(x == 0, lanes), "eq74")) ||
        (no_overflow(delta.type()) && (get_rule_flag("eq75", rflag) && rewrite(x * y == 0, (x == 0) || (y == 0), "eq75"))) ||
        (get_rule_flag("eq76", rflag) && rewrite(select(x, 0, y) == 0, x || (y == 0), "eq76")) ||
        (get_rule_flag("eq77", rflag) && rewrite(select(x, c0, y) == 0, !x && (y == 0), c0 != 0, "eq77")) ||
        (get_rule_flag("eq78", rflag) && rewrite(select(x, y, 0) == 0, !x || (y == 0), "eq78")) ||
        (get_rule_flag("eq79", rflag) && rewrite(select(x, y, c0) == 0, x && (y == 0), c0 != 0, "eq79")) ||
        (get_rule_flag("eq80", rflag) && rewrite(max(x, y) - y == 0, x <= y, "eq80")) ||
        (get_rule_flag("eq81", rflag) && rewrite(min(x, y) - y == 0, y <= x, "eq81")) ||
        (get_rule_flag("eq82", rflag) && rewrite(max(y, x) - y == 0, x <= y, "eq82")) ||
        (get_rule_flag("eq83", rflag) && rewrite(min(y, x) - y == 0, y <= x, "eq83")) ||
        (get_rule_flag("eq84", rflag) && rewrite(y - max(x, y) == 0, x <= y, "eq84")) ||
        (get_rule_flag("eq85", rflag) && rewrite(y - min(x, y) == 0, y <= x, "eq85")) ||
        (get_rule_flag("eq86", rflag) && rewrite(y - max(y, x) == 0, x <= y, "eq86")) ||
        (get_rule_flag("eq87", rflag) && rewrite(y - min(y, x) == 0, y <= x, "eq87")) ||
        (get_rule_flag("eq88", rflag) && rewrite(max(x, c0) + c1 == 0, x == fold(-c1), c0 + c1 < 0, "eq88")) ||
        (get_rule_flag("eq89", rflag) && rewrite(min(x, c0) + c1 == 0, x == fold(-c1), c0 + c1 > 0, "eq89")) ||
        (get_rule_flag("eq90", rflag) && rewrite(max(x, c0) + c1 == 0, x <= c0, c0 + c1 == 0, "eq90")) ||
        (get_rule_flag("eq91", rflag) && rewrite(min(x, c0) + c1 == 0, c0 <= x, c0 + c1 == 0, "eq91")) ||
        (get_rule_flag("eq92", rflag) && rewrite(max(x, 0) == 0, x <= 0, "eq92")) ||
        (get_rule_flag("eq93", rflag) && rewrite(min(x, 0) == 0, 0 <= x, "eq93"))) {

        return mutate(std::move(rewrite.result), bounds);
    }

    if ((get_rule_flag("eq98", rflag) && rewrite(c0 == 0, fold(c0 == 0), "eq98")) ||
        (get_rule_flag("eq99", rflag) && rewrite((x - y) + c0 == 0, x == y + fold(-c0), "eq99")) ||
        (get_rule_flag("eq100", rflag) && rewrite(x + c0 == 0, x == fold(-c0), "eq100")) ||
        (get_rule_flag("eq101", rflag) && rewrite(c0 - x == 0, x == c0, "eq101"))) {
        return rewrite.result;
    }

    if (const Sub *s = delta.as<Sub>()) {
        if (s->a.same_as(a) && s->b.same_as(b)) {
            return op;
        } else {
            Expr a = s->a;
            Expr b = s->b;
            auto rewrite = IRMatcher::rewriter(IRMatcher::eq(a, b), op->type, delta.type());
            if (no_overflow_int(op->a.type()) &&
                use_synthesized_rules &&
                (
#include "Simplify_EQ.inc"
                 )) {
                return mutate(std::move(rewrite.result), bounds);
            } else {
                return EQ::make(a, b);
            }
        }
    }

    return delta == make_zero(a.type());
}

// ne redirects to not eq
Expr Simplify::visit(const NE *op, ExprInfo *bounds) {
    if (!may_simplify(op->a.type())) {
        Expr a = mutate(op->a, nullptr);
        Expr b = mutate(op->b, nullptr);
        if (a.same_as(op->a) && b.same_as(op->b)) {
            return op;
        } else {
            return NE::make(a, b);
        }
    }

    Expr mutated = mutate(Not::make(EQ::make(op->a, op->b)), bounds);
    if (const NE *ne = mutated.as<NE>()) {
        if (ne->a.same_as(op->a) && ne->b.same_as(op->b)) {
            return op;
        }
    }
    return mutated;
}

}
}
