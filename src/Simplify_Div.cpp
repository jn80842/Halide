#include "Simplify_Internal.h"

namespace Halide {
namespace Internal {

Expr Simplify::visit(const Div *op, ExprInfo *bounds) {
    ExprInfo a_bounds, b_bounds;
    Expr a = mutate(op->a, &a_bounds);
    Expr b = mutate(op->b, &b_bounds);

    if (bounds && no_overflow_int(op->type)) {
        bounds->min = INT64_MAX;
        bounds->max = INT64_MIN;

        // Enumerate all possible values for the min and max and take the extreme values.
        if (a_bounds.min_defined && b_bounds.min_defined && b_bounds.min != 0) {
            int64_t v = div_imp(a_bounds.min, b_bounds.min);
            bounds->min = std::min(bounds->min, v);
            bounds->max = std::max(bounds->max, v);
        }

        if (a_bounds.min_defined && b_bounds.max_defined && b_bounds.max != 0) {
            int64_t v = div_imp(a_bounds.min, b_bounds.max);
            bounds->min = std::min(bounds->min, v);
            bounds->max = std::max(bounds->max, v);
        }

        if (a_bounds.max_defined && b_bounds.max_defined && b_bounds.max != 0) {
            int64_t v = div_imp(a_bounds.max, b_bounds.max);
            bounds->min = std::min(bounds->min, v);
            bounds->max = std::max(bounds->max, v);
        }

        if (a_bounds.max_defined && b_bounds.min_defined && b_bounds.min != 0) {
            int64_t v = div_imp(a_bounds.max, b_bounds.min);
            bounds->min = std::min(bounds->min, v);
            bounds->max = std::max(bounds->max, v);
        }

        const bool b_positive = b_bounds.min_defined && b_bounds.min > 0;
        const bool b_negative = b_bounds.max_defined && b_bounds.max < 0;

        if ((b_positive && !b_bounds.max_defined) ||
            (b_negative && !b_bounds.min_defined)) {
            // Take limit as b -> +/- infinity
            int64_t v = 0;
            bounds->min = std::min(bounds->min, v);
            bounds->max = std::max(bounds->max, v);
        }

        bounds->min_defined = ((a_bounds.min_defined && b_positive) ||
                               (a_bounds.max_defined && b_negative));
        bounds->max_defined = ((a_bounds.max_defined && b_positive) ||
                               (a_bounds.min_defined && b_negative));

        // Bounded numerator divided by constantish
        // denominator can sometimes collapse things to a
        // constant at this point
        if (bounds->min_defined &&
            bounds->max_defined &&
            bounds->max == bounds->min) {
            if (op->type.can_represent(bounds->min)) {
                return make_const(op->type, bounds->min);
            } else {
                // Even though this is 'no-overflow-int', if the result
                // we calculate can't fit into the destination type,
                // we're better off returning an overflow condition than
                // a known-wrong value. (Note that no_overflow_int() should
                // only be true for signed integers.)
                internal_assert(op->type.is_int());
                return make_signed_integer_overflow(op->type);
            }
        }
        // Code downstream can use min/max in calculated-but-unused arithmetic
        // that can lead to UB (and thus, flaky failures under ASAN/UBSAN)
        // if we leave them set to INT64_MAX/INT64_MIN; normalize to zero to avoid this.
        if (!bounds->min_defined) bounds->min = 0;
        if (!bounds->max_defined) bounds->max = 0;
        bounds->alignment = a_bounds.alignment / b_bounds.alignment;
        bounds->trim_bounds_using_alignment();
    }

    if (may_simplify(op->type)) {

        int lanes = op->type.lanes();

        auto rewrite = IRMatcher::rewriter(IRMatcher::div(a, b), op->type);

        if (rewrite(IRMatcher::Indeterminate() / x, a) ||
            rewrite(x / IRMatcher::Indeterminate(), b) ||
            rewrite(IRMatcher::Overflow() / x, a) ||
            rewrite(x / IRMatcher::Overflow(), b) ||
            (get_rule_flag("div93", rflag) && rewrite(x / 1, x, "div93")) ||
            (!op->type.is_float() &&
             (get_rule_flag("div95", rflag) && rewrite(x / 0, IRMatcher::Indeterminate(), "div95"))) ||
            (get_rule_flag("div96", rflag) && rewrite(0 / x, 0, "div96")) ||
            (get_rule_flag("div97", rflag) && rewrite(x / x, 1, "div97")) ||
            (get_rule_flag("div98", rflag) && rewrite(c0 / c1, fold(c0 / c1), "div98"))) {
            return rewrite.result;
        }

        if (EVAL_IN_LAMBDA
            ((get_rule_flag("div103", rflag) && rewrite(broadcast(x) / broadcast(y), broadcast(x / y, lanes), "div103")) ||
             (get_rule_flag("div103", rflag) && rewrite(select(x, c0, c1) / c2, select(x, fold(c0/c2), fold(c1/c2)), "div104")) ||
             (no_overflow(op->type) &&
              (// Fold repeated division
               (get_rule_flag("div107", rflag) && rewrite((x / c0) / c2, x / fold(c0 * c2),                          c0 > 0 && c2 > 0 && !overflows(c0 * c2), "div107")) ||
               (get_rule_flag("div108", rflag) && rewrite((x / c0 + c1) / c2, (x + fold(c1 * c0)) / fold(c0 * c2),   c0 > 0 && c2 > 0 && !overflows(c0 * c2) && !overflows(c0 * c1), "div108")) ||
               (get_rule_flag("div109", rflag) && rewrite((x * c0) / c1, x / fold(c1 / c0),                          c1 % c0 == 0 && c0 > 0 && c1 / c0 != 0, "div109")) ||
               // Pull out terms that are a multiple of the denominator
               (get_rule_flag("div111", rflag) && rewrite((x * c0) / c1, x * fold(c0 / c1),                          c0 % c1 == 0 && c1 > 0, "div111")) ||

               (get_rule_flag("div113", rflag) && rewrite((x * c0 + y) / c1, y / c1 + x * fold(c0 / c1),             c0 % c1 == 0 && c1 > 0, "div113")) ||
               (get_rule_flag("div114", rflag) && rewrite((x * c0 - y) / c1, (-y) / c1 + x * fold(c0 / c1),          c0 % c1 == 0 && c1 > 0, "div114")) ||
               (get_rule_flag("div115", rflag) && rewrite((y + x * c0) / c1, y / c1 + x * fold(c0 / c1),             c0 % c1 == 0 && c1 > 0, "div115")) ||
               (get_rule_flag("div116", rflag) && rewrite((y - x * c0) / c1, y / c1 - x * fold(c0 / c1),             c0 % c1 == 0 && c1 > 0, "div116")) ||

               (get_rule_flag("div118", rflag) && rewrite(((x * c0 + y) + z) / c1, (y + z) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div118")) ||
               (get_rule_flag("div119", rflag) && rewrite(((x * c0 - y) + z) / c1, (z - y) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div119")) ||
               (get_rule_flag("div120", rflag) && rewrite(((x * c0 + y) - z) / c1, (y - z) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div120")) ||
               (get_rule_flag("div121", rflag) && rewrite(((x * c0 - y) - z) / c1, (-y - z) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div121")) ||
               (get_rule_flag("div122", rflag) && rewrite(((y + x * c0) + z) / c1, (y + z) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div122")) ||
               (get_rule_flag("div123", rflag) && rewrite(((y + x * c0) - z) / c1, (y - z) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div123")) ||
               (get_rule_flag("div124", rflag) && rewrite(((y - x * c0) - z) / c1, (y - z) / c1 - x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div124")) ||
               (get_rule_flag("div125", rflag) && rewrite(((y - x * c0) + z) / c1, (y + z) / c1 - x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div125")) ||

               (get_rule_flag("div127", rflag) && rewrite((z + (x * c0 + y)) / c1, (z + y) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div127")) ||
               (get_rule_flag("div128", rflag) && rewrite((z + (x * c0 - y)) / c1, (z - y) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div128")) ||
               (get_rule_flag("div129", rflag) && rewrite((z - (x * c0 - y)) / c1, (z + y) / c1 - x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div129")) ||
               (get_rule_flag("div130", rflag) && rewrite((z - (x * c0 + y)) / c1, (z - y) / c1 - x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div130")) ||

               (get_rule_flag("div132", rflag) && rewrite((z + (y + x * c0)) / c1, (z + y) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div132")) ||
               (get_rule_flag("div133", rflag) && rewrite((z - (y + x * c0)) / c1, (z - y) / c1 - x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div133")) ||
               (get_rule_flag("div134", rflag) && rewrite((z + (y - x * c0)) / c1, (z + y) / c1 - x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div134")) ||
               (get_rule_flag("div135", rflag) && rewrite((z - (y - x * c0)) / c1, (z - y) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div135")) ||

               // For the next depth, stick to addition
               (get_rule_flag("div138", rflag) && rewrite((((x * c0 + y) + z) + w) / c1, (y + z + w) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div138")) ||
               (get_rule_flag("div139", rflag) && rewrite((((y + x * c0) + z) + w) / c1, (y + z + w) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div139")) ||
               (get_rule_flag("div140", rflag) && rewrite(((z + (x * c0 + y)) + w) / c1, (y + z + w) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div140")) ||
               (get_rule_flag("div141", rflag) && rewrite(((z + (y + x * c0)) + w) / c1, (y + z + w) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div141")) ||
               (get_rule_flag("div142", rflag) && rewrite((w + ((x * c0 + y) + z)) / c1, (y + z + w) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div142")) ||
               (get_rule_flag("div143", rflag) && rewrite((w + ((y + x * c0) + z)) / c1, (y + z + w) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div143")) ||
               (get_rule_flag("div144", rflag) && rewrite((w + (z + (x * c0 + y))) / c1, (y + z + w) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div144")) ||
               (get_rule_flag("div145", rflag) && rewrite((w + (z + (y + x * c0))) / c1, (y + z + w) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0, "div145")) ||

               (get_rule_flag("div147", rflag) && rewrite((x + c0) / c1, x / c1 + fold(c0 / c1),                     c0 % c1 == 0, "div147")) ||
               (get_rule_flag("div148", rflag) && rewrite((x + y)/x, y/x + 1, "div148")) ||
               (get_rule_flag("div149", rflag) && rewrite((y + x)/x, y/x + 1, "div149")) ||
               // rewrite((x - y)/x, (-y)/x + 1) || reduction order failure detected
               (get_rule_flag("div151", rflag) && rewrite((y - x)/x, y/x - 1, "div150")) ||
               (get_rule_flag("div152", rflag) && rewrite(((x + y) + z)/x, (y + z)/x + 1, "div152")) ||
               (get_rule_flag("div153", rflag) && rewrite(((y + x) + z)/x, (y + z)/x + 1, "div153")) ||
               (get_rule_flag("div154", rflag) && rewrite((z + (x + y))/x, (z + y)/x + 1, "div154")) ||
               (get_rule_flag("div155", rflag) && rewrite((z + (y + x))/x, (z + y)/x + 1, "div155")) ||
               (get_rule_flag("div156", rflag) && rewrite((x*y)/x, y, "div156")) ||
               (get_rule_flag("div157", rflag) && rewrite((y*x)/x, y, "div157")) ||
               (get_rule_flag("div158", rflag) && rewrite((x*y + z)/x, y + z/x, "div158")) ||
               (get_rule_flag("div159", rflag) && rewrite((y*x + z)/x, y + z/x, "div159")) ||
               (get_rule_flag("div160", rflag) && rewrite((z + x*y)/x, z/x + y, "div160")) ||
               (get_rule_flag("div161", rflag) && rewrite((z + y*x)/x, z/x + y, "div161")) ||
               (get_rule_flag("div162", rflag) && rewrite((x*y - z)/x, y + (-z)/x, "div162")) ||
               (get_rule_flag("div163", rflag) && rewrite((y*x - z)/x, y + (-z)/x, "div163")) ||
               (get_rule_flag("div164", rflag) && rewrite((z - x*y)/x, z/x - y, "div164")) ||
               (get_rule_flag("div165", rflag) && rewrite((z - y*x)/x, z/x - y, "div165")) ||
               (op->type.is_float() && rewrite(x/c0, x * fold(1/c0))))) ||
             (no_overflow_int(op->type) &&
              ((get_rule_flag("div168", rflag) && rewrite(ramp(x, c0) / broadcast(c1), ramp(x / c1, fold(c0 / c1), lanes), c0 % c1 == 0, "div168")) ||
               (get_rule_flag("div171", rflag) && rewrite(ramp(x, c0) / broadcast(c1), broadcast(x / c1, lanes),
                                      // First and last lanes are the same when...
                                      can_prove((x % c1 + c0 * (lanes - 1)) / c1 == 0, this), "div171")))) ||
             (no_overflow_scalar_int(op->type) &&
              ((get_rule_flag("div173", rflag) && rewrite(x / -1, -x, "div173")) ||
               (get_rule_flag("div174", rflag) && rewrite(c0 / y, select(y < 0, fold(-c0), c0), c0 == -1, "div174")) ||
               (get_rule_flag("div177", rflag) && rewrite((x * c0 + c1) / c2,
                                       (x + fold(c1 / c0)) / fold(c2 / c0),
                                       c2 > 0 && c0 > 0 && c2 % c0 == 0, "div177")) ||
               (get_rule_flag("div180", rflag) && rewrite((x * c0 + c1) / c2,
                                      x * fold(c0 / c2) + fold(c1 / c2),
                       c2 > 0 && c0 % c2 == 0, "div180")) ||
               // A very specific pattern that comes up in bounds in upsampling code.
               (get_rule_flag("div182", rflag) && rewrite((x % 2 + c0) / 2, x % 2 + fold(c0 / 2), c0 % 2 == 1, "div182")))))) {
            return mutate(std::move(rewrite.result), bounds);
        }

        if (no_overflow_int(op->type) &&
            use_synthesized_rules &&
            (
#include "Simplify_Div.inc"
             )) {
            return mutate(std::move(rewrite.result), bounds);
        }
    }

    if (a.same_as(op->a) && b.same_as(op->b)) {
        return op;
    } else {
        return Div::make(a, b);
    }
}

}
}
