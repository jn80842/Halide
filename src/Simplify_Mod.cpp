#include "Simplify_Internal.h"

namespace Halide {
namespace Internal {

Expr Simplify::visit(const Mod *op, ExprInfo *bounds) {
    ExprInfo a_bounds, b_bounds;
    Expr a = mutate(op->a, &a_bounds);
    Expr b = mutate(op->b, &b_bounds);

    // We always combine bounds here, even if not requested, because
    // we can use them to simplify down to a constant if the bounds
    // are tight enough.
    ExprInfo mod_bounds;

    if (no_overflow_int(op->type)) {
        // The result is at least zero.
        mod_bounds.min_defined = true;
        mod_bounds.min = 0;

        // Mod by produces a result between 0
        // and max(0, abs(modulus) - 1). However, if b is unbounded in
        // either direction, abs(modulus) could be arbitrarily
        // large.
        if (b_bounds.max_defined && b_bounds.min_defined) {
            mod_bounds.max_defined = true;
            mod_bounds.max = 0;                                            // When b == 0
            mod_bounds.max = std::max(mod_bounds.max, b_bounds.max - 1);   // When b > 0
            mod_bounds.max = std::max(mod_bounds.max, -1 - b_bounds.min);  // When b < 0
        }

        // If a is positive, mod can't make it larger
        if (a_bounds.min_defined && a_bounds.min >= 0 && a_bounds.max_defined) {
            if (mod_bounds.max_defined) {
                mod_bounds.max = std::min(mod_bounds.max, a_bounds.max);
            } else {
                mod_bounds.max_defined = true;
                mod_bounds.max = a_bounds.max;
            }
        }

        mod_bounds.alignment = a_bounds.alignment % b_bounds.alignment;
        mod_bounds.trim_bounds_using_alignment();
        if (bounds) {
            *bounds = mod_bounds;
        }
    }

    if (may_simplify(op->type)) {
        if (a_bounds.min_defined && a_bounds.min >= 0 &&
            a_bounds.max_defined && b_bounds.min_defined && a_bounds.max < b_bounds.min) {
            if (bounds) {
                *bounds = a_bounds;
            }
            return a;
        }

        if (mod_bounds.min_defined && mod_bounds.max_defined && mod_bounds.min == mod_bounds.max) {
            return make_const(op->type, mod_bounds.min);
        }

        int lanes = op->type.lanes();

        auto rewrite = IRMatcher::rewriter(IRMatcher::mod(a, b), op->type);

        if ((get_rule_flag("mod66", rflag) && rewrite(c0 % c1, fold(c0 % c1), "mod66")) ||
            (get_rule_flag("mod67", rflag) && rewrite(IRMatcher::Overflow() % x, IRMatcher::Overflow(), "mod67")) ||
            (get_rule_flag("mod68", rflag) && rewrite(x % IRMatcher::Overflow(), IRMatcher::Overflow(), "mod68")) ||
            (get_rule_flag("mod69", rflag) && rewrite(0 % x, 0, "mod69")) ||
            (get_rule_flag("mod70", rflag) && rewrite(x % x, 0, "mod70")) ||
            (get_rule_flag("mod71", rflag) && rewrite(x % 0, 0, "mod71")) ||
            (!op->type.is_float() &&
             (get_rule_flag("mod73", rflag) && rewrite(x % 1, 0, "mod73")))) {
            return rewrite.result;
        }

        // clang-format off
        if (EVAL_IN_LAMBDA
            ((get_rule_flag("mod79", rflag) && rewrite(broadcast(x) % broadcast(y), broadcast(x % y, lanes), "mod79")) ||
             (no_overflow_int(op->type) &&
              ((get_rule_flag("mod81", rflag) && rewrite((x * c0) % c1, (x * fold(c0 % c1)) % c1, c1 > 0 && (c0 >= c1 || c0 < 0), "mod81")) ||
               (get_rule_flag("mod82", rflag) && rewrite((x + c0) % c1, (x + fold(c0 % c1)) % c1, c1 > 0 && (c0 >= c1 || c0 < 0), "mod82")) ||
               (get_rule_flag("mod83", rflag) && rewrite((x * c0) % c1, (x % fold(c1/c0)) * c0, c0 > 0 && c1 % c0 == 0, "mod83")) ||
               (get_rule_flag("mod84", rflag) && rewrite((x * c0 + y) % c1, y % c1, c0 % c1 == 0, "mod84")) ||
               (get_rule_flag("mod85", rflag) && rewrite((y + x * c0) % c1, y % c1, c0 % c1 == 0, "mod85")) ||
               (get_rule_flag("mod86", rflag) && rewrite((x * c0 - y) % c1, (-y) % c1, c0 % c1 == 0, "mod86")) ||
               (get_rule_flag("mod87", rflag) && rewrite((y - x * c0) % c1, y % c1, c0 % c1 == 0, "mod87")) ||
               (get_rule_flag("mod88", rflag) && rewrite((x - y) % 2, (x + y) % 2, "mod88")) || // Addition and subtraction are the same modulo 2, because -1 == 1

               (get_rule_flag("mod90", rflag) && rewrite(ramp(x, c0) % broadcast(c1), broadcast(x, lanes) % c1, c0 % c1 == 0, "mod90")) ||
               (get_rule_flag("mod91", rflag) && rewrite(ramp(x, c0) % broadcast(c1), ramp(x % c1, c0, lanes),
                       // First and last lanes are the same when...
                       can_prove((x % c1 + c0 * (lanes - 1)) / c1 == 0, this), "mod91")) ||
               (get_rule_flag("mod94", rflag) && rewrite(ramp(x * c0, c2) % broadcast(c1), (ramp(x * fold(c0 % c1), fold(c2 % c1), lanes) % c1), c1 > 0 && (c0 >= c1 || c0 < 0), "mod94")) ||
               (get_rule_flag("mod95", rflag) && rewrite(ramp(x + c0, c2) % broadcast(c1), (ramp(x + fold(c0 % c1), fold(c2 % c1), lanes) % c1), c1 > 0 && (c0 >= c1 || c0 < 0), "mod95")) ||
               (get_rule_flag("mod96", rflag) && rewrite(ramp(x * c0 + y, c2) % broadcast(c1), ramp(y, fold(c2 % c1), lanes) % c1, c0 % c1 == 0, "mod96")) ||
               (get_rule_flag("mod97", rflag) && rewrite(ramp(y + x * c0, c2) % broadcast(c1), ramp(y, fold(c2 % c1), lanes) % c1, c0 % c1 == 0, "mod97")))))) {
            return mutate(std::move(rewrite.result), bounds);
        }
        // clang-format on
    }

    if (a.same_as(op->a) && b.same_as(op->b)) {
        return op;
    } else {
        return Mod::make(a, b);
    }
}

}  // namespace Internal
}  // namespace Halide