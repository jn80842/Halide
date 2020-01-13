#include "Simplify_Internal.h"

namespace Halide {
namespace Internal {

Expr Simplify::visit(const Add *op, ExprInfo *bounds) {
    ExprInfo a_bounds, b_bounds;
    Expr a = mutate(op->a, &a_bounds);
    Expr b = mutate(op->b, &b_bounds);

    if (bounds && no_overflow_int(op->type)) {
        bounds->min_defined = a_bounds.min_defined && b_bounds.min_defined;
        bounds->max_defined = a_bounds.max_defined && b_bounds.max_defined;
        bounds->min = a_bounds.min + b_bounds.min;
        bounds->max = a_bounds.max + b_bounds.max;
        bounds->alignment = a_bounds.alignment + b_bounds.alignment;
        bounds->trim_bounds_using_alignment();
    }

    if (may_simplify(op->type)) {

        // Order commutative operations by node type
        if (should_commute(a, b)) {
            std::swap(a, b);
            std::swap(a_bounds, b_bounds);
        }

        auto rewrite = IRMatcher::rewriter(IRMatcher::add(a, b), op->type);
        const int lanes = op->type.lanes();

        if (rewrite(c0 + c1, fold(c0 + c1), "add31") ||
            rewrite(IRMatcher::Indeterminate() + x, a) ||
            rewrite(x + IRMatcher::Indeterminate(), b) ||
            rewrite(IRMatcher::Overflow() + x, a) ||
            rewrite(x + IRMatcher::Overflow(), b) ||
            rewrite(x + 0, x, "add36") ||
            rewrite(0 + x, x, "add37")) {
            return rewrite.result;
        }

        if (EVAL_IN_LAMBDA
            ((get_rule_flag("add42", rflag) && (rewrite(x + x, x * 2, "add42"))) ||
             (get_rule_flag("add43", rflag) && rewrite(ramp(x, y) + ramp(z, w), ramp(x + z, y + w, lanes), "add43")) ||
             (get_rule_flag("add44", rflag) && rewrite(ramp(x, y) + broadcast(z), ramp(x + z, y, lanes), "add44")) ||
             (get_rule_flag("add45", rflag) && rewrite(broadcast(x) + broadcast(y), broadcast(x + y, lanes), "add45")) ||
             (get_rule_flag("add46", rflag) && rewrite(select(x, y, z) + select(x, w, u), select(x, y + w, z + u), "add46")) ||
             (get_rule_flag("add47", rflag) && rewrite(select(x, c0, c1) + c2, select(x, fold(c0 + c2), fold(c1 + c2)), "add47")) ||
             //             rewrite(select(x, y, c1) + c2, select(x, y + c2, fold(c1 + c2))) ||
             (get_rule_flag("add48", rflag) && rewrite(select(x, c0, y) + c2, select(x, fold(c0 + c2), y + c2), "add48")) ||

             (get_rule_flag("add51", rflag) && rewrite((select(x, y, z) + w) + select(x, u, v), select(x, y + u, z + v) + w, "add51")) ||
             (get_rule_flag("add52", rflag) && rewrite((w + select(x, y, z)) + select(x, u, v), select(x, y + u, z + v) + w, "add52")) ||
             (get_rule_flag("add53", rflag) && rewrite(select(x, y, z) + (select(x, u, v) + w), select(x, y + u, z + v) + w, "add53")) ||
             (get_rule_flag("add54", rflag) && rewrite(select(x, y, z) + (w + select(x, u, v)), select(x, y + u, z + v) + w, "add54")) ||
             (get_rule_flag("add55", rflag) && rewrite((select(x, y, z) - w) + select(x, u, v), select(x, y + u, z + v) - w, "add55")) ||
             (get_rule_flag("add56", rflag) && rewrite(select(x, y, z) + (select(x, u, v) - w), select(x, y + u, z + v) - w, "add56")) ||
             (get_rule_flag("add57", rflag) && rewrite((w - select(x, y, z)) + select(x, u, v), select(x, u - y, v - z) + w, "add57")) ||
             (get_rule_flag("add58", rflag) && rewrite(select(x, y, z) + (w - select(x, u, v)), select(x, y - u, z - v) + w, "add58")) ||

             (get_rule_flag("add60", rflag) && rewrite((x + c0) + c1, x + fold(c0 + c1), "add60")) ||
             (get_rule_flag("add61", rflag) && rewrite((x + c0) + y, (x + y) + c0, "add61")) ||
             (get_rule_flag("add62", rflag) && rewrite(x + (y + c0), (x + y) + c0, "add62")) ||
             (get_rule_flag("add63", rflag) && rewrite((c0 - x) + c1, fold(c0 + c1) - x, "add63")) ||
             (get_rule_flag("add64", rflag) && rewrite((c0 - x) + y, (y - x) + c0, "add64")) ||
             (get_rule_flag("add65", rflag) && rewrite((x - y) + y, x, "add65")) ||
             (get_rule_flag("add66", rflag) && rewrite(x + (y - x), y, "add66")) ||
             (get_rule_flag("add67", rflag) && rewrite(x + (c0 - y), (x - y) + c0, "add67")) ||
             (get_rule_flag("add68", rflag) && rewrite((x - y) + (y - z), x - z, "add68")) ||
             (get_rule_flag("add69", rflag) && rewrite((x - y) + (z - x), z - y, "add69")) ||
             (get_rule_flag("add70", rflag) && rewrite(x + y*c0, x - y*(-c0), c0 < 0 && -c0 > 0, "add70")) ||
             (get_rule_flag("add71", rflag) && rewrite(x*c0 + y, y - x*(-c0), c0 < 0 && -c0 > 0 && !is_const(y), "add71")) ||
             (get_rule_flag("add72", rflag) && rewrite(x*y + z*y, (x + z)*y, "add72")) ||
             (get_rule_flag("add73", rflag) && rewrite(x*y + y*z, (x + z)*y, "add73")) ||
             (get_rule_flag("add74", rflag) && rewrite(y*x + z*y, y*(x + z), "add74")) ||
             (get_rule_flag("add75", rflag) && rewrite(y*x + y*z, y*(x + z), "add75")) ||
             (get_rule_flag("add76", rflag) && rewrite(x*c0 + y*c1, (x + y*fold(c1/c0)) * c0, c1 % c0 == 0, "add76")) ||
             (get_rule_flag("add77", rflag) && rewrite(x*c0 + y*c1, (x*fold(c0/c1) + y) * c1, c0 % c1 == 0, "add77")) ||
             (no_overflow(op->type) &&
              ((get_rule_flag("add79", rflag) && rewrite(x + x*y, x * (y + 1), "add79")) ||
               (get_rule_flag("add80", rflag) && rewrite(x + y*x, (y + 1) * x, "add80")) ||
               (get_rule_flag("add81", rflag) && rewrite(x*y + x, x * (y + 1), "add81")) ||
               (get_rule_flag("add82", rflag) && rewrite(y*x + x, (y + 1) * x, !is_const(x), "add82")) ||
               (get_rule_flag("add83", rflag) && rewrite((x + c0)/c1 + c2, (x + fold(c0 + c1*c2))/c1, "add83")) ||
               (get_rule_flag("add84", rflag) && rewrite((x + (y + c0)/c1) + c2, x + (y + fold(c0 + c1*c2))/c1, "add84")) ||
               (get_rule_flag("add85", rflag) && rewrite(((y + c0)/c1 + x) + c2, x + (y + fold(c0 + c1*c2))/c1, "add85")) ||
               (get_rule_flag("add86", rflag) && rewrite((c0 - x)/c1 + c2, (fold(c0 + c1*c2) - x)/c1, c0 != 0 && c1 != 0, "add86")) || // When c0 is zero, this would fight another rule
               (get_rule_flag("add87", rflag) && rewrite(x + (x + y)/c0, (fold(c0 + 1)*x + y)/c0, "add87")) ||
               (get_rule_flag("add88", rflag) && rewrite(x + (y + x)/c0, (fold(c0 + 1)*x + y)/c0, "add88")) ||
               (get_rule_flag("add89", rflag) && rewrite(x + (y - x)/c0, (fold(c0 - 1)*x + y)/c0, "add89")) ||
               (get_rule_flag("add90", rflag) && rewrite(x + (x - y)/c0, (fold(c0 + 1)*x - y)/c0, "add90")) ||
               (get_rule_flag("add91", rflag) && rewrite((x - y)/c0 + x, (fold(c0 + 1)*x - y)/c0, "add91")) ||
               (get_rule_flag("add92", rflag) && rewrite((y - x)/c0 + x, (y + fold(c0 - 1)*x)/c0, "add92")) ||
               (get_rule_flag("add93", rflag) && rewrite((x + y)/c0 + x, (fold(c0 + 1)*x + y)/c0, "add93")) ||
               (get_rule_flag("add94", rflag) && rewrite((y + x)/c0 + x, (y + fold(c0 + 1)*x)/c0, "add94")) ||
               (get_rule_flag("add95", rflag) && rewrite(min(x, y - z) + z, min(x + z, y), "add95")) ||
               (get_rule_flag("add96", rflag) && rewrite(min(y - z, x) + z, min(y, x + z), "add96")) ||
               (get_rule_flag("add97", rflag) && rewrite(min(x, y + c0) + c1, min(x + c1, y), c0 + c1 == 0, "add97")) ||
               (get_rule_flag("add98", rflag) && rewrite(min(y + c0, x) + c1, min(y, x + c1), c0 + c1 == 0, "add98")) ||
               (get_rule_flag("add99", rflag) && rewrite(z + min(x, y - z), min(z + x, y), "add99")) ||
               (get_rule_flag("add100", rflag) && rewrite(z + min(y - z, x), min(y, z + x), "add100")) ||
               (get_rule_flag("add101", rflag) && rewrite(z + max(x, y - z), max(z + x, y), "add101")) ||
               (get_rule_flag("add102", rflag) && rewrite(z + max(y - z, x), max(y, z + x), "add102")) ||
               (get_rule_flag("add103", rflag) && rewrite(max(x, y - z) + z, max(x + z, y), "add103")) ||
               (get_rule_flag("add104", rflag) && rewrite(max(y - z, x) + z, max(y, x + z), "add104")) ||
               (get_rule_flag("add105", rflag) && rewrite(max(x, y + c0) + c1, max(x + c1, y), c0 + c1 == 0, "add105")) ||
               (get_rule_flag("add106", rflag) && rewrite(max(y + c0, x) + c1, max(y, x + c1), c0 + c1 == 0, "add106")) ||
               (get_rule_flag("add107", rflag) && rewrite(max(x, y) + min(x, y), x + y, "add107")) ||
               (get_rule_flag("add108", rflag) && rewrite(max(x, y) + min(y, x), x + y, "add108")))) ||
             (no_overflow_int(op->type) &&
              ((get_rule_flag("add110", rflag) && rewrite((x/y)*y + x%y, x, "add110")) ||
               (get_rule_flag("add111", rflag) && rewrite((z + x/y)*y + x%y, z*y + x, "add111")) ||
               (get_rule_flag("add112", rflag) && rewrite((x/y + z)*y + x%y, x + z*y, "add112")) ||
               (get_rule_flag("add113", rflag) && rewrite(x%y + ((x/y)*y + z), x + z, "add113")) ||
               (get_rule_flag("add114", rflag) && rewrite(x%y + ((x/y)*y - z), x - z, "add114")) ||
               (get_rule_flag("add115", rflag) && rewrite(x%y + (z + (x/y)*y), x + z, "add115")) ||
               (get_rule_flag("add116", rflag) && rewrite((x/y)*y + (x%y + z), x + z, "add116")) ||
               (get_rule_flag("add117", rflag) && rewrite((x/y)*y + (x%y - z), x - z, "add117")) ||
               (get_rule_flag("add118", rflag) && rewrite((x/y)*y + (z + x%y), x + z, "add118")) ||
               (get_rule_flag("add119", rflag) && rewrite(x/2 + x%2, (x + 1) / 2, "add119")) ||

               (get_rule_flag("add121", rflag) && rewrite(x + ((c0 - x)/c1)*c1, c0 - ((c0 - x) % c1), c1 > 0, "add121")) ||
               (get_rule_flag("add122", rflag) && rewrite(x + ((c0 - x)/c1 + y)*c1, y * c1 - ((c0 - x) % c1) + c0, c1 > 0, "add122")) ||
               (get_rule_flag("add123", rflag) && rewrite(x + (y + (c0 - x)/c1)*c1, y * c1 - ((c0 - x) % c1) + c0, c1 > 0, "add123")) ||
               false)))) {
            return mutate(std::move(rewrite.result), bounds);
        }

        if (no_overflow_int(op->type) &&
            use_synthesized_rules &&
            (
#include "Simplify_Add.inc"
             )) {
            return mutate(std::move(rewrite.result), bounds);
        }

        const Shuffle *shuffle_a = a.as<Shuffle>();
        const Shuffle *shuffle_b = b.as<Shuffle>();
        if (shuffle_a && shuffle_b &&
            shuffle_a->is_slice() &&
            shuffle_b->is_slice()) {
            if (a.same_as(op->a) && b.same_as(op->b)) {
                return hoist_slice_vector<Add>(op);
            } else {
                return hoist_slice_vector<Add>(Add::make(a, b));
            }
        }
    }

    if (a.same_as(op->a) && b.same_as(op->b)) {
        return op;
    } else {
        return Add::make(a, b);
    }
}

}
}
