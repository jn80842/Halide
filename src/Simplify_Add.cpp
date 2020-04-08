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
        if (add_would_overflow(64, a_bounds.min, b_bounds.min)) {
            bounds->min_defined = false;
            bounds->min = 0;
        } else {
            bounds->min = a_bounds.min + b_bounds.min;
        }
        if (add_would_overflow(64, a_bounds.max, b_bounds.max)) {
            bounds->max_defined = false;
            bounds->max = 0;
        } else {
            bounds->max = a_bounds.max + b_bounds.max;
        }

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

        if ((get_rule_flag("add42", rflag) && rewrite(c0 + c1, fold(c0 + c1), "add42")) ||
            (get_rule_flag("add43", rflag) && rewrite(IRMatcher::Overflow() + x, a, "add43")) ||
            (get_rule_flag("add44", rflag) && rewrite(x + IRMatcher::Overflow(), b, "add44")) ||
            (get_rule_flag("add45", rflag) && rewrite(x + 0, x, "add45")) ||
            (get_rule_flag("add46", rflag) && rewrite(0 + x, x, "add46"))) {
            return rewrite.result;
        }

        // clang-format off
        if (EVAL_IN_LAMBDA
            ((get_rule_flag("add52", rflag) && rewrite(x + x, x * 2, "add52")) ||
             (get_rule_flag("add53", rflag) && rewrite(ramp(x, y) + ramp(z, w), ramp(x + z, y + w, lanes), "add53")) ||
             (get_rule_flag("add54", rflag) && rewrite(ramp(x, y) + broadcast(z), ramp(x + z, y, lanes), "add54")) ||
             (get_rule_flag("add55", rflag) && rewrite(broadcast(x) + broadcast(y), broadcast(x + y, lanes), "add55")) ||
             (get_rule_flag("add56", rflag) && rewrite(select(x, y, z) + select(x, w, u), select(x, y + w, z + u), "add56")) ||
             (get_rule_flag("add57", rflag) && rewrite(select(x, c0, c1) + c2, select(x, fold(c0 + c2), fold(c1 + c2)), "add57")) ||
             (get_rule_flag("add58", rflag) && rewrite(select(x, y, c1) + c2, select(x, y + c2, fold(c1 + c2)), "add58")) ||
             (get_rule_flag("add59", rflag) && rewrite(select(x, c0, y) + c2, select(x, fold(c0 + c2), y + c2), "add59")) ||

             (get_rule_flag("add61", rflag) && rewrite((select(x, y, z) + w) + select(x, u, v), select(x, y + u, z + v) + w, "add61")) ||
             (get_rule_flag("add62", rflag) && rewrite((w + select(x, y, z)) + select(x, u, v), select(x, y + u, z + v) + w, "add62")) ||
             (get_rule_flag("add63", rflag) && rewrite(select(x, y, z) + (select(x, u, v) + w), select(x, y + u, z + v) + w, "add63")) ||
             (get_rule_flag("add64", rflag) && rewrite(select(x, y, z) + (w + select(x, u, v)), select(x, y + u, z + v) + w, "add64")) ||
             (get_rule_flag("add65", rflag) && rewrite((select(x, y, z) - w) + select(x, u, v), select(x, y + u, z + v) - w, "add65")) ||
             (get_rule_flag("add66", rflag) && rewrite(select(x, y, z) + (select(x, u, v) - w), select(x, y + u, z + v) - w, "add66")) ||
             (get_rule_flag("add67", rflag) && rewrite((w - select(x, y, z)) + select(x, u, v), select(x, u - y, v - z) + w, "add67")) ||
             (get_rule_flag("add68", rflag) && rewrite(select(x, y, z) + (w - select(x, u, v)), select(x, y - u, z - v) + w, "add68")) ||

             (get_rule_flag("add70", rflag) && rewrite((x + c0) + c1, x + fold(c0 + c1), "add70")) ||
             (get_rule_flag("add71", rflag) && rewrite((x + c0) + y, (x + y) + c0, "add71")) ||
             (get_rule_flag("add72", rflag) && rewrite(x + (y + c0), (x + y) + c0, "add72")) ||
             (get_rule_flag("add73", rflag) && rewrite((c0 - x) + c1, fold(c0 + c1) - x, "add73")) ||
             (get_rule_flag("add74", rflag) && rewrite((c0 - x) + y, (y - x) + c0, "add74")) ||

             (get_rule_flag("add76", rflag) && rewrite((x - y) + y, x, "add76")) ||
             (get_rule_flag("add76", rflag) && rewrite(x + (y - x), y, "add77")) ||

             (get_rule_flag("add79", rflag) && rewrite(((x - y) + z) + y, x + z, "add79")) ||
             (get_rule_flag("add80", rflag) && rewrite((z + (x - y)) + y, z + x, "add80")) ||
             (get_rule_flag("add81", rflag) && rewrite(x + ((y - x) + z), y + z, "add81")) ||
             (get_rule_flag("add82", rflag) && rewrite(x + (z + (y - x)), z + y, "add82")) ||

             (get_rule_flag("add84", rflag) && rewrite(x + (c0 - y), (x - y) + c0, "add84")) ||
             (get_rule_flag("add85", rflag) && rewrite((x - y) + (y - z), x - z, "add85")) ||
             (get_rule_flag("add86", rflag) && rewrite((x - y) + (z - x), z - y, "add86")) ||
             (get_rule_flag("add87", rflag) && rewrite(x + y*c0, x - y*(-c0), c0 < 0 && -c0 > 0, "add87")) ||

             (get_rule_flag("add89", rflag) && rewrite(x + (y*c0 - z), x - y*(-c0) - z, c0 < 0 && -c0 > 0, "add89")) ||
             (get_rule_flag("add90", rflag) && rewrite((y*c0 - z) + x, x - y*(-c0) - z, c0 < 0 && -c0 > 0, "add90")) ||

             (get_rule_flag("add92", rflag) && rewrite(x*c0 + y, y - x*(-c0), c0 < 0 && -c0 > 0 && !is_const(y), "add92")) ||
             (get_rule_flag("add93", rflag) && rewrite(x*y + z*y, (x + z)*y, "add93")) ||
             (get_rule_flag("add94", rflag) && rewrite(x*y + y*z, (x + z)*y, "add94")) ||
             (get_rule_flag("add95", rflag) && rewrite(y*x + z*y, y*(x + z), "add95")) ||
             (get_rule_flag("add96", rflag) && rewrite(y*x + y*z, y*(x + z), "add96")) ||
             (get_rule_flag("add97", rflag) && rewrite(x*c0 + y*c1, (x + y*fold(c1/c0)) * c0, c1 % c0 == 0, "add97")) ||
             (get_rule_flag("add98", rflag) && rewrite(x*c0 + y*c1, (x*fold(c0/c1) + y) * c1, c0 % c1 == 0, "add98")) ||
             (no_overflow(op->type) &&
              ((get_rule_flag("add100", rflag) && rewrite(x + x*y, x * (y + 1), "add100")) ||
               (get_rule_flag("add101", rflag) && rewrite(x + y*x, (y + 1) * x, "add101")) ||
               (get_rule_flag("add102", rflag) && rewrite(x*y + x, x * (y + 1), "add102")) ||
               (get_rule_flag("add103", rflag) && rewrite(y*x + x, (y + 1) * x, !is_const(x), "add103")) ||
               (get_rule_flag("add104", rflag) && rewrite((x + c0)/c1 + c2, (x + fold(c0 + c1*c2))/c1, c1 != 0, "add104")) ||
               (get_rule_flag("add105", rflag) && rewrite((x + (y + c0)/c1) + c2, x + (y + fold(c0 + c1*c2))/c1, c1 != 0, "add105")) ||
               (get_rule_flag("add106", rflag) && rewrite(((y + c0)/c1 + x) + c2, x + (y + fold(c0 + c1*c2))/c1, c1 != 0, "add106")) ||
               (get_rule_flag("add107", rflag) && rewrite((c0 - x)/c1 + c2, (fold(c0 + c1*c2) - x)/c1, c0 != 0 && c1 != 0, "add107")) || // When c0 is zero, this would fight another rule
               (get_rule_flag("add108", rflag) && rewrite(x + (x + y)/c0, (fold(c0 + 1)*x + y)/c0, c0 != 0, "add108")) ||
               (get_rule_flag("add109", rflag) && rewrite(x + (y + x)/c0, (fold(c0 + 1)*x + y)/c0, c0 != 0, "add109")) ||
               (get_rule_flag("add110", rflag) && rewrite(x + (y - x)/c0, (fold(c0 - 1)*x + y)/c0, c0 != 0, "add110")) ||
               (get_rule_flag("add111", rflag) && rewrite(x + (x - y)/c0, (fold(c0 + 1)*x - y)/c0, c0 != 0, "add111")) ||
               (get_rule_flag("add112", rflag) && rewrite((x - y)/c0 + x, (fold(c0 + 1)*x - y)/c0, c0 != 0, "add112")) ||
               (get_rule_flag("add113", rflag) && rewrite((y - x)/c0 + x, (y + fold(c0 - 1)*x)/c0, c0 != 0, "add113")) ||
               (get_rule_flag("add114", rflag) && rewrite((x + y)/c0 + x, (fold(c0 + 1)*x + y)/c0, c0 != 0, "add114")) ||
               (get_rule_flag("add115", rflag) && rewrite((y + x)/c0 + x, (y + fold(c0 + 1)*x)/c0, c0 != 0, "add115")) ||
               (get_rule_flag("add116", rflag) && rewrite(min(x, y - z) + z, min(x + z, y), "add116")) ||
               (get_rule_flag("add117", rflag) && rewrite(min(y - z, x) + z, min(y, x + z), "add117")) ||
               (get_rule_flag("add118", rflag) && rewrite(min(x, y + c0) + c1, min(x + c1, y), c0 + c1 == 0, "add118")) ||
               (get_rule_flag("add119", rflag) && rewrite(min(y + c0, x) + c1, min(y, x + c1), c0 + c1 == 0, "add119")) ||
               (get_rule_flag("add120", rflag) && rewrite(z + min(x, y - z), min(z + x, y), "add120")) ||
               (get_rule_flag("add121", rflag) && rewrite(z + min(y - z, x), min(y, z + x), "add121")) ||
               (get_rule_flag("add122", rflag) && rewrite(z + max(x, y - z), max(z + x, y), "add122")) ||
               (get_rule_flag("add123", rflag) && rewrite(z + max(y - z, x), max(y, z + x), "add123")) ||
               (get_rule_flag("add124", rflag) && rewrite(max(x, y - z) + z, max(x + z, y), "add124")) ||
               (get_rule_flag("add125", rflag) && rewrite(max(y - z, x) + z, max(y, x + z), "add125")) ||
               (get_rule_flag("add126", rflag) && rewrite(max(x, y + c0) + c1, max(x + c1, y), c0 + c1 == 0, "add126")) ||
               (get_rule_flag("add127", rflag) && rewrite(max(y + c0, x) + c1, max(y, x + c1), c0 + c1 == 0, "add127")) ||
               (get_rule_flag("add128", rflag) && rewrite(max(x, y) + min(x, y), x + y, "add128")) ||
               (get_rule_flag("add129", rflag) && rewrite(max(x, y) + min(y, x), x + y, "add129")))) ||
             (no_overflow_int(op->type) &&
              ((get_rule_flag("add131", rflag) && rewrite((x/c0)*c0 + x%c0, x, c0 != 0, "add131")) ||
               (get_rule_flag("add132", rflag) && rewrite((z + x/c0)*c0 + x%c0, z*c0 + x, c0 != 0, "add132")) ||
               (get_rule_flag("add133", rflag) && rewrite((x/c0 + z)*c0 + x%c0, x + z*c0, c0 != 0, "add133")) ||
               (get_rule_flag("add134", rflag) && rewrite(x%c0 + ((x/c0)*c0 + z), x + z, c0 != 0, "add134")) ||
               (get_rule_flag("add135", rflag) && rewrite(x%c0 + ((x/c0)*c0 - z), x - z, c0 != 0, "add135")) ||
               (get_rule_flag("add136", rflag) && rewrite(x%c0 + (z + (x/c0)*c0), x + z, c0 != 0, "add136")) ||
               (get_rule_flag("add137", rflag) && rewrite((x/c0)*c0 + (x%c0 + z), x + z, c0 != 0, "add137")) ||
               (get_rule_flag("add138", rflag) && rewrite((x/c0)*c0 + (x%c0 - z), x - z, c0 != 0, "add138")) ||
               (get_rule_flag("add139", rflag) && rewrite((x/c0)*c0 + (z + x%c0), x + z, c0 != 0, "add139")) ||
               (get_rule_flag("add140", rflag) && rewrite(x/2 + x%2, (x + 1) / 2, "add140")) ||

               (get_rule_flag("add142", rflag) && rewrite(x + ((c0 - x)/c1)*c1, c0 - ((c0 - x) % c1), c1 > 0, "add142")) ||
               (get_rule_flag("add143", rflag) && rewrite(x + ((c0 - x)/c1 + y)*c1, y * c1 - ((c0 - x) % c1) + c0, c1 > 0, "add143")) ||
               (get_rule_flag("add144", rflag) && rewrite(x + (y + (c0 - x)/c1)*c1, y * c1 - ((c0 - x) % c1) + c0, c1 > 0, "add144")))))) {
            return mutate(std::move(rewrite.result), bounds);
        }
        // clang-format on

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

}  // namespace Internal
}  // namespace Halide