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
            (rewrite(x + x, x * 2, "add42") ||
             rewrite(ramp(x, y) + ramp(z, w), ramp(x + z, y + w, lanes), "add43") ||
             rewrite(ramp(x, y) + broadcast(z), ramp(x + z, y, lanes), "add44") ||
             rewrite(broadcast(x) + broadcast(y), broadcast(x + y, lanes), "add45") ||
             rewrite(select(x, y, z) + select(x, w, u), select(x, y + w, z + u), "add46") ||
             (!exclude_misordered_rules && rewrite(select(x, c0, c1) + c2, select(x, fold(c0 + c2), fold(c1 + c2)), "add47")) ||
             //             rewrite(select(x, y, c1) + c2, select(x, y + c2, fold(c1 + c2))) ||
             rewrite(select(x, c0, y) + c2, select(x, fold(c0 + c2), y + c2), "add48") ||

             rewrite((select(x, y, z) + w) + select(x, u, v), select(x, y + u, z + v) + w, "add51") ||
             rewrite((w + select(x, y, z)) + select(x, u, v), select(x, y + u, z + v) + w, "add52") ||
             rewrite(select(x, y, z) + (select(x, u, v) + w), select(x, y + u, z + v) + w, "add53") ||
             rewrite(select(x, y, z) + (w + select(x, u, v)), select(x, y + u, z + v) + w, "add54") ||
             rewrite((select(x, y, z) - w) + select(x, u, v), select(x, y + u, z + v) - w, "add55") ||
             rewrite(select(x, y, z) + (select(x, u, v) - w), select(x, y + u, z + v) - w, "add56") ||
             rewrite((w - select(x, y, z)) + select(x, u, v), select(x, u - y, v - z) + w, "add57") ||
             rewrite(select(x, y, z) + (w - select(x, u, v)), select(x, y - u, z - v) + w, "add58") ||

             rewrite((x + c0) + c1, x + fold(c0 + c1), "add60") ||
             rewrite((x + c0) + y, (x + y) + c0, "add61") ||
             rewrite(x + (y + c0), (x + y) + c0, "add62") ||
             rewrite((c0 - x) + c1, fold(c0 + c1) - x, "add63") ||
             rewrite((c0 - x) + y, (y - x) + c0, "add64") ||
             rewrite((x - y) + y, x, "add65") ||
             rewrite(x + (y - x), y, "add66") ||
             rewrite(x + (c0 - y), (x - y) + c0, "add67") ||
             rewrite((x - y) + (y - z), x - z, "add68") ||
             rewrite((x - y) + (z - x), z - y, "add69") ||
             (!exclude_misordered_rules && rewrite(x + y*c0, x - y*(-c0), c0 < 0 && -c0 > 0, "add70")) ||
             (!exclude_misordered_rules && rewrite(x*c0 + y, y - x*(-c0), c0 < 0 && -c0 > 0 && !is_const(y), "add71")) ||
             rewrite(x*y + z*y, (x + z)*y, "add72") ||
             rewrite(x*y + y*z, (x + z)*y, "add73") ||
             rewrite(y*x + z*y, y*(x + z), "add74") ||
             rewrite(y*x + y*z, y*(x + z), "add75") ||
             (!exclude_misordered_rules && rewrite(x*c0 + y*c1, (x + y*fold(c1/c0)) * c0, c1 % c0 == 0, "add76")) ||
             (!exclude_misordered_rules && rewrite(x*c0 + y*c1, (x*fold(c0/c1) + y) * c1, c0 % c1 == 0, "add77")) ||
             (no_overflow(op->type) &&
              (rewrite(x + x*y, x * (y + 1), "add79") ||
               rewrite(x + y*x, (y + 1) * x, "add80") ||
               rewrite(x*y + x, x * (y + 1), "add81") ||
               rewrite(y*x + x, (y + 1) * x, !is_const(x), "add82") ||
               rewrite((x + c0)/c1 + c2, (x + fold(c0 + c1*c2))/c1, "add83") ||
               rewrite((x + (y + c0)/c1) + c2, x + (y + fold(c0 + c1*c2))/c1, "add84") ||
               rewrite(((y + c0)/c1 + x) + c2, x + (y + fold(c0 + c1*c2))/c1, "add85") ||
               rewrite((c0 - x)/c1 + c2, (fold(c0 + c1*c2) - x)/c1, c0 != 0 && c1 != 0, "add86") || // When c0 is zero, this would fight another rule
               rewrite(x + (x + y)/c0, (fold(c0 + 1)*x + y)/c0, "add87") ||
               rewrite(x + (y + x)/c0, (fold(c0 + 1)*x + y)/c0, "add88") ||
               rewrite(x + (y - x)/c0, (fold(c0 - 1)*x + y)/c0, "add89") ||
               rewrite(x + (x - y)/c0, (fold(c0 + 1)*x - y)/c0, "add90") ||
               rewrite((x - y)/c0 + x, (fold(c0 + 1)*x - y)/c0, "add91") ||
               rewrite((y - x)/c0 + x, (y + fold(c0 - 1)*x)/c0, "add92") ||
               rewrite((x + y)/c0 + x, (fold(c0 + 1)*x + y)/c0, "add93") ||
               rewrite((y + x)/c0 + x, (y + fold(c0 + 1)*x)/c0, "add94") ||
               rewrite(min(x, y - z) + z, min(x + z, y), "add95") ||
               rewrite(min(y - z, x) + z, min(y, x + z), "add96") ||
               rewrite(min(x, y + c0) + c1, min(x + c1, y), c0 + c1 == 0, "add97") ||
               rewrite(min(y + c0, x) + c1, min(y, x + c1), c0 + c1 == 0, "add98") ||
               rewrite(z + min(x, y - z), min(z + x, y), "add99") ||
               rewrite(z + min(y - z, x), min(y, z + x), "add100") ||
               rewrite(z + max(x, y - z), max(z + x, y), "add101") ||
               rewrite(z + max(y - z, x), max(y, z + x), "add102") ||
               rewrite(max(x, y - z) + z, max(x + z, y), "add103") ||
               rewrite(max(y - z, x) + z, max(y, x + z), "add104") ||
               rewrite(max(x, y + c0) + c1, max(x + c1, y), c0 + c1 == 0, "add105") ||
               rewrite(max(y + c0, x) + c1, max(y, x + c1), c0 + c1 == 0, "add106") ||
               rewrite(max(x, y) + min(x, y), x + y, "add107") ||
               rewrite(max(x, y) + min(y, x), x + y, "add108"))) ||
             (no_overflow_int(op->type) &&
              (rewrite((x/y)*y + x%y, x, "add110") ||
               rewrite((z + x/y)*y + x%y, z*y + x, "add111") ||
               rewrite((x/y + z)*y + x%y, x + z*y, "add112") ||
               rewrite(x%y + ((x/y)*y + z), x + z, "add113") ||
               rewrite(x%y + ((x/y)*y - z), x - z, "add114") ||
               rewrite(x%y + (z + (x/y)*y), x + z, "add115") ||
               rewrite((x/y)*y + (x%y + z), x + z, "add116") ||
               rewrite((x/y)*y + (x%y - z), x - z, "add117") ||
               rewrite((x/y)*y + (z + x%y), x + z, "add118") ||
               rewrite(x/2 + x%2, (x + 1) / 2, "add119") ||

               rewrite(x + ((c0 - x)/c1)*c1, c0 - ((c0 - x) % c1), c1 > 0, "add121") ||
               rewrite(x + ((c0 - x)/c1 + y)*c1, y * c1 - ((c0 - x) % c1) + c0, c1 > 0, "add122") ||
               rewrite(x + (y + (c0 - x)/c1)*c1, y * c1 - ((c0 - x) % c1) + c0, c1 > 0, "add123") ||
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
