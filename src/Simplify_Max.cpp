#include "Simplify_Internal.h"

namespace Halide {
namespace Internal {

Expr Simplify::visit(const Max *op, ExprInfo *bounds) {
    ExprInfo a_bounds, b_bounds;
    Expr a = mutate(op->a, &a_bounds);
    Expr b = mutate(op->b, &b_bounds);

    if (bounds) {
        bounds->min_defined = a_bounds.min_defined || b_bounds.min_defined;
        bounds->max_defined = a_bounds.max_defined && b_bounds.max_defined;
        bounds->max = std::max(a_bounds.max, b_bounds.max);
        if (a_bounds.min_defined && b_bounds.min_defined) {
            bounds->min = std::max(a_bounds.min, b_bounds.min);
        } else if (a_bounds.min_defined) {
            bounds->min = a_bounds.min;
        } else {
            bounds->min = b_bounds.min;
        }
        bounds->alignment = ModulusRemainder::unify(a_bounds.alignment, b_bounds.alignment);
        bounds->trim_bounds_using_alignment();
    }

    // Early out when the bounds tells us one side or the other is smaller
    if (a_bounds.max_defined && b_bounds.min_defined && a_bounds.max <= b_bounds.min) {
        return b;
    }
    if (b_bounds.max_defined && a_bounds.min_defined && b_bounds.max <= a_bounds.min) {
        return a;
    }

    if (may_simplify(op->type)) {

        // Order commutative operations by node type
        if (should_commute(a, b)) {
            std::swap(a, b);
            std::swap(a_bounds, b_bounds);
        }

        int lanes = op->type.lanes();
        auto rewrite = IRMatcher::rewriter(IRMatcher::max(a, b), op->type);

        if (EVAL_IN_LAMBDA
            ((get_rule_flag("max46", rflag) && rewrite(max(x, x), x, "max46")) ||
             (get_rule_flag("max47", rflag) && rewrite(max(c0, c1), fold(max(c0, c1)), "max47")) ||
             (get_rule_flag("max48", rflag) && rewrite(max(IRMatcher::Indeterminate(), x), a, "max48")) ||
             (get_rule_flag("max49", rflag) && rewrite(max(x, IRMatcher::Indeterminate()), b, "max49")) ||
             (get_rule_flag("max50", rflag) && rewrite(max(IRMatcher::Overflow(), x), a, "max50")) ||
             (get_rule_flag("max51", rflag) && rewrite(max(x,IRMatcher::Overflow()), b, "max51")) ||
             // Cases where one side dominates:
             (get_rule_flag("max53", rflag) && rewrite(max(x, op->type.max()), b, "max53")) ||
             (get_rule_flag("max54", rflag) && rewrite(max(x, op->type.min()), x, "max54")) ||
             (get_rule_flag("max55", rflag) && rewrite(max((x/c0)*c0, x), b, c0 > 0, "max55")) ||
             (get_rule_flag("max56", rflag) && rewrite(max(x, (x/c0)*c0), a, c0 > 0, "max56")) ||
             (get_rule_flag("max57", rflag) && rewrite(max(max(x, y), x), a, "max57")) ||
             (get_rule_flag("max58", rflag) && rewrite(max(max(x, y), y), a, "max58")) ||
             (get_rule_flag("max59", rflag) && rewrite(max(max(max(x, y), z), x), a, "max59")) ||
             (get_rule_flag("max60", rflag) && rewrite(max(max(max(x, y), z), y), a, "max60")) ||
             (get_rule_flag("max61", rflag) && rewrite(max(max(max(max(x, y), z), w), x), a, "max61")) ||
             (get_rule_flag("max62", rflag) && rewrite(max(max(max(max(x, y), z), w), y), a, "max62")) ||
             (get_rule_flag("max63", rflag) && rewrite(max(max(max(max(max(x, y), z), w), u), x), a, "max63")) ||
             (get_rule_flag("max64", rflag) && rewrite(max(max(max(max(max(x, y), z), w), u), y), a, "max64")) ||
             (get_rule_flag("max65", rflag) && rewrite(max(x, min(x, y)), a, "max65")) ||
             (get_rule_flag("max66", rflag) && rewrite(max(x, min(y, x)), a, "max66")) ||
             (get_rule_flag("max67", rflag) && rewrite(max(max(x, y), min(x, y)), a, "max67")) ||
             (get_rule_flag("max68", rflag) && rewrite(max(max(x, y), min(y, x)), a, "max68")) ||
             (get_rule_flag("max69", rflag) && rewrite(max(min(x, y), x), b, "max69")) ||
             (get_rule_flag("max70", rflag) && rewrite(max(min(y, x), x), b, "max70")) ||
             (get_rule_flag("max71", rflag) && rewrite(max(min(x, c0), c1), b, c1 >= c0, "max71")) ||

             (get_rule_flag("max73", rflag) && rewrite(max(intrin(Call::likely, x), x), a, "max73")) ||
             (get_rule_flag("max74", rflag) && rewrite(max(x, intrin(Call::likely, x)), b, "max74")) ||
             (get_rule_flag("max75", rflag) && rewrite(max(intrin(Call::likely_if_innermost, x), x), a, "max75")) ||
             (get_rule_flag("max76", rflag) && rewrite(max(x, intrin(Call::likely_if_innermost, x)), b, "max76")) ||

             (no_overflow(op->type) &&
              ((get_rule_flag("max79", rflag) && rewrite(max(ramp(x, y), broadcast(z)), a, can_prove(x + y * (lanes - 1) >= z && x >= z, this), "max79")) ||
               (get_rule_flag("max80", rflag) && rewrite(max(ramp(x, y), broadcast(z)), b, can_prove(x + y * (lanes - 1) <= z && x <= z, this), "max80")) ||
               // Compare x to a stair-step function in x
               (get_rule_flag("max82", rflag) && rewrite(max(((x + c0)/c1)*c1 + c2, x), a, c1 > 0 && c0 + c2 >= c1 - 1, "max82")) ||
               (get_rule_flag("max83", rflag) && rewrite(max(x, ((x + c0)/c1)*c1 + c2), b, c1 > 0 && c0 + c2 >= c1 - 1, "max83")) ||
               (get_rule_flag("max84", rflag) && rewrite(max(((x + c0)/c1)*c1 + c2, x), b, c1 > 0 && c0 + c2 <= 0, "max84")) ||
               (get_rule_flag("max85", rflag) && rewrite(max(x, ((x + c0)/c1)*c1 + c2), a, c1 > 0 && c0 + c2 <= 0, "max85")) ||
               // Special cases where c0 or c2 is zero
               (get_rule_flag("max87", rflag) && rewrite(max((x/c1)*c1 + c2, x), a, c1 > 0 && c2 >= c1 - 1, "max87")) ||
               (get_rule_flag("max88", rflag) && rewrite(max(x, (x/c1)*c1 + c2), b, c1 > 0 && c2 >= c1 - 1, "max88")) ||
               (get_rule_flag("max89", rflag) && rewrite(max(((x + c0)/c1)*c1, x), a, c1 > 0 && c0 >= c1 - 1, "max89")) ||
               (get_rule_flag("max90", rflag) && rewrite(max(x, ((x + c0)/c1)*c1), b, c1 > 0 && c0 >= c1 - 1, "max90")) ||
               (get_rule_flag("max91", rflag) && rewrite(max((x/c1)*c1 + c2, x), b, c1 > 0 && c2 <= 0, "max91")) ||
               (get_rule_flag("max92", rflag) && rewrite(max(x, (x/c1)*c1 + c2), a, c1 > 0 && c2 <= 0, "max92")) ||
               (get_rule_flag("max93", rflag) && rewrite(max(((x + c0)/c1)*c1, x), b, c1 > 0 && c0 <= 0, "max93")) ||
               (get_rule_flag("max94", rflag) && rewrite(max(x, ((x + c0)/c1)*c1), a, c1 > 0 && c0 <= 0, "max94")))))) {
            return rewrite.result;
        }

        if (EVAL_IN_LAMBDA
            ((get_rule_flag("max99", rflag) && rewrite(max(max(x, c0), c1), max(x, fold(max(c0, c1))), "max99")) ||
             (get_rule_flag("max100", rflag) && rewrite(max(max(x, c0), y), max(max(x, y), c0), "max100")) ||
             (get_rule_flag("max101", rflag) && rewrite(max(max(x, y), max(x, z)), max(max(y, z), x), "max101")) ||
             (get_rule_flag("max102", rflag) && rewrite(max(max(y, x), max(x, z)), max(max(y, z), x), "max102")) ||
             (get_rule_flag("max103", rflag) && rewrite(max(max(x, y), max(z, x)), max(max(y, z), x), "max103")) ||
             (get_rule_flag("max104", rflag) && rewrite(max(max(y, x), max(z, x)), max(max(y, z), x), "max104")) ||
             (get_rule_flag("max105", rflag) && rewrite(max(max(x, y), max(z, w)), max(max(max(x, y), z), w), "max105")) ||
             (get_rule_flag("max106", rflag) && rewrite(max(broadcast(x), broadcast(y)), broadcast(max(x, y), lanes), "max106")) ||
             rewrite(max(broadcast(x), ramp(y, z)), max(b, a)) || // check this one!!
             (get_rule_flag("max108", rflag) && rewrite(max(max(x, broadcast(y)), broadcast(z)), max(x, broadcast(max(y, z), lanes)), "max108")) ||
             (get_rule_flag("max109", rflag) && rewrite(max(min(x, y), min(x, z)), min(x, max(y, z)), "max109")) ||
             (get_rule_flag("max110", rflag) && rewrite(max(min(x, y), min(z, x)), min(x, max(y, z)), "max110")) ||
             (get_rule_flag("max111", rflag) && rewrite(max(min(y, x), min(x, z)), min(max(y, z), x), "max111")) ||
             (get_rule_flag("max112", rflag) && rewrite(max(min(y, x), min(z, x)), min(max(y, z), x), "max112")) ||
             (get_rule_flag("max113", rflag) && rewrite(max(min(max(x, y), z), y), max(min(x, z), y), "max113")) ||
             (get_rule_flag("max114", rflag) && rewrite(max(min(max(y, x), z), y), max(y, min(x, z)), "max114")) ||
             (get_rule_flag("max115", rflag) && rewrite(max(max(x, c0), c1), max(x, fold(max(c0, c1))), "max115")) ||

             (no_overflow(op->type) &&
              ((get_rule_flag("max118", rflag) && rewrite(max(max(x, y) + c0, x), max(x, y + c0), c0 < 0, "max118")) ||
               (get_rule_flag("max119", rflag) && rewrite(max(max(x, y) + c0, x), max(x, y) + c0, c0 > 0, "max119")) ||
               (get_rule_flag("max120", rflag) && rewrite(max(max(y, x) + c0, x), max(y + c0, x), c0 < 0, "max120")) ||
               (get_rule_flag("max121", rflag) && rewrite(max(max(y, x) + c0, x), max(y, x) + c0, c0 > 0, "max121")) ||

               (get_rule_flag("max123", rflag) && rewrite(max(x, max(x, y) + c0), max(x, y + c0), c0 < 0, "max123")) ||
               (get_rule_flag("max124", rflag) && rewrite(max(x, max(x, y) + c0), max(x, y) + c0, c0 > 0, "max124")) ||
               (get_rule_flag("max125", rflag) && rewrite(max(x, max(y, x) + c0), max(x, y + c0), c0 < 0, "max125")) ||
               (get_rule_flag("max126", rflag) && rewrite(max(x, max(y, x) + c0), max(x, y) + c0, c0 > 0, "max126")) ||

               (get_rule_flag("max128", rflag) && rewrite(max(x + c0, c1), max(x, fold(c1 - c0)) + c0, "max128")) ||

               (get_rule_flag("max130", rflag) && rewrite(max(x + c0, y + c1), max(x, y + fold(c1 - c0)) + c0, c1 > c0, "max130")) ||
               (get_rule_flag("max131", rflag) && rewrite(max(x + c0, y + c1), max(x + fold(c0 - c1), y) + c1, c0 > c1, "max131")) ||

               (get_rule_flag("max133", rflag) && rewrite(max(x + y, x + z), x + max(y, z), "max133")) ||
               (get_rule_flag("max134", rflag) && rewrite(max(x + y, z + x), x + max(y, z), "max134")) ||
               (get_rule_flag("max135", rflag) && rewrite(max(y + x, x + z), max(y, z) + x, "max135")) ||
               (get_rule_flag("max136", rflag) && rewrite(max(y + x, z + x), max(y, z) + x, "max136")) ||
               (get_rule_flag("max137", rflag) && rewrite(max(x, x + z), x + max(z, 0), "max137")) ||
               (get_rule_flag("max138", rflag) && rewrite(max(x, z + x), x + max(z, 0), "max138")) ||
               (get_rule_flag("max139", rflag) && rewrite(max(y + x, x), max(y, 0) + x, "max139")) ||
               (get_rule_flag("max140", rflag) && rewrite(max(x + y, x), x + max(y, 0), "max140")) ||

               (get_rule_flag("max142", rflag) && rewrite(max((x*c0 + y)*c1, x*c2 + z), max(y*c1, z) + x*c2, c0 * c1 == c2, "max142")) ||
               (get_rule_flag("max143", rflag) && rewrite(max((y + x*c0)*c1, x*c2 + z), max(y*c1, z) + x*c2, c0 * c1 == c2, "max143")) ||
               (get_rule_flag("max144", rflag) && rewrite(max((x*c0 + y)*c1, z + x*c2), max(y*c1, z) + x*c2, c0 * c1 == c2, "max144")) ||
               (get_rule_flag("max145", rflag) && rewrite(max((y + x*c0)*c1, z + x*c2), max(y*c1, z) + x*c2, c0 * c1 == c2, "max145")) ||

               (get_rule_flag("max147", rflag) && rewrite(max(max(x + y, z), x + w), max(x + max(y, w), z), "max147")) ||
               (get_rule_flag("max148", rflag) && rewrite(max(max(z, x + y), x + w), max(x + max(y, w), z), "max148")) ||
               (get_rule_flag("max149", rflag) && rewrite(max(max(x + y, z), w + x), max(x + max(y, w), z), "max149")) ||
               (get_rule_flag("max150", rflag) && rewrite(max(max(z, x + y), w + x), max(x + max(y, w), z), "max150")) ||

               (get_rule_flag("max152", rflag) && rewrite(max(max(y + x, z), x + w), max(max(y, w) + x, z), "max152")) ||
               (get_rule_flag("max153", rflag) && rewrite(max(max(z, y + x), x + w), max(max(y, w) + x, z), "max153")) ||
               (get_rule_flag("max154", rflag) && rewrite(max(max(y + x, z), w + x), max(max(y, w) + x, z), "max154")) ||
               (get_rule_flag("max155", rflag) && rewrite(max(max(z, y + x), w + x), max(max(y, w) + x, z), "max155")) ||

               (get_rule_flag("max157", rflag) && rewrite(max((x + w) + y, x + z), x + max(w + y, z), "max157")) ||
               (get_rule_flag("max158", rflag) && rewrite(max((w + x) + y, x + z), max(w + y, z) + x, "max158")) ||
               (get_rule_flag("max159", rflag) && rewrite(max((x + w) + y, z + x), x + max(w + y, z), "max159")) ||
               (get_rule_flag("max160", rflag) && rewrite(max((w + x) + y, z + x), max(w + y, z) + x, "max160")) ||
               (get_rule_flag("max161", rflag) && rewrite(max((x + w) + y, x), x + max(w + y, 0), "max161")) ||
               (get_rule_flag("max162", rflag) && rewrite(max((w + x) + y, x), x + max(w + y, 0), "max162")) ||
               (get_rule_flag("max163", rflag) && rewrite(max(x + y, (w + x) + z), x + max(w + z, y), "max163")) ||
               (get_rule_flag("max164", rflag) && rewrite(max(x + y, (x + w) + z), x + max(w + z, y), "max164")) ||
               (get_rule_flag("max165", rflag) && rewrite(max(y + x, (w + x) + z), max(w + z, y) + x, "max165")) ||
               (get_rule_flag("max166", rflag) && rewrite(max(y + x, (x + w) + z), max(w + z, y) + x, "max166")) ||
               (get_rule_flag("max167", rflag) && rewrite(max(x, (w + x) + z), x + max(w + z, 0), "max167")) ||
               (get_rule_flag("max168", rflag) && rewrite(max(x, (x + w) + z), x + max(w + z, 0), "max168")) ||

               (get_rule_flag("max169", rflag) && rewrite(max(y - x, z - x), max(y, z) - x, "max169")) ||
               (get_rule_flag("max170", rflag) && rewrite(max(x - y, x - z), x - min(y, z), "max170")) ||

               (get_rule_flag("max173", rflag) && rewrite(max(x, x - y), x - min(0, y), "max173")) ||
               (get_rule_flag("max174", rflag) && rewrite(max(x - y, x), x - min(0, y), "max174")) ||
               (get_rule_flag("max175", rflag) && rewrite(max(x, (x - y) + z), x + max(0, z - y), "max175")) ||
               (get_rule_flag("max176", rflag) && rewrite(max(x, z + (x - y)), x + max(0, z - y), "max176")) ||
               (get_rule_flag("max177", rflag) && rewrite(max(x, (x - y) - z), x - min(0, y + z), "max177")) ||
               (get_rule_flag("max178", rflag) && rewrite(max((x - y) + z, x), max(0, z - y) + x, "max178")) ||
               (get_rule_flag("max179", rflag) && rewrite(max(z + (x - y), x), max(0, z - y) + x, "max179")) ||
               (get_rule_flag("max180", rflag) && rewrite(max((x - y) - z, x), x - min(0, y + z), "max180")) ||

               (get_rule_flag("max182", rflag) && rewrite(max(x * c0, c1), max(x, fold(c1 / c0)) * c0, c0 > 0 && c1 % c0 == 0, "max182")) ||
               (get_rule_flag("max183", rflag) && rewrite(max(x * c0, c1), min(x, fold(c1 / c0)) * c0, c0 < 0 && c1 % c0 == 0, "max183")) ||

               (get_rule_flag("max185", rflag) && rewrite(max(x * c0, y * c1), max(x, y * fold(c1 / c0)) * c0, c0 > 0 && c1 % c0 == 0, "max185")) ||
               (get_rule_flag("max186", rflag) && rewrite(max(x * c0, y * c1), min(x, y * fold(c1 / c0)) * c0, c0 < 0 && c1 % c0 == 0, "max186")) ||
               (get_rule_flag("max187", rflag) && rewrite(max(x * c0, y * c1), max(x * fold(c0 / c1), y) * c1, c1 > 0 && c0 % c1 == 0, "max187")) ||
               (get_rule_flag("max188", rflag) && rewrite(max(x * c0, y * c1), min(x * fold(c0 / c1), y) * c1, c1 < 0 && c0 % c1 == 0, "max188")) ||
               (get_rule_flag("max189", rflag) && rewrite(max(x * c0, y * c0 + c1), max(x, y + fold(c1 / c0)) * c0, c0 > 0 && c1 % c0 == 0, "max189")) ||
               (get_rule_flag("max190", rflag) && rewrite(max(x * c0, y * c0 + c1), min(x, y + fold(c1 / c0)) * c0, c0 < 0 && c1 % c0 == 0, "max190")) ||

               (get_rule_flag("max192", rflag) && rewrite(max(x / c0, y / c0), max(x, y) / c0, c0 > 0, "max192")) ||
               (get_rule_flag("max193", rflag) && rewrite(max(x / c0, y / c0), min(x, y) / c0, c0 < 0, "max193")) ||

               /* Causes some things to cancel, but also creates large constants and breaks peephole patterns
                  rewrite(max(x / c0, c1), max(x, fold(c1 * c0)) / c0, c0 > 0 && !overflows(c1 * c0)) ||
                  rewrite(max(x / c0, c1), min(x, fold(c1 * c0)) / c0, c0 < 0 && !overflows(c1 * c0)) ||
               */

               (get_rule_flag("max200", rflag) && rewrite(max(x / c0, y / c0 + c1), max(x, y + fold(c1 * c0)) / c0, c0 > 0 && !overflows(c1 * c0), "max200")) ||
               (get_rule_flag("max201", rflag) && rewrite(max(x / c0, y / c0 + c1), min(x, y + fold(c1 * c0)) / c0, c0 < 0 && !overflows(c1 * c0), "max201")) ||

               (get_rule_flag("max203", rflag) && rewrite(max(select(x, y, z), select(x, w, u)), select(x, max(y, w), max(z, u)), "max203")) ||

               (get_rule_flag("max205", rflag) && rewrite(max(c0 - x, c1), c0 - min(x, fold(c0 - c1)), "max205")))) ||
             false)) {

            return mutate(std::move(rewrite.result), bounds);
        }

        if (no_overflow_int(op->type) &&
            use_synthesized_rules &&
            (
#include "Simplify_Max.inc"
              )) {
            return mutate(std::move(rewrite.result), bounds);
        }
    }

    const Shuffle *shuffle_a = a.as<Shuffle>();
    const Shuffle *shuffle_b = b.as<Shuffle>();
    if (shuffle_a && shuffle_b &&
        shuffle_a->is_slice() &&
        shuffle_b->is_slice()) {
        if (a.same_as(op->a) && b.same_as(op->b)) {
            return hoist_slice_vector<Max>(op);
        } else {
            return hoist_slice_vector<Max>(Max::make(a, b));
        }
    }

    if (a.same_as(op->a) && b.same_as(op->b)) {
        return op;
    } else {
        return Max::make(a, b);
    }
}

}
}
