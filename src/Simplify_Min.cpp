#include "Simplify_Internal.h"

namespace Halide {
namespace Internal {

Expr Simplify::visit(const Min *op, ExprInfo *bounds) {
    ExprInfo a_bounds, b_bounds;
    Expr a = mutate(op->a, &a_bounds);
    Expr b = mutate(op->b, &b_bounds);

    if (bounds) {
        bounds->min_defined = a_bounds.min_defined && b_bounds.min_defined;
        bounds->max_defined = a_bounds.max_defined || b_bounds.max_defined;
        bounds->min = std::min(a_bounds.min, b_bounds.min);
        if (a_bounds.max_defined && b_bounds.max_defined) {
            bounds->max = std::min(a_bounds.max, b_bounds.max);
        } else if (a_bounds.max_defined) {
            bounds->max = a_bounds.max;
        } else {
            bounds->max = b_bounds.max;
        }
        bounds->alignment = ModulusRemainder::unify(a_bounds.alignment, b_bounds.alignment);
        bounds->trim_bounds_using_alignment();
    }

    // Early out when the bounds tells us one side or the other is smaller
    if (a_bounds.max_defined && b_bounds.min_defined && a_bounds.max <= b_bounds.min) {
        return a;
    }
    if (b_bounds.max_defined && a_bounds.min_defined && b_bounds.max <= a_bounds.min) {
        return b;
    }

    if (may_simplify(op->type)) {

        // Order commutative operations by node type
        if (should_commute(a, b)) {
            std::swap(a, b);
            std::swap(a_bounds, b_bounds);
        }

        int lanes = op->type.lanes();
        auto rewrite = IRMatcher::rewriter(IRMatcher::min(a, b), op->type);

        // clang-format off
        if (EVAL_IN_LAMBDA
            ((get_rule_flag("min47", rflag) && rewrite(min(x, x), x, "min47")) ||
             (get_rule_flag("min48", rflag) && rewrite(min(c0, c1), fold(min(c0, c1)), "min48")) ||
             (get_rule_flag("min49", rflag) && rewrite(min(IRMatcher::Overflow(), x), IRMatcher::Overflow(), "min49")) ||
             (get_rule_flag("min50", rflag) && rewrite(min(x,IRMatcher::Overflow()), IRMatcher::Overflow(), "min50")) ||
             // Cases where one side dominates:
             (get_rule_flag("min52", rflag) && rewrite(min(x, op->type.min()), b, "min52")) ||
             (get_rule_flag("min53", rflag) && rewrite(min(x, op->type.max()), x, "min53")) ||
             (get_rule_flag("min54", rflag) && rewrite(min((x/c0)*c0, x), (x/c0)*c0, c0 > 0, "min54")) ||
             (get_rule_flag("min55", rflag) && rewrite(min(x, (x/c0)*c0), (x/c0)*c0, c0 > 0, "min55")) ||
             (get_rule_flag("min56", rflag) && rewrite(min(min(x, y), x), min(x, y), "min56")) ||
             (get_rule_flag("min57", rflag) && rewrite(min(min(x, y), y), min(x, y), "min57")) ||
             (get_rule_flag("min58", rflag) && rewrite(min(min(min(x, y), z), x), min(min(x, y), z), "min58")) ||
             (get_rule_flag("min59", rflag) && rewrite(min(min(min(x, y), z), y), min(min(x, y), z), "min59")) ||
             (get_rule_flag("min60", rflag) && rewrite(min(min(min(min(x, y), z), w), x), min(min(min(x, y), z), w), "min60")) ||
             (get_rule_flag("min61", rflag) && rewrite(min(min(min(min(x, y), z), w), y), min(min(min(x, y), z), w), "min61")) ||
             (get_rule_flag("min62", rflag) && rewrite(min(min(min(min(min(x, y), z), w), u), x), min(min(min(min(x, y), z), w), u), "min62")) ||
             (get_rule_flag("min63", rflag) && rewrite(min(min(min(min(min(x, y), z), w), u), y), min(min(min(min(x, y), z), w), u), "min63")) ||
             (get_rule_flag("min64", rflag) && rewrite(min(x, max(x, y)), x, "min64")) ||
             (get_rule_flag("min65", rflag) && rewrite(min(x, max(y, x)), x, "min65")) ||
             (get_rule_flag("min66", rflag) && rewrite(min(max(x, y), min(x, y)), min(x, y), "min66")) ||
             (get_rule_flag("min67", rflag) && rewrite(min(max(x, y), min(y, x)), min(y, x), "min67")) ||
             (get_rule_flag("min68", rflag) && rewrite(min(max(x, y), x), x, "min68")) ||
             (get_rule_flag("min69", rflag) && rewrite(min(max(y, x), x), x, "min69")) ||
             (get_rule_flag("min70", rflag) && rewrite(min(max(x, c0), c1), c1, c1 <= c0, "min70")) ||

             (get_rule_flag("min72", rflag) && rewrite(min(intrin(Call::likely, x), x), intrin(Call::likely, x), "min72")) ||
             (get_rule_flag("min73", rflag) && rewrite(min(x, intrin(Call::likely, x)), intrin(Call::likely, x), "min73")) ||
             (get_rule_flag("min74", rflag) && rewrite(min(intrin(Call::likely_if_innermost, x), x), intrin(Call::likely_if_innermost, x), "min74")) ||
             (get_rule_flag("min75", rflag) && rewrite(min(x, intrin(Call::likely_if_innermost, x)), intrin(Call::likely_if_innermost, x), "min75")) ||

             (no_overflow(op->type) &&
              ((get_rule_flag("min78", rflag) && rewrite(min(ramp(x, y), broadcast(z)), ramp(x, y), can_prove(x + y * (lanes - 1) <= z && x <= z, this), "min78")) ||
               (get_rule_flag("min79", rflag) && rewrite(min(ramp(x, y), broadcast(z)), broadcast(z), can_prove(x + y * (lanes - 1) >= z && x >= z, this), "min79")) ||
               // Compare x to a stair-step function in x
               (get_rule_flag("min81", rflag) && rewrite(min(((x + c0)/c1)*c1 + c2, x), x, c1 > 0 && c0 + c2 >= c1 - 1, "min81")) ||
               (get_rule_flag("min82", rflag) && rewrite(min(x, ((x + c0)/c1)*c1 + c2), x, c1 > 0 && c0 + c2 >= c1 - 1, "min82")) ||
               (get_rule_flag("min83", rflag) && rewrite(min(((x + c0)/c1)*c1 + c2, x), ((x + c0)/c1)*c1 + c2, c1 > 0 && c0 + c2 <= 0, "min83")) ||
               (get_rule_flag("min84", rflag) && rewrite(min(x, ((x + c0)/c1)*c1 + c2), ((x + c0)/c1)*c1 + c2, c1 > 0 && c0 + c2 <= 0, "min84")) ||
               // Special cases where c0 or c2 is zero
               (get_rule_flag("min86", rflag) && rewrite(min((x/c1)*c1 + c2, x), x, c1 > 0 && c2 >= c1 - 1, "min86")) ||
               (get_rule_flag("min87", rflag) && rewrite(min(x, (x/c1)*c1 + c2), x, c1 > 0 && c2 >= c1 - 1, "min87")) ||
               (get_rule_flag("min88", rflag) && rewrite(min(((x + c0)/c1)*c1, x), x, c1 > 0 && c0 >= c1 - 1, "min88")) ||
               (get_rule_flag("min89", rflag) && rewrite(min(x, ((x + c0)/c1)*c1), x, c1 > 0 && c0 >= c1 - 1, "min89")) ||
               (get_rule_flag("min90", rflag) && rewrite(min((x/c1)*c1 + c2, x), (x/c1)*c1 + c2, c1 > 0 && c2 <= 0, "min90")) ||
               (get_rule_flag("min91", rflag) && rewrite(min(x, (x/c1)*c1 + c2), (x/c1)*c1 + c2, c1 > 0 && c2 <= 0, "min91")) ||
               (get_rule_flag("min92", rflag) && rewrite(min(((x + c0)/c1)*c1, x), ((x + c0)/c1)*c1, c1 > 0 && c0 <= 0, "min92")) ||
               (get_rule_flag("min93", rflag) && rewrite(min(x, ((x + c0)/c1)*c1), ((x + c0)/c1)*c1, c1 > 0 && c0 <= 0, "min93")))))) {
            return rewrite.result;
        }
        // clang-format on

        // clang-format off
        if (EVAL_IN_LAMBDA
            ((get_rule_flag("min100", rflag) && rewrite(min(min(x, c0), c1), min(x, fold(min(c0, c1))), "min100")) ||
             (get_rule_flag("min101", rflag) && rewrite(min(min(x, c0), y), min(min(x, y), c0), "min101")) ||
             (get_rule_flag("min102", rflag) && rewrite(min(min(x, y), min(x, z)), min(min(y, z), x), "min102")) ||
             (get_rule_flag("min103", rflag) && rewrite(min(min(y, x), min(x, z)), min(min(y, z), x), "min103")) ||
             (get_rule_flag("min104", rflag) && rewrite(min(min(x, y), min(z, x)), min(min(y, z), x), "min104")) ||
             (get_rule_flag("min105", rflag) && rewrite(min(min(y, x), min(z, x)), min(min(y, z), x), "min105")) ||
             (get_rule_flag("min106", rflag) && rewrite(min(min(x, y), min(z, w)), min(min(min(x, y), z), w), "min106")) ||
             (get_rule_flag("min107", rflag) && rewrite(min(broadcast(x), broadcast(y)), broadcast(min(x, y), lanes), "min107")) ||
             (get_rule_flag("min108", rflag) && rewrite(min(broadcast(x), ramp(y, z)), min(ramp(y, z), broadcast(x)), "min108")) ||
             (get_rule_flag("min109", rflag) && rewrite(min(min(x, broadcast(y)), broadcast(z)), min(x, broadcast(min(y, z), lanes)), "min109")) ||
             (get_rule_flag("min110", rflag) && rewrite(min(max(x, y), max(x, z)), max(x, min(y, z)), "min110")) ||
             (get_rule_flag("min111", rflag) && rewrite(min(max(x, y), max(z, x)), max(x, min(y, z)), "min111")) ||
             (get_rule_flag("min112", rflag) && rewrite(min(max(y, x), max(x, z)), max(min(y, z), x), "min112")) ||
             (get_rule_flag("min113", rflag) && rewrite(min(max(y, x), max(z, x)), max(min(y, z), x), "min113")) ||
             (get_rule_flag("min114", rflag) && rewrite(min(max(min(x, y), z), y), min(max(x, z), y), "min114")) ||
             (get_rule_flag("min115", rflag) && rewrite(min(max(min(y, x), z), y), min(y, max(x, z)), "min115")) ||
             (get_rule_flag("min116", rflag) && rewrite(min(min(x, c0), c1), min(x, fold(min(c0, c1))), "min116")) ||

             // Canonicalize a clamp
             (get_rule_flag("min119", rflag) && rewrite(min(max(x, c0), c1), max(min(x, c1), c0), c0 <= c1, "min119")) ||

             (no_overflow(op->type) &&
              ((get_rule_flag("min122", rflag) && rewrite(min(min(x, y) + c0, x), min(x, y + c0), c0 > 0, "min122")) ||
               (get_rule_flag("min123", rflag) && rewrite(min(min(x, y) + c0, x), min(x, y) + c0, c0 < 0, "min123")) ||
               (get_rule_flag("min124", rflag) && rewrite(min(min(y, x) + c0, x), min(y + c0, x), c0 > 0, "min124")) ||
               (get_rule_flag("min125", rflag) && rewrite(min(min(y, x) + c0, x), min(y, x) + c0, c0 < 0, "min125")) ||

               (get_rule_flag("min127", rflag) && rewrite(min(x, min(x, y) + c0), min(x, y + c0), c0 > 0, "min127")) ||
               (get_rule_flag("min128", rflag) && rewrite(min(x, min(x, y) + c0), min(x, y) + c0, c0 < 0, "min128")) ||
               (get_rule_flag("min129", rflag) && rewrite(min(x, min(y, x) + c0), min(x, y + c0), c0 > 0, "min129")) ||
               (get_rule_flag("min130", rflag) && rewrite(min(x, min(y, x) + c0), min(x, y) + c0, c0 < 0, "min130")) ||

               (get_rule_flag("min132", rflag) && rewrite(min(x + c0, c1), min(x, fold(c1 - c0)) + c0, "min132")) ||

               (get_rule_flag("min134", rflag) && rewrite(min(x + c0, y + c1), min(x, y + fold(c1 - c0)) + c0, c1 > c0, "min134")) ||
               (get_rule_flag("min134", rflag) && rewrite(min(x + c0, y + c1), min(x + fold(c0 - c1), y) + c1, c0 > c1, "min135")) ||

               (get_rule_flag("min137", rflag) && rewrite(min(x + y, x + z), x + min(y, z), "min137")) ||
               (get_rule_flag("min138", rflag) && rewrite(min(x + y, z + x), x + min(y, z), "min138")) ||
               (get_rule_flag("min139", rflag) && rewrite(min(y + x, x + z), min(y, z) + x, "min139")) ||
               (get_rule_flag("min140", rflag) && rewrite(min(y + x, z + x), min(y, z) + x, "min140")) ||
               (get_rule_flag("min141", rflag) && rewrite(min(x, x + z), x + min(z, 0), "min141")) ||
               (get_rule_flag("min142", rflag) && rewrite(min(x, z + x), x + min(z, 0), "min142")) ||
               (get_rule_flag("min143", rflag) && rewrite(min(y + x, x), min(y, 0) + x, "min143")) ||
               (get_rule_flag("min144", rflag) && rewrite(min(x + y, x), x + min(y, 0), "min144")) ||

               (get_rule_flag("min146", rflag) && rewrite(min((x*c0 + y)*c1, x*c2 + z), min(y*c1, z) + x*c2, c0 * c1 == c2, "min146")) ||
               (get_rule_flag("min147", rflag) && rewrite(min((y + x*c0)*c1, x*c2 + z), min(y*c1, z) + x*c2, c0 * c1 == c2, "min147")) ||
               (get_rule_flag("min148", rflag) && rewrite(min((x*c0 + y)*c1, z + x*c2), min(y*c1, z) + x*c2, c0 * c1 == c2, "min148")) ||
               (get_rule_flag("min149", rflag) && rewrite(min((y + x*c0)*c1, z + x*c2), min(y*c1, z) + x*c2, c0 * c1 == c2, "min149")) ||

               (get_rule_flag("min151", rflag) && rewrite(min(min(x + y, z), x + w), min(x + min(y, w), z), "min151")) ||
               (get_rule_flag("min152", rflag) && rewrite(min(min(z, x + y), x + w), min(x + min(y, w), z), "min152")) ||
               (get_rule_flag("min153", rflag) && rewrite(min(min(x + y, z), w + x), min(x + min(y, w), z), "min153")) ||
               (get_rule_flag("min154", rflag) && rewrite(min(min(z, x + y), w + x), min(x + min(y, w), z), "min154")) ||

               (get_rule_flag("min156", rflag) && rewrite(min(min(y + x, z), x + w), min(min(y, w) + x, z), "min156")) ||
               (get_rule_flag("min156", rflag) && rewrite(min(min(z, y + x), x + w), min(min(y, w) + x, z), "min157")) ||
               (get_rule_flag("min156", rflag) && rewrite(min(min(y + x, z), w + x), min(min(y, w) + x, z), "min158")) ||
               (get_rule_flag("min156", rflag) && rewrite(min(min(z, y + x), w + x), min(min(y, w) + x, z), "min159")) ||

               (get_rule_flag("min161", rflag) && rewrite(min((x + w) + y, x + z), x + min(w + y, z), "min161")) ||
               (get_rule_flag("min162", rflag) && rewrite(min((w + x) + y, x + z), min(w + y, z) + x, "min162")) ||
               (get_rule_flag("min163", rflag) && rewrite(min((x + w) + y, z + x), x + min(w + y, z), "min163")) ||
               (get_rule_flag("min164", rflag) && rewrite(min((w + x) + y, z + x), min(w + y, z) + x, "min164")) ||
               (get_rule_flag("min165", rflag) && rewrite(min((x + w) + y, x), x + min(w + y, 0), "min165")) ||
               (get_rule_flag("min166", rflag) && rewrite(min((w + x) + y, x), x + min(w + y, 0), "min166")) ||
               (get_rule_flag("min167", rflag) && rewrite(min(x + y, (w + x) + z), x + min(w + z, y), "min167")) ||
               (get_rule_flag("min168", rflag) && rewrite(min(x + y, (x + w) + z), x + min(w + z, y), "min168")) ||
               (get_rule_flag("min169", rflag) && rewrite(min(y + x, (w + x) + z), min(w + z, y) + x, "min169")) ||
               (get_rule_flag("min170", rflag) && rewrite(min(y + x, (x + w) + z), min(w + z, y) + x, "min170")) ||
               (get_rule_flag("min171", rflag) && rewrite(min(x, (w + x) + z), x + min(w + z, 0), "min171")) ||
               (get_rule_flag("min172", rflag) && rewrite(min(x, (x + w) + z), x + min(w + z, 0), "min172")) ||

               (get_rule_flag("min174", rflag) && rewrite(min(y - x, z - x), min(y, z) - x, "min174")) ||
               (get_rule_flag("min175", rflag) && rewrite(min(x - y, x - z), x - max(y, z), "min175")) ||

               (get_rule_flag("min177", rflag) && rewrite(min(x, x - y), x - max(0, y), "min177")) ||
               (get_rule_flag("min178", rflag) && rewrite(min(x - y, x), x - max(0, y), "min178")) ||
               (get_rule_flag("min179", rflag) && rewrite(min(x, (x - y) + z), x + min(0, z - y), "min179")) ||
               (get_rule_flag("min180", rflag) && rewrite(min(x, z + (x - y)), x + min(0, z - y), "min180")) ||
               (get_rule_flag("min181", rflag) && rewrite(min(x, (x - y) - z), x - max(0, y + z), "min181")) ||
               (get_rule_flag("min182", rflag) && rewrite(min((x - y) + z, x), min(0, z - y) + x, "min182")) ||
               (get_rule_flag("min183", rflag) && rewrite(min(z + (x - y), x), min(0, z - y) + x, "min183")) ||
               (get_rule_flag("min184", rflag) && rewrite(min((x - y) - z, x), x - max(0, y + z), "min184")) ||

               (get_rule_flag("min186", rflag) && rewrite(min(x * c0, c1), min(x, fold(c1 / c0)) * c0, c0 > 0 && c1 % c0 == 0, "min186")) ||
               (get_rule_flag("min187", rflag) && rewrite(min(x * c0, c1), max(x, fold(c1 / c0)) * c0, c0 < 0 && c1 % c0 == 0, "min187")) ||

               (get_rule_flag("min189", rflag) && rewrite(min(x * c0, y * c1), min(x, y * fold(c1 / c0)) * c0, c0 > 0 && c1 % c0 == 0, "min189")) ||
               (get_rule_flag("min190", rflag) && rewrite(min(x * c0, y * c1), max(x, y * fold(c1 / c0)) * c0, c0 < 0 && c1 % c0 == 0, "min190")) ||
               (get_rule_flag("min191", rflag) && rewrite(min(x * c0, y * c1), min(x * fold(c0 / c1), y) * c1, c1 > 0 && c0 % c1 == 0, "min191")) ||
               (get_rule_flag("min192", rflag) && rewrite(min(x * c0, y * c1), max(x * fold(c0 / c1), y) * c1, c1 < 0 && c0 % c1 == 0, "min192")) ||
               (get_rule_flag("min193", rflag) && rewrite(min(x * c0, y * c0 + c1), min(x, y + fold(c1 / c0)) * c0, c0 > 0 && c1 % c0 == 0, "min193")) ||
               (get_rule_flag("min194", rflag) && rewrite(min(x * c0, y * c0 + c1), max(x, y + fold(c1 / c0)) * c0, c0 < 0 && c1 % c0 == 0, "min194")) ||

               (get_rule_flag("min196", rflag) && rewrite(min(x / c0, y / c0), min(x, y) / c0, c0 > 0, "min196")) ||
               (get_rule_flag("min197", rflag) && rewrite(min(x / c0, y / c0), max(x, y) / c0, c0 < 0, "min197")) ||

               /* Causes some things to cancel, but also creates large constants and breaks peephole patterns
               rewrite(min(x / c0, c1), min(x, fold(c1 * c0)) / c0, c0 > 0 && !overflows(c1 * c0)) ||
               rewrite(min(x / c0, c1), max(x, fold(c1 * c0)) / c0, c0 < 0 && !overflows(c1 * c0)) ||
               */

               (get_rule_flag("min204", rflag) && rewrite(min(x / c0, y / c0 + c1), min(x, y + fold(c1 * c0)) / c0, c0 > 0 && !overflows(c1 * c0), "min204")) ||
               (get_rule_flag("min205", rflag) && rewrite(min(x / c0, y / c0 + c1), max(x, y + fold(c1 * c0)) / c0, c0 < 0 && !overflows(c1 * c0), "min205")) ||

               (get_rule_flag("min207", rflag) && rewrite(min(select(x, y, z), select(x, w, u)), select(x, min(y, w), min(z, u)), "min207")) ||

               (get_rule_flag("min209", rflag) && rewrite(min(c0 - x, c1), c0 - max(x, fold(c0 - c1)), "min209")))))) {

            return mutate(std::move(rewrite.result), bounds);
        }
        // clang-format on
    }

    const Shuffle *shuffle_a = a.as<Shuffle>();
    const Shuffle *shuffle_b = b.as<Shuffle>();
    if (shuffle_a && shuffle_b &&
        shuffle_a->is_slice() &&
        shuffle_b->is_slice()) {
        if (a.same_as(op->a) && b.same_as(op->b)) {
            return hoist_slice_vector<Min>(op);
        } else {
            return hoist_slice_vector<Min>(Min::make(a, b));
        }
    }

    if (a.same_as(op->a) && b.same_as(op->b)) {
        return op;
    } else {
        return Min::make(a, b);
    }
}

}  // namespace Internal
}  // namespace Halide