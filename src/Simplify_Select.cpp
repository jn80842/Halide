#include "Simplify_Internal.h"

namespace Halide {
namespace Internal {

Expr Simplify::visit(const Select *op, ExprInfo *bounds) {

    ExprInfo t_bounds, f_bounds;
    Expr condition = mutate(op->condition, nullptr);
    Expr true_value = mutate(op->true_value, &t_bounds);
    Expr false_value = mutate(op->false_value, &f_bounds);

    if (bounds) {
        bounds->min_defined = t_bounds.min_defined && f_bounds.min_defined;
        bounds->max_defined = t_bounds.max_defined && f_bounds.max_defined;
        bounds->min = std::min(t_bounds.min, f_bounds.min);
        bounds->max = std::max(t_bounds.max, f_bounds.max);
        bounds->alignment = ModulusRemainder::unify(t_bounds.alignment, f_bounds.alignment);
        bounds->trim_bounds_using_alignment();
    }

    if (may_simplify(op->type)) {
        auto rewrite = IRMatcher::rewriter(IRMatcher::select(condition, true_value, false_value), op->type);

        if (EVAL_IN_LAMBDA
            ((get_rule_flag("sel26", rflag) && rewrite(select(IRMatcher::intrin(Call::likely, true), x, y), x, "sel26")) ||
             (get_rule_flag("sel27", rflag) && rewrite(select(IRMatcher::intrin(Call::likely, false), x, y), y, "sel27")) ||
             (get_rule_flag("sel28", rflag) && rewrite(select(IRMatcher::intrin(Call::likely_if_innermost, true), x, y), x, "sel28")) ||
             (get_rule_flag("sel29", rflag) && rewrite(select(IRMatcher::intrin(Call::likely_if_innermost, false), x, y), y, "sel29")) ||
             (get_rule_flag("sel30", rflag) && rewrite(select(1, x, y), x, "sel30")) ||
             (get_rule_flag("sel31", rflag) && rewrite(select(0, x, y), y, "sel31")) ||
             (get_rule_flag("sel32", rflag) && rewrite(select(x, y, y), y, "sel32")) ||
             rewrite(select(x, intrin(Call::likely, y), y), true_value) ||
             rewrite(select(x, y, intrin(Call::likely, y)), false_value) ||
             rewrite(select(x, intrin(Call::likely_if_innermost, y), y), true_value) ||
             rewrite(select(x, y, intrin(Call::likely_if_innermost, y)), false_value) ||

             // Select evaluates both sides, so if we have an
             // unreachable expression on one side we can't use a
             // signalling error. Call it UB and assume it can't
             // happen. The tricky case to consider is:
             // select(x > 0, a/x, select(x < 0, b/x, indeterminate()))
             // If we use a signalling error and x > 0, then this will
             // evaluate indeterminate(), because the top-level select
             // evaluates both sides.

             (get_rule_flag("sel47", rflag) && rewrite(select(x, y, IRMatcher::Indeterminate()), y, "sel47")) ||
             (get_rule_flag("sel48", rflag) && rewrite(select(x, IRMatcher::Indeterminate(), y), y, "sel48")))) {
            return rewrite.result;
        }

        if (EVAL_IN_LAMBDA
            ((get_rule_flag("sel53", rflag) && rewrite(select(broadcast(x), y, z), select(x, y, z), "sel53")) ||
             (get_rule_flag("sel54", rflag) && rewrite(select(x != y, z, w), select(x == y, w, z), "sel54")) ||
             (get_rule_flag("sel55", rflag) && rewrite(select(x <= y, z, w), select(y < x, w, z), "sel55")) ||
             (get_rule_flag("sel56", rflag) && rewrite(select(x, select(y, z, w), z), select(x && !y, w, z), "sel56")) ||
             (get_rule_flag("sel57", rflag) && rewrite(select(x, select(y, z, w), w), select(x && y, z, w), "sel57")) ||
             (get_rule_flag("sel58", rflag) && rewrite(select(x, y, select(z, y, w)), select(x || z, y, w), "sel58")) ||
             (get_rule_flag("sel59", rflag) && rewrite(select(x, y, select(z, w, y)), select(x || !z, y, w), "sel59")) ||
             (get_rule_flag("sel60", rflag) && rewrite(select(x, select(x, y, z), w), select(x, y, w), "sel60")) ||
             (get_rule_flag("sel61", rflag) && rewrite(select(x, y, select(x, z, w)), select(x, y, w), "sel61")) ||
             (get_rule_flag("sel62", rflag) && rewrite(select(x, y + z, y + w), y + select(x, z, w), "sel62")) ||
             (get_rule_flag("sel63", rflag) && rewrite(select(x, y + z, w + y), y + select(x, z, w), "sel63")) ||
             (get_rule_flag("sel64", rflag) && rewrite(select(x, z + y, y + w), y + select(x, z, w), "sel64")) ||
             (get_rule_flag("sel65", rflag) && rewrite(select(x, z + y, w + y), select(x, z, w) + y, "sel65")) ||
             (get_rule_flag("sel66", rflag) && rewrite(select(x, y - z, y - w), y - select(x, z, w), "sel66")) ||
             (get_rule_flag("sel67", rflag) && rewrite(select(x, y - z, y + w), y + select(x, -z, w), "sel67")) ||
             (get_rule_flag("sel68", rflag) && rewrite(select(x, y + z, y - w), y + select(x, z, -w), "sel68")) ||
             (get_rule_flag("sel69", rflag) && rewrite(select(x, y - z, w + y), y + select(x, -z, w), "sel69")) ||
             (get_rule_flag("sel70", rflag) && rewrite(select(x, z + y, y - w), y + select(x, z, -w), "sel70")) ||
             (get_rule_flag("sel71", rflag) && rewrite(select(x, z - y, w - y), select(x, z, w) - y, "sel71")) ||
             (get_rule_flag("sel72", rflag) && rewrite(select(x, y * z, y * w), y * select(x, z, w), "sel72")) ||
             (get_rule_flag("sel73", rflag) && rewrite(select(x, y * z, w * y), y * select(x, z, w), "sel73")) ||
             (get_rule_flag("sel74", rflag) && rewrite(select(x, z * y, y * w), y * select(x, z, w), "sel74")) ||
             (get_rule_flag("sel75", rflag) && rewrite(select(x, z * y, w * y), select(x, z, w) * y, "sel75")) ||
             (get_rule_flag("sel76", rflag) && rewrite(select(x, z / y, w / y), select(x, z, w) / y, "sel76")) ||
             (get_rule_flag("sel77", rflag) && rewrite(select(x, z % y, w % y), select(x, z, w) % y, "sel77")) ||

             (get_rule_flag("sel79", rflag) && rewrite(select(x < y, x, y), min(x, y), "sel79")) ||
             (get_rule_flag("sel80", rflag) && rewrite(select(x < y, y, x), max(x, y), "sel80")) ||

             (no_overflow_int(op->type) &&
              ((get_rule_flag("sel83", rflag) && rewrite(select(x, y * c0, c1), select(x, y, fold(c1 / c0)) * c0, c1 % c0 == 0, "sel83")) ||
               (get_rule_flag("sel84", rflag) && rewrite(select(x, c0, y * c1), select(x, fold(c0 / c1), y) * c1, c0 % c1 == 0, "sel84")) ||

               // Selects that are equivalent to mins/maxes
               (get_rule_flag("sel87", rflag) && rewrite(select(c0 < x, x + c1, c2), max(x + c1, c2), c2 == c0 + c1 || c2 == c0 + c1 + 1, "sel87")) ||
               (get_rule_flag("sel88", rflag) && rewrite(select(x < c0, c1, x + c2), max(x + c2, c1), c1 == c0 + c2 || c1 + 1 == c0 + c2, "sel88")) ||
               (get_rule_flag("sel89", rflag) && rewrite(select(c0 < x, c1, x + c2), min(x + c2, c1), c1 == c0 + c2 || c1 == c0 + c2 + 1, "sel89")) ||
               (get_rule_flag("sel90", rflag) && rewrite(select(x < c0, x + c1, c2), min(x + c1, c2), c2 == c0 + c1 || c2 + 1 == c0 + c1, "sel90")) ||

               (get_rule_flag("sel92", rflag) && rewrite(select(c0 < x, x, c1), max(x, c1), c1 == c0 + 1, "sel92")) ||
               (get_rule_flag("sel93", rflag) && rewrite(select(x < c0, c1, x), max(x, c1), c1 + 1 == c0, "sel93")) ||
               (get_rule_flag("sel94", rflag) && rewrite(select(c0 < x, c1, x), min(x, c1), c1 == c0 + 1, "sel94")) ||
               (get_rule_flag("sel95", rflag) && rewrite(select(x < c0, x, c1), min(x, c1), c1 + 1 == c0, "sel95")) ||

               false)) ||

             (op->type.is_bool() &&
              ((get_rule_flag("sel100", rflag) && rewrite(select(x, true, false), cast(op->type, x), "sel100")) ||
               (get_rule_flag("sel101", rflag) && rewrite(select(x, false, true), cast(op->type, !x), "sel101")) ||
               (get_rule_flag("sel102", rflag) && rewrite(select(x, y, false), x && y, "sel102")) ||
               (get_rule_flag("sel103", rflag) && rewrite(select(x, y, true), !x || y, "sel103")) ||
               (get_rule_flag("sel104", rflag) && rewrite(select(x, false, y), !x && y, "sel104")) ||
               (get_rule_flag("sel105", rflag) && rewrite(select(x, true, y), x || y, "sel105")))))) {
            return mutate(std::move(rewrite.result), bounds);
        }

        Expr a = condition, b = true_value;
        if (no_overflow_int(op->true_value.type()) &&
            use_synthesized_rules &&
            (
#include "Simplify_Select.inc"
             )) {
            return mutate(std::move(rewrite.result), bounds);
        }
    }

    if (condition.same_as(op->condition) &&
        true_value.same_as(op->true_value) &&
        false_value.same_as(op->false_value)) {
        return op;
    } else {
        return Select::make(std::move(condition), std::move(true_value), std::move(false_value));
    }

}

}
}
