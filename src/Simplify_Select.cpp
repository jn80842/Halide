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

        // clang-format off
        if (EVAL_IN_LAMBDA
            ((get_rule_flag("sel27", rflag) && rewrite(select(IRMatcher::intrin(Call::likely, true), x, y), x, "sel27")) ||
             (get_rule_flag("sel28", rflag) && rewrite(select(IRMatcher::intrin(Call::likely, false), x, y), y, "sel28")) ||
             (get_rule_flag("sel29", rflag) && rewrite(select(IRMatcher::intrin(Call::likely_if_innermost, true), x, y), x, "sel29")) ||
             (get_rule_flag("sel30", rflag) && rewrite(select(IRMatcher::intrin(Call::likely_if_innermost, false), x, y), y, "sel30")) ||
             (get_rule_flag("sel31", rflag) && rewrite(select(1, x, y), x, "sel31")) ||
             (get_rule_flag("sel32", rflag) && rewrite(select(0, x, y), y, "sel32")) ||
             (get_rule_flag("sel33", rflag) && rewrite(select(x, y, y), y, "sel33")) ||
             (get_rule_flag("sel34", rflag) && rewrite(select(x, intrin(Call::likely, y), y), intrin(Call::likely, y), "sel34")) ||
             (get_rule_flag("sel35", rflag) && rewrite(select(x, y, intrin(Call::likely, y)), intrin(Call::likely, y), "sel35")) ||
             (get_rule_flag("sel36", rflag) && rewrite(select(x, intrin(Call::likely_if_innermost, y), y), intrin(Call::likely_if_innermost, y), "sel36")) ||
             (get_rule_flag("sel37", rflag) && rewrite(select(x, y, intrin(Call::likely_if_innermost, y)), intrin(Call::likely_if_innermost, y), "sel37")) ||
             false)) {
            return rewrite.result;
        }
        // clang-format on

        // clang-format off
        if (EVAL_IN_LAMBDA
            ((get_rule_flag("sel45", rflag) && rewrite(select(broadcast(x), y, z), select(x, y, z), "sel45")) ||
             (get_rule_flag("sel46", rflag) && rewrite(select(x != y, z, w), select(x == y, w, z), "sel46")) ||
             (get_rule_flag("sel47", rflag) && rewrite(select(x <= y, z, w), select(y < x, w, z), "sel47")) ||
             (get_rule_flag("sel48", rflag) && rewrite(select(x, select(y, z, w), z), select(x && !y, w, z), "sel48")) ||
             (get_rule_flag("sel49", rflag) && rewrite(select(x, select(y, z, w), w), select(x && y, z, w), "sel49")) ||
             (get_rule_flag("sel50", rflag) && rewrite(select(x, y, select(z, y, w)), select(x || z, y, w), "sel50")) ||
             (get_rule_flag("sel51", rflag) && rewrite(select(x, y, select(z, w, y)), select(x || !z, y, w), "sel51")) ||
             (get_rule_flag("sel52", rflag) && rewrite(select(x, select(x, y, z), w), select(x, y, w), "sel52")) ||
             (get_rule_flag("sel53", rflag) && rewrite(select(x, y, select(x, z, w)), select(x, y, w), "sel53")) ||
             (get_rule_flag("sel54", rflag) && rewrite(select(x, y + z, y + w), y + select(x, z, w), "sel54")) ||
             (get_rule_flag("sel55", rflag) && rewrite(select(x, y + z, w + y), y + select(x, z, w), "sel55")) ||
             (get_rule_flag("sel56", rflag) && rewrite(select(x, z + y, y + w), y + select(x, z, w), "sel56")) ||
             (get_rule_flag("sel57", rflag) && rewrite(select(x, z + y, w + y), select(x, z, w) + y, "sel57")) ||
             (get_rule_flag("sel58", rflag) && rewrite(select(x, y - z, y - w), y - select(x, z, w), "sel58")) ||
             (get_rule_flag("sel59", rflag) && rewrite(select(x, y - z, y + w), y + select(x, -z, w), "sel59")) ||
             (get_rule_flag("sel60", rflag) && rewrite(select(x, y + z, y - w), y + select(x, z, -w), "sel60")) ||
             (get_rule_flag("sel61", rflag) && rewrite(select(x, y - z, w + y), y + select(x, -z, w), "sel61")) ||
             (get_rule_flag("sel62", rflag) && rewrite(select(x, z + y, y - w), y + select(x, z, -w), "sel62")) ||
             (get_rule_flag("sel63", rflag) && rewrite(select(x, z - y, w - y), select(x, z, w) - y, "sel63")) ||
             (get_rule_flag("sel64", rflag) && rewrite(select(x, y * z, y * w), y * select(x, z, w), "sel64")) ||
             (get_rule_flag("sel65", rflag) && rewrite(select(x, y * z, w * y), y * select(x, z, w), "sel65")) ||
             (get_rule_flag("sel66", rflag) && rewrite(select(x, z * y, y * w), y * select(x, z, w), "sel66")) ||
             (get_rule_flag("sel67", rflag) && rewrite(select(x, z * y, w * y), select(x, z, w) * y, "sel67")) ||
             (get_rule_flag("sel68", rflag) && rewrite(select(x, z / y, w / y), select(x, z, w) / y, "sel68")) ||
             (get_rule_flag("sel69", rflag) && rewrite(select(x, z % y, w % y), select(x, z, w) % y, "sel69")) ||

             (get_rule_flag("sel71", rflag) && rewrite(select(x, (y + z) + u, y + w), y + select(x, z + u, w), "sel71")) ||
             (get_rule_flag("sel72", rflag) && rewrite(select(x, (y + z) - u, y + w), y + select(x, z - u, w), "sel72")) ||
             (get_rule_flag("sel73", rflag) && rewrite(select(x, u + (y + z), y + w), y + select(x, u + z, w), "sel73")) ||
             (get_rule_flag("sel74", rflag) && rewrite(select(x, y + z, (y + w) + u), y + select(x, z, w + u), "sel74")) ||
             (get_rule_flag("sel75", rflag) && rewrite(select(x, y + z, (y + w) - u), y + select(x, z, w - u), "sel75")) ||
             (get_rule_flag("sel76", rflag) && rewrite(select(x, y + z, u + (y + w)), y + select(x, z, u + w), "sel76")) ||

             (get_rule_flag("sel78", rflag) && rewrite(select(x, (y + z) + u, w + y), y + select(x, z + u, w), "sel78")) ||
             (get_rule_flag("sel79", rflag) && rewrite(select(x, (y + z) - u, w + y), y + select(x, z - u, w), "sel79")) ||
             (get_rule_flag("sel80", rflag) && rewrite(select(x, u + (y + z), w + y), y + select(x, u + z, w), "sel80")) ||
             (get_rule_flag("sel81", rflag) && rewrite(select(x, y + z, (w + y) + u), y + select(x, z, w + u), "sel81")) ||
             (get_rule_flag("sel82", rflag) && rewrite(select(x, y + z, (w + y) - u), y + select(x, z, w - u), "sel82")) ||
             (get_rule_flag("sel83", rflag) && rewrite(select(x, y + z, u + (w + y)), y + select(x, z, u + w), "sel83")) ||

             (get_rule_flag("sel85", rflag) && rewrite(select(x, (z + y) + u, y + w), y + select(x, z + u, w), "sel85")) ||
             (get_rule_flag("sel86", rflag) && rewrite(select(x, (z + y) - u, y + w), y + select(x, z - u, w), "sel86")) ||
             (get_rule_flag("sel87", rflag) && rewrite(select(x, u + (z + y), y + w), y + select(x, u + z, w), "sel87")) ||
             (get_rule_flag("sel88", rflag) && rewrite(select(x, z + y, (y + w) + u), y + select(x, z, w + u), "sel88")) ||
             (get_rule_flag("sel89", rflag) && rewrite(select(x, z + y, (y + w) - u), y + select(x, z, w - u), "sel89")) ||
             (get_rule_flag("sel90", rflag) && rewrite(select(x, z + y, u + (y + w)), y + select(x, z, u + w), "sel90")) ||

             (get_rule_flag("sel92", rflag) && rewrite(select(x, (z + y) + u, w + y), select(x, z + u, w) + y, "sel92")) ||
             (get_rule_flag("sel93", rflag) && rewrite(select(x, (z + y) - u, w + y), select(x, z - u, w) + y, "sel93")) ||
             (get_rule_flag("sel94", rflag) && rewrite(select(x, u + (z + y), w + y), select(x, u + z, w) + y, "sel94")) ||
             (get_rule_flag("sel95", rflag) && rewrite(select(x, z + y, (w + y) + u), select(x, z, w + u) + y, "sel95")) ||
             (get_rule_flag("sel96", rflag) && rewrite(select(x, z + y, (w + y) - u), select(x, z, w - u) + y, "sel96")) ||
             (get_rule_flag("sel97", rflag) && rewrite(select(x, z + y, u + (w + y)), select(x, z, u + w) + y, "sel97")) ||

             (get_rule_flag("sel99", rflag) && rewrite(select(x < y, x, y), min(x, y), "sel99")) ||
             (get_rule_flag("sel100", rflag) && rewrite(select(x < y, y, x), max(x, y), "sel100")) ||
             (get_rule_flag("sel101", rflag) && rewrite(select(x < 0, x * y, 0), min(x, 0) * y, "sel101")) ||
             (get_rule_flag("sel102", rflag) && rewrite(select(x < 0, 0, x * y), max(x, 0) * y, "sel102")) ||

             (no_overflow_int(op->type) &&
              ((get_rule_flag("sel105", rflag) && rewrite(select(x, y * c0, c1), select(x, y, fold(c1 / c0)) * c0, c1 % c0 == 0, "sel105")) ||
               (get_rule_flag("sel105", rflag) && rewrite(select(x, c0, y * c1), select(x, fold(c0 / c1), y) * c1, c0 % c1 == 0, "sel106")) ||

               // Selects that are equivalent to mins/maxes
               (get_rule_flag("sel109", rflag) && rewrite(select(c0 < x, x + c1, c2), max(x + c1, c2), c2 == c0 + c1 || c2 == c0 + c1 + 1, "sel109")) ||
               (get_rule_flag("sel110", rflag) && rewrite(select(x < c0, c1, x + c2), max(x + c2, c1), c1 == c0 + c2 || c1 + 1 == c0 + c2, "sel110")) ||
               (get_rule_flag("sel111", rflag) && rewrite(select(c0 < x, c1, x + c2), min(x + c2, c1), c1 == c0 + c2 || c1 == c0 + c2 + 1, "sel111")) ||
               (get_rule_flag("sel112", rflag) && rewrite(select(x < c0, x + c1, c2), min(x + c1, c2), c2 == c0 + c1 || c2 + 1 == c0 + c1, "sel112")) ||

               (get_rule_flag("sel114", rflag) && rewrite(select(c0 < x, x, c1), max(x, c1), c1 == c0 + 1, "sel114")) ||
               (get_rule_flag("sel115", rflag) && rewrite(select(x < c0, c1, x), max(x, c1), c1 + 1 == c0, "sel115")) ||
               (get_rule_flag("sel116", rflag) && rewrite(select(c0 < x, c1, x), min(x, c1), c1 == c0 + 1, "sel116")) ||
               (get_rule_flag("sel117", rflag) && rewrite(select(x < c0, x, c1), min(x, c1), c1 + 1 == c0, "sel117")))) ||

             (op->type.is_bool() &&
              ((get_rule_flag("sel120", rflag) && rewrite(select(x, true, false), cast(op->type, x), "sel120")) ||
               (get_rule_flag("sel121", rflag) && rewrite(select(x, false, true), cast(op->type, !x), "sel121")) ||
               (get_rule_flag("sel122", rflag) && rewrite(select(x, y, false), x && y, "sel122")) ||
               (get_rule_flag("sel123", rflag) && rewrite(select(x, y, true), !x || y, "sel123")) ||
               (get_rule_flag("sel124", rflag) && rewrite(select(x, false, y), !x && y, "sel124")) ||
               (get_rule_flag("sel125", rflag) && rewrite(select(x, true, y), x || y, "sel125")))))) {
            return mutate(std::move(rewrite.result), bounds);
        }
        // clang-format on
    }

    if (condition.same_as(op->condition) &&
        true_value.same_as(op->true_value) &&
        false_value.same_as(op->false_value)) {
        return op;
    } else {
        return Select::make(std::move(condition), std::move(true_value), std::move(false_value));
    }
}

}  // namespace Internal
}  // namespace Halide