#include "Simplify_Internal.h"

namespace Halide {
namespace Internal {

Expr Simplify::visit(const Or *op, ExprInfo *bounds) {
    if (truths.count(op)) {
        return const_true(op->type.lanes());
    }

    Expr a = mutate(op->a, nullptr);
    Expr b = mutate(op->b, nullptr);

    if (should_commute(a, b)) {
        std::swap(a, b);
    }

    auto rewrite = IRMatcher::rewriter(IRMatcher::or_op(a, b), op->type);

    if (EVAL_IN_LAMBDA
        ((get_rule_flag("or21", rflag) && rewrite(x || true, b, "or21")) ||
         (get_rule_flag("or22", rflag) && rewrite(x || false, a, "or22")) ||
         (get_rule_flag("or23", rflag) && rewrite(x || x, a, "or23")) ||

         (get_rule_flag("or25", rflag) && rewrite((x || y) || x, a, "or25")) ||
         (get_rule_flag("or26", rflag) && rewrite(x || (x || y), b, "or26")) ||
         (get_rule_flag("or27", rflag) && rewrite((x || y) || y, a, "or27")) ||
         (get_rule_flag("or28", rflag) && rewrite(y || (x || y), b, "or28")) ||

         (get_rule_flag("or30", rflag) && rewrite(((x || y) || z) || x, a, "or30")) ||
         (get_rule_flag("or31", rflag) && rewrite(x || ((x || y) || z), b, "or31")) ||
         (get_rule_flag("or32", rflag) && rewrite((z || (x || y)) || x, a, "or32")) ||
         (get_rule_flag("or33", rflag) && rewrite(x || (z || (x || y)), b, "or33")) ||
         (get_rule_flag("or34", rflag) && rewrite(((x || y) || z) || y, a, "or34")) ||
         (get_rule_flag("or35", rflag) && rewrite(y || ((x || y) || z), b, "or35")) ||
         (get_rule_flag("or36", rflag) && rewrite((z || (x || y)) || y, a, "or36")) ||
         (get_rule_flag("or37", rflag) && rewrite(y || (z || (x || y)), b, "or37")) ||

         (get_rule_flag("or39", rflag) && rewrite((x && y) || x, b, "or39")) ||
         (get_rule_flag("or40", rflag) && rewrite(x || (x && y), a, "or40")) ||
         (get_rule_flag("or41", rflag) && rewrite((x && y) || y, b, "or41")) ||
         (get_rule_flag("or42", rflag) && rewrite(y || (x && y), a, "or42")) ||

         (get_rule_flag("or44", rflag) && rewrite(((x || y) || z) || x, a, "or44")) ||
         (get_rule_flag("or45", rflag) && rewrite(x || ((x || y) || z), b, "or45")) ||
         (get_rule_flag("or46", rflag) && rewrite((z || (x || y)) || x, a, "or46")) ||
         (get_rule_flag("or47", rflag) && rewrite(x || (z || (x || y)), b, "or47")) ||
         (get_rule_flag("or48", rflag) && rewrite(((x || y) || z) || y, a, "or48")) ||
         (get_rule_flag("or49", rflag) && rewrite(y || ((x || y) || z), b, "or49")) ||
         (get_rule_flag("or50", rflag) && rewrite((z || (x || y)) || y, a, "or50")) ||
         (get_rule_flag("or51", rflag) && rewrite(y || (z || (x || y)), b, "or51")) ||

         (get_rule_flag("or53", rflag) && rewrite(x != y || x == y, true, "or53")) ||
         (get_rule_flag("or54", rflag) && rewrite(x != y || y == x, true, "or54")) ||
         (get_rule_flag("or55", rflag) && rewrite((z || x != y) || x == y, true, "or55")) ||
         (get_rule_flag("or56", rflag) && rewrite((z || x != y) || y == x, true, "or56")) ||
         (get_rule_flag("or57", rflag) && rewrite((x != y || z) || x == y, true, "or57")) ||
         (get_rule_flag("or58", rflag) && rewrite((x != y || z) || y == x, true, "or58")) ||
         (get_rule_flag("or59", rflag) && rewrite((z || x == y) || x != y, true, "or59")) ||
         (get_rule_flag("or60", rflag) && rewrite((z || x == y) || y != x, true, "or60")) ||
         (get_rule_flag("or61", rflag) && rewrite((x == y || z) || x != y, true, "or61")) ||
         (get_rule_flag("or62", rflag) && rewrite((x == y || z) || y != x, true, "or62")) ||
         (get_rule_flag("or63", rflag) && rewrite(x || !x, true, "or63")) ||
         (get_rule_flag("or64", rflag) && rewrite(!x || x, true, "or64")) ||
         (get_rule_flag("or65", rflag) && rewrite(y <= x || x < y, true, "or65")) ||
         (get_rule_flag("or66", rflag) && rewrite(x != c0 || x == c1, a, c0 != c1, "or66")) ||
         (get_rule_flag("or67", rflag) && rewrite(x <= c0 || c1 <= x, true, !is_float(x) && c1 <= c0 + 1, "or67")) ||
         (get_rule_flag("or68", rflag) && rewrite(c1 <= x || x <= c0, true, !is_float(x) && c1 <= c0 + 1, "or68")) ||
         (get_rule_flag("or69", rflag) && rewrite(x <= c0 || c1 < x, true, c1 <= c0, "or69")) ||
         (get_rule_flag("or70", rflag) && rewrite(c1 <= x || x < c0, true, c1 <= c0, "or70")) ||
         (get_rule_flag("or71", rflag) && rewrite(x < c0 || c1 < x, true, c1 < c0, "or71")) ||
         (get_rule_flag("or72", rflag) && rewrite(c1 < x || x < c0, true, c1 < c0, "or72")) ||
         (get_rule_flag("or73", rflag) && rewrite(c0 < x || c1 < x, fold(min(c0, c1)) < x, "or73")) ||
         (get_rule_flag("or74", rflag) && rewrite(c0 <= x || c1 <= x, fold(min(c0, c1)) <= x, "or74")) ||
         (get_rule_flag("or75", rflag) && rewrite(x < c0 || x < c1, x < fold(max(c0, c1)), "or75")) ||
         (get_rule_flag("or76", rflag) && rewrite(x <= c0 || x <= c1, x <= fold(max(c0, c1)), "or76")))) {
        return rewrite.result;
    }

    if (EVAL_IN_LAMBDA
        (get_rule_flag("or81", rflag) && rewrite(broadcast(x) || broadcast(y), broadcast(x || y, op->type.lanes()), "or81") ||

         (get_rule_flag("or83", rflag) && rewrite(x < y || y < x, x != y, "or83")) ||

         (get_rule_flag("or85", rflag) && rewrite((x && (y || z)) || y, (x && z) || y, "or85")) ||
         (get_rule_flag("or86", rflag) && rewrite((x && (z || y)) || y, (x && z) || y, "or86")) ||
         (get_rule_flag("or87", rflag) && rewrite(y || (x && (y || z)), y || (x && z), "or87")) ||
         (get_rule_flag("or88", rflag) && rewrite(y || (x && (z || y)), y || (x && z), "or88")) ||

         (get_rule_flag("or90", rflag) && rewrite(((y || z) && x) || y, (z && x) || y, "or90")) ||
         (get_rule_flag("or91", rflag) && rewrite(((z || y) && x) || y, (z && x) || y, "or91")) ||
         (get_rule_flag("or92", rflag) && rewrite(y || ((y || z) && x), y || (z && x), "or92")) ||
         (get_rule_flag("or93", rflag) && rewrite(y || ((z || y) && x), y || (z && x), "or93")) ||

         (get_rule_flag("or95", rflag) && rewrite((x || (y && z)) || y, x || y, "or95")) ||
         (get_rule_flag("or96", rflag) && rewrite((x || (z && y)) || y, x || y, "or96")) ||
         (get_rule_flag("or97", rflag) && rewrite(y || (x || (y && z)), y || x, "or97")) ||
         (get_rule_flag("or98", rflag) && rewrite(y || (x || (z && y)), y || x, "or98")) ||

         (get_rule_flag("or100", rflag) && rewrite(((y && z) || x) || y, x || y, "or100")) ||
         (get_rule_flag("or101", rflag) && rewrite(((z && y) || x) || y, x || y, "or101")) ||
         (get_rule_flag("or102", rflag) && rewrite(y || ((y && z) || x), y || x, "or102")) ||
         (get_rule_flag("or103", rflag) && rewrite(y || ((z && y) || x), y || x, "or103")) ||

         (get_rule_flag("or105", rflag) && rewrite((x && y) || (x && z), x && (y || z), "or105")) ||
         (get_rule_flag("or106", rflag) && rewrite((x && y) || (z && x), x && (y || z), "or106")) ||
         (get_rule_flag("or107", rflag) && rewrite((y && x) || (x && z), x && (y || z), "or107")) ||
         (get_rule_flag("or108", rflag) && rewrite((y && x) || (z && x), x && (y || z), "or108")) ||

         (get_rule_flag("or110", rflag) && rewrite(x < y || x < z, x < max(y, z), "or110")) ||
         (get_rule_flag("or111", rflag) && rewrite(y < x || z < x, min(y, z) < x, "or111")) ||
         (get_rule_flag("or112", rflag) && rewrite(x <= y || x <= z, x <= max(y, z), "or112")) ||
         (get_rule_flag("or113", rflag) && rewrite(y <= x || z <= x, min(y, z) <= x, "or113")))) {

        return mutate(std::move(rewrite.result), bounds);
    }


    if (use_synthesized_rules &&
        (
#include "Simplify_Or.inc"
         )) {
        return mutate(std::move(rewrite.result), bounds);
    }


    if (a.same_as(op->a) &&
        b.same_as(op->b)) {
        return op;
    } else {
        return Or::make(a, b);
    }
}

}
}
