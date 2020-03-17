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

    // clang-format off
    if (EVAL_IN_LAMBDA
        ((get_rule_flag("or22", rflag) && rewrite(x || true, true, "or22")) ||
         (get_rule_flag("or23", rflag) && rewrite(x || false, x, "or23")) ||
         (get_rule_flag("or24", rflag) && rewrite(x || x, x, "or24")) ||

         (get_rule_flag("or26", rflag) && rewrite((x || y) || x, (x || y), "or26")) ||
         (get_rule_flag("or27", rflag) && rewrite(x || (x || y), (x || y), "or27")) ||
         (get_rule_flag("or28", rflag) && rewrite((x || y) || y, (x || y), "or28")) ||
         (get_rule_flag("or29", rflag) && rewrite(y || (x || y), (x || y), "or29")) ||

         (get_rule_flag("or31", rflag) && rewrite(((x || y) || z) || x, ((x || y) || z), "or31")) ||
         (get_rule_flag("or32", rflag) && rewrite(x || ((x || y) || z), ((x || y) || z), "or32")) ||
         (get_rule_flag("or33", rflag) && rewrite((z || (x || y)) || x, (z || (x || y)), "or33")) ||
         (get_rule_flag("or34", rflag) && rewrite(x || (z || (x || y)), (z || (x || y)), "or34")) ||
         (get_rule_flag("or35", rflag) && rewrite(((x || y) || z) || y, ((x || y) || z), "or35")) ||
         (get_rule_flag("or36", rflag) && rewrite(y || ((x || y) || z), ((x || y) || z), "or36")) ||
         (get_rule_flag("or37", rflag) && rewrite((z || (x || y)) || y, (z || (x || y)), "or37")) ||
         (get_rule_flag("or38", rflag) && rewrite(y || (z || (x || y)), (z || (x || y)), "or38")) ||

         (get_rule_flag("or40", rflag) && rewrite((x && y) || x, x, "or40")) ||
         (get_rule_flag("or40", rflag) && rewrite(x || (x && y), x, "or41")) ||
         (get_rule_flag("or40", rflag) && rewrite((x && y) || y, y, "or42")) ||
         (get_rule_flag("or43", rflag) && rewrite(y || (x && y), y, "or43")) ||

         (get_rule_flag("or45", rflag) && rewrite(((x || y) || z) || x, ((x || y) || z), "or45")) ||
         (get_rule_flag("or46", rflag) && rewrite(x || ((x || y) || z), ((x || y) || z), "or46")) ||
         (get_rule_flag("or47", rflag) && rewrite((z || (x || y)) || x, (z || (x || y)), "or47")) ||
         (get_rule_flag("or48", rflag) && rewrite(x || (z || (x || y)), (z || (x || y)), "or48")) ||
         (get_rule_flag("or49", rflag) && rewrite(((x || y) || z) || y, ((x || y) || z), "or49")) ||
         (get_rule_flag("or50", rflag) && rewrite(y || ((x || y) || z), ((x || y) || z), "or50")) ||
         (get_rule_flag("or51", rflag) && rewrite((z || (x || y)) || y, (z || (x || y)), "or51")) ||
         (get_rule_flag("or52", rflag) && rewrite(y || (z || (x || y)), (z || (x || y)), "or52")) ||

         (get_rule_flag("or54", rflag) && rewrite(x != y || x == y, true, "or54")) ||
         (get_rule_flag("or55", rflag) && rewrite(x != y || y == x, true, "or55")) ||
         (get_rule_flag("or56", rflag) && rewrite((z || x != y) || x == y, true, "or56")) ||
         (get_rule_flag("or57", rflag) && rewrite((z || x != y) || y == x, true, "or57")) ||
         (get_rule_flag("or58", rflag) && rewrite((x != y || z) || x == y, true, "or58")) ||
         (get_rule_flag("or59", rflag) && rewrite((x != y || z) || y == x, true, "or59")) ||
         (get_rule_flag("or60", rflag) && rewrite((z || x == y) || x != y, true, "or60")) ||
         (get_rule_flag("or61", rflag) && rewrite((z || x == y) || y != x, true, "or61")) ||
         (get_rule_flag("or62", rflag) && rewrite((x == y || z) || x != y, true, "or62")) ||
         (get_rule_flag("or63", rflag) && rewrite((x == y || z) || y != x, true, "or63")) ||
         (get_rule_flag("or64", rflag) && rewrite(x || !x, true, "or64")) ||
         (get_rule_flag("or65", rflag) && rewrite(!x || x, true, "or65")) ||
         (get_rule_flag("or66", rflag) && rewrite(y <= x || x < y, true, "or66")) ||
         (get_rule_flag("or67", rflag) && rewrite(x != c0 || x == c1, x != c0, c0 != c1, "or67")) ||
         (get_rule_flag("or68", rflag) && rewrite(x <= c0 || c1 <= x, true, !is_float(x) && c1 <= c0 + 1, "or68")) ||
         (get_rule_flag("or69", rflag) && rewrite(c1 <= x || x <= c0, true, !is_float(x) && c1 <= c0 + 1, "or69")) ||
         (get_rule_flag("or70", rflag) && rewrite(x <= c0 || c1 < x, true, c1 <= c0, "or70")) ||
         (get_rule_flag("or71", rflag) && rewrite(c1 <= x || x < c0, true, c1 <= c0, "or71")) ||
         (get_rule_flag("or72", rflag) && rewrite(x < c0 || c1 < x, true, c1 < c0, "or72")) ||
         (get_rule_flag("or73", rflag) && rewrite(c1 < x || x < c0, true, c1 < c0, "or73")) ||
         (get_rule_flag("or74", rflag) && rewrite(c0 < x || c1 < x, fold(min(c0, c1)) < x, "or74")) ||
         (get_rule_flag("or75", rflag) && rewrite(c0 <= x || c1 <= x, fold(min(c0, c1)) <= x, "or75")) ||
         (get_rule_flag("or76", rflag) && rewrite(x < c0 || x < c1, x < fold(max(c0, c1)), "or76")) ||
         (get_rule_flag("or77", rflag) && rewrite(x <= c0 || x <= c1, x <= fold(max(c0, c1)), "or77")))) {
        return rewrite.result;
    }
    // clang-format on

    if ((get_rule_flag("or82", rflag) && rewrite(broadcast(x) || broadcast(y), broadcast(x || y, op->type.lanes()), "or82")) ||

        (get_rule_flag("or84", rflag) && rewrite((x && (y || z)) || y, (x && z) || y, "or84")) ||
        (get_rule_flag("or85", rflag) && rewrite((x && (z || y)) || y, (x && z) || y, "or85")) ||
        (get_rule_flag("or86", rflag) && rewrite(y || (x && (y || z)), y || (x && z), "or86")) ||
        (get_rule_flag("or87", rflag) && rewrite(y || (x && (z || y)), y || (x && z), "or87")) ||

        (get_rule_flag("or89", rflag) && rewrite(((y || z) && x) || y, (z && x) || y, "or89")) ||
        (get_rule_flag("or90", rflag) && rewrite(((z || y) && x) || y, (z && x) || y, "or90")) ||
        (get_rule_flag("or91", rflag) && rewrite(y || ((y || z) && x), y || (z && x), "or91")) ||
        (get_rule_flag("or92", rflag) && rewrite(y || ((z || y) && x), y || (z && x), "or92")) ||

        (get_rule_flag("or94", rflag) && rewrite((x || (y && z)) || y, x || y, "or94")) ||
        (get_rule_flag("or95", rflag) && rewrite((x || (z && y)) || y, x || y, "or95")) ||
        (get_rule_flag("or96", rflag) && rewrite(y || (x || (y && z)), y || x, "or96")) ||
        (get_rule_flag("or97", rflag) && rewrite(y || (x || (z && y)), y || x, "or97")) ||

        (get_rule_flag("or99", rflag) && rewrite(((y && z) || x) || y, x || y, "or99")) ||
        (get_rule_flag("or100", rflag) && rewrite(((z && y) || x) || y, x || y, "or100")) ||
        (get_rule_flag("or101", rflag) && rewrite(y || ((y && z) || x), y || x, "or101")) ||
        (get_rule_flag("or102", rflag) && rewrite(y || ((z && y) || x), y || x, "or102")) ||

        (get_rule_flag("or104", rflag) && rewrite((x && y) || (x && z), x && (y || z), "or104")) ||
        (get_rule_flag("or105", rflag) && rewrite((x && y) || (z && x), x && (y || z), "or105")) ||
        (get_rule_flag("or106", rflag) && rewrite((y && x) || (x && z), x && (y || z), "or106")) ||
        (get_rule_flag("or107", rflag) && rewrite((y && x) || (z && x), x && (y || z), "or107")) ||

        (get_rule_flag("or109", rflag) && rewrite(x < y || x < z, x < max(y, z), "or109")) ||
        (get_rule_flag("or110", rflag) && rewrite(y < x || z < x, min(y, z) < x, "or110")) ||
        (get_rule_flag("or111", rflag) && rewrite(x <= y || x <= z, x <= max(y, z), "or111")) ||
        (get_rule_flag("or112", rflag) && rewrite(y <= x || z <= x, min(y, z) <= x, "or112"))) {

        return mutate(std::move(rewrite.result), bounds);
    }

    if (a.same_as(op->a) &&
        b.same_as(op->b)) {
        return op;
    } else {
        return Or::make(a, b);
    }
}

}  // namespace Internal
}  // namespace Halide