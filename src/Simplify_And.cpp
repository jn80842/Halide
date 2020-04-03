#include "Simplify_Internal.h"

namespace Halide {
namespace Internal {

Expr Simplify::visit(const And *op, ExprInfo *bounds) {
    if (falsehoods.count(op)) {
        return const_false(op->type.lanes());
    }

    Expr a = mutate(op->a, nullptr);
    Expr b = mutate(op->b, nullptr);

    // Order commutative operations by node type
    if (should_commute(a, b)) {
        debug(0) << "triggered should_commute: " << a << " ; " << b << "\n";
        std::swap(a, b);
    }

    auto rewrite = IRMatcher::rewriter(IRMatcher::and_op(a, b), op->type);

    // clang-format off
    if (EVAL_IN_LAMBDA
        ((get_rule_flag("and23", rflag) && rewrite(x && true, x, "and23")) ||
         (get_rule_flag("and24", rflag) && rewrite(x && false, false, "and24")) ||
         (get_rule_flag("and25", rflag) && rewrite(x && x, x, "and25")) ||

         (get_rule_flag("and27", rflag) && rewrite((x && y) && x, (x && y), "and27")) ||
         (get_rule_flag("and28", rflag) && rewrite(x && (x && y), (x && y), "and28")) ||
         (get_rule_flag("and29", rflag) && rewrite((x && y) && y, (x && y), "and29")) ||
         (get_rule_flag("and30", rflag) && rewrite(y && (x && y), (x && y), "and30")) ||

         (get_rule_flag("and32", rflag) && rewrite(((x && y) && z) && x, ((x && y) && z), "and32")) ||
         (get_rule_flag("and33", rflag) && rewrite(x && ((x && y) && z), ((x && y) && z), "and33")) ||
         (get_rule_flag("and34", rflag) && rewrite((z && (x && y)) && x, (z && (x && y)), "and34")) ||
         (get_rule_flag("and35", rflag) && rewrite(x && (z && (x && y)), (z && (x && y)), "and35")) ||
         (get_rule_flag("and36", rflag) && rewrite(((x && y) && z) && y, ((x && y) && z), "and36")) ||
         (get_rule_flag("and37", rflag) && rewrite(y && ((x && y) && z), ((x && y) && z), "and37")) ||
         (get_rule_flag("and38", rflag) && rewrite((z && (x && y)) && y, (z && (x && y)), "and38")) ||
         (get_rule_flag("and39", rflag) && rewrite(y && (z && (x && y)), (z && (x && y)), "and39")) ||

         (get_rule_flag("and41", rflag) && rewrite((x || y) && x, x, "and41")) ||
         (get_rule_flag("and42", rflag) && rewrite(x && (x || y), x, "and42")) ||
         (get_rule_flag("and43", rflag) && rewrite((x || y) && y, y, "and43")) ||
         (get_rule_flag("and44", rflag) && rewrite(y && (x || y), y, "and44")) ||

         (get_rule_flag("and46", rflag) && rewrite(x != y && x == y, false, "and46")) ||
         (get_rule_flag("and47", rflag) && rewrite(x != y && y == x, false, "and47")) ||
         (get_rule_flag("and48", rflag) && rewrite((z && x != y) && x == y, false, "and48")) ||
         (get_rule_flag("and49", rflag) && rewrite((z && x != y) && y == x, false, "and49")) ||
         (get_rule_flag("and50", rflag) && rewrite((x != y && z) && x == y, false, "and50")) ||
         (get_rule_flag("and51", rflag) && rewrite((x != y && z) && y == x, false, "and51")) ||
         (get_rule_flag("and52", rflag) && rewrite((z && x == y) && x != y, false, "and52")) ||
         (get_rule_flag("and53", rflag) && rewrite((z && x == y) && y != x, false, "and53")) ||
         (get_rule_flag("and54", rflag) && rewrite((x == y && z) && x != y, false, "and54")) ||
         (get_rule_flag("and55", rflag) && rewrite((x == y && z) && y != x, false, "and55")) ||
         (get_rule_flag("and56", rflag) && rewrite(x && !x, false, "and56")) ||
         (get_rule_flag("and57", rflag) && rewrite(!x && x, false, "and57")) ||
         (get_rule_flag("and58", rflag) && rewrite(y <= x && x < y, false, "and58")) ||
         (get_rule_flag("and59", rflag) && rewrite(x != c0 && x == c1, x == c1, c0 != c1, "and59")) ||
         // Note: In the predicate below, if undefined overflow
         // occurs, the predicate counts as false. If well-defined
         // overflow occurs, the condition couldn't possibly
         // trigger because c0 + 1 will be the smallest possible
         // value.
         (get_rule_flag("and65", rflag) && rewrite(c0 < x && x < c1, false, !is_float(x) && c1 <= c0 + 1, "and65")) ||
         (get_rule_flag("and66", rflag) && rewrite(x < c1 && c0 < x, false, !is_float(x) && c1 <= c0 + 1, "and66")) ||
         (get_rule_flag("and67", rflag) && rewrite(x <= c1 && c0 < x, false, c1 <= c0, "and67")) ||
         (get_rule_flag("and68", rflag) && rewrite(c0 <= x && x < c1, false, c1 <= c0, "and68")) ||
         (get_rule_flag("and69", rflag) && rewrite(c0 <= x && x <= c1, false, c1 < c0, "and69")) ||
         (get_rule_flag("and70", rflag) && rewrite(x <= c1 && c0 <= x, false, c1 < c0, "and70")) ||
         (get_rule_flag("and71", rflag) && rewrite(c0 < x && c1 < x, fold(max(c0, c1)) < x, "and71")) ||
         (get_rule_flag("and72", rflag) && rewrite(c0 <= x && c1 <= x, fold(max(c0, c1)) <= x, "and72")) ||
         (get_rule_flag("and73", rflag) && rewrite(x < c0 && x < c1, x < fold(min(c0, c1)), "and73")) ||
         (get_rule_flag("and74", rflag) && rewrite(x <= c0 && x <= c1, x <= fold(min(c0, c1)), "and74")))) {
        return rewrite.result;
    }
    // clang-format on

    if ((get_rule_flag("and79", rflag) && rewrite(broadcast(x) && broadcast(y), broadcast(x && y, op->type.lanes()), "and79")) ||

        (get_rule_flag("and81", rflag) && rewrite((x || (y && z)) && y, (x || z) && y, "and81")) ||
        (get_rule_flag("and82", rflag) && rewrite((x || (z && y)) && y, (x || z) && y, "and82")) ||
        (get_rule_flag("and83", rflag) && rewrite(y && (x || (y && z)), y && (x || z), "and83")) ||
        (get_rule_flag("and84", rflag) && rewrite(y && (x || (z && y)), y && (x || z), "and84")) ||

        (get_rule_flag("and86", rflag) && rewrite(((y && z) || x) && y, (z || x) && y, "and86")) ||
        (get_rule_flag("and87", rflag) && rewrite(((z && y) || x) && y, (z || x) && y, "and87")) ||
        (get_rule_flag("and88", rflag) && rewrite(y && ((y && z) || x), y && (z || x), "and88")) ||
        (get_rule_flag("and89", rflag) && rewrite(y && ((z && y) || x), y && (z || x), "and89")) ||

        (get_rule_flag("and91", rflag) && rewrite((x && (y || z)) && y, x && y, "and91")) ||
        (get_rule_flag("and92", rflag) && rewrite((x && (z || y)) && y, x && y, "and92")) ||
        (get_rule_flag("and93", rflag) && rewrite(y && (x && (y || z)), y && x, "and93")) ||
        (get_rule_flag("and94", rflag) && rewrite(y && (x && (z || y)), y && x, "and94")) ||

        (get_rule_flag("and96", rflag) && rewrite(((y || z) && x) && y, x && y, "and96")) ||
        (get_rule_flag("and97", rflag) && rewrite(((z || y) && x) && y, x && y, "and97")) ||
        (get_rule_flag("and98", rflag) && rewrite(y && ((y || z) && x), y && x, "and98")) ||
        (get_rule_flag("and99", rflag) && rewrite(y && ((z || y) && x), y && x, "and99")) ||

        (get_rule_flag("and101", rflag) && rewrite((x || y) && (x || z), x || (y && z), "and101")) ||
        (get_rule_flag("and102", rflag) && rewrite((x || y) && (z || x), x || (y && z), "and102")) ||
        (get_rule_flag("and103", rflag) && rewrite((y || x) && (x || z), x || (y && z), "and103")) ||
        (get_rule_flag("and104", rflag) && rewrite((y || x) && (z || x), x || (y && z), "and104")) ||

        (get_rule_flag("and106", rflag) && rewrite(x < y && x < z, x < min(y, z), "and106")) ||
        (get_rule_flag("and107", rflag) && rewrite(y < x && z < x, max(y, z) < x, "and107")) ||
        (get_rule_flag("and108", rflag) && rewrite(x <= y && x <= z, x <= min(y, z), "and108")) ||
        (get_rule_flag("and109", rflag) && rewrite(y <= x && z <= x, max(y, z) <= x, "and109"))) {

        return mutate(std::move(rewrite.result), bounds);
    }

    if (a.same_as(op->a) &&
        b.same_as(op->b)) {
        return op;
    } else {
        return And::make(a, b);
    }
}

}  // namespace Internal
}  // namespace Halide