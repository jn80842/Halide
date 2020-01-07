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
        std::swap(a, b);
    }

    auto rewrite = IRMatcher::rewriter(IRMatcher::and_op(a, b), op->type);

    if (EVAL_IN_LAMBDA
        (rewrite(x && true, a) ||
         rewrite(x && false, b) ||
         rewrite(x && x, a) ||

         rewrite((x && y) && x, a) ||
         rewrite(x && (x && y), b) ||
         rewrite((x && y) && y, a) ||
         rewrite(y && (x && y), b) ||

         rewrite(((x && y) && z) && x, a) ||
         rewrite(x && ((x && y) && z), b) ||
         rewrite((z && (x && y)) && x, a) ||
         rewrite(x && (z && (x && y)), b) ||
         rewrite(((x && y) && z) && y, a) ||
         rewrite(y && ((x && y) && z), b) ||
         rewrite((z && (x && y)) && y, a) ||
         rewrite(y && (z && (x && y)), b) ||

         rewrite((x || y) && x, b) ||
         rewrite(x && (x || y), a) ||
         rewrite((x || y) && y, b) ||
         rewrite(y && (x || y), a) ||

         (get_rule_flag("and45", rflag) && rewrite(x != y && x == y, false, "and45")) ||
         (get_rule_flag("and46", rflag) && rewrite(x != y && y == x, false, "and46")) ||
         (get_rule_flag("and47", rflag) && rewrite((z && x != y) && x == y, false, "and47")) ||
         (get_rule_flag("and48", rflag) && rewrite((z && x != y) && y == x, false, "and48")) ||
         (get_rule_flag("and49", rflag) && rewrite((x != y && z) && x == y, false, "and49")) ||
         (get_rule_flag("and50", rflag) && rewrite((x != y && z) && y == x, false, "and50")) ||
         (get_rule_flag("and51", rflag) && rewrite((z && x == y) && x != y, false, "and51")) ||
         (get_rule_flag("and52", rflag) && rewrite((z && x == y) && y != x, false, "and52")) ||
         (get_rule_flag("and53", rflag) && rewrite((x == y && z) && x != y, false, "and53")) ||
         (get_rule_flag("and54", rflag) && rewrite((x == y && z) && y != x, false, "and54")) ||
         (get_rule_flag("and55", rflag) && rewrite(x && !x, false, "and55")) ||
         (get_rule_flag("and56", rflag) && rewrite(!x && x, false, "and56")) ||
         (get_rule_flag("and57", rflag) && rewrite(y <= x && x < y, false, "and57")) ||
         rewrite(x != c0 && x == c1, b, c0 != c1) ||
         // Note: In the predicate below, if undefined overflow
         // occurs, the predicate counts as false. If well-defined
         // overflow occurs, the condition couldn't possibly
         // trigger because c0 + 1 will be the smallest possible
         // value.
         (get_rule_flag("and64", rflag) && rewrite(c0 < x && x < c1, false, !is_float(x) && c1 <= c0 + 1, "and64")) ||
         (get_rule_flag("and65", rflag) && rewrite(x < c1 && c0 < x, false, !is_float(x) && c1 <= c0 + 1, "and65")) ||
         (get_rule_flag("and66", rflag) && rewrite(x <= c1 && c0 < x, false, c1 <= c0, "and66")) ||
         (get_rule_flag("and67", rflag) && rewrite(c0 <= x && x < c1, false, c1 <= c0, "and67")) ||
         (get_rule_flag("and68", rflag) && rewrite(c0 <= x && x <= c1, false, c1 < c0, "and68")) ||
         (get_rule_flag("and69", rflag) && rewrite(x <= c1 && c0 <= x, false, c1 < c0, "and69")) ||
         rewrite(c0 < x && x != c1, a, c1 <= c0) ||
         (get_rule_flag("and71", rflag) && rewrite(c0 < x && c1 < x, fold(max(c0, c1)) < x, "and71")) ||
         (get_rule_flag("and72", rflag) && rewrite(c0 <= x && c1 <= x, fold(max(c0, c1)) <= x, "and72")) ||
         (get_rule_flag("and73", rflag) && rewrite(x < c0 && x < c1, x < fold(min(c0, c1)), "and73")) ||
         (get_rule_flag("and74", rflag) && rewrite(x <= c0 && x <= c1, x <= fold(min(c0, c1)), "and74")))) {
        return rewrite.result;
    }

    if ((get_rule_flag("and78", rflag) && rewrite(broadcast(x) && broadcast(y), broadcast(x && y, op->type.lanes()), "and78"))||

        (get_rule_flag("and80", rflag) && rewrite(c0 < x && x < c1, x == fold(c0 + 1), !is_float(x) && c1 == c0 + 2, "and80")) ||
        (get_rule_flag("and81", rflag) && rewrite(c0 <= x && x < c1, x == c0, !is_float(x) && c1 == c0 + 1, "and81")) ||
        (get_rule_flag("and82", rflag) && rewrite(c0 < x && x <= c1, x == fold(c0 + 1), !is_float(x) && c1 == c0 + 1, "and82")) ||
        (get_rule_flag("and83", rflag) && rewrite(x < c1 && c0 < x, x == fold(c0 + 1), !is_float(x) && c1 == c0 + 2, "and83")) ||
        (get_rule_flag("and84", rflag) && rewrite(x < c1 && c0 <= x, x == c0, !is_float(x) && c1 == c0 + 1, "and84")) ||
        (get_rule_flag("and85", rflag) && rewrite(x <= c1 && c0 < x, x == fold(c0 + 1), !is_float(x) && c1 == c0 + 1, "and85")) ||

        (get_rule_flag("and87", rflag) && rewrite(c0 < x && x != c1, c1 < x, !is_float(x) && c1 == c0 + 1, "and87")) ||

        (get_rule_flag("and89", rflag) && rewrite((x || (y && z)) && y, (x || z) && y, "and89")) ||
        (get_rule_flag("and90", rflag) && rewrite((x || (z && y)) && y, (x || z) && y, "and90")) ||
        (get_rule_flag("and91", rflag) && rewrite(y && (x || (y && z)), y && (x || z), "and91")) ||
        (get_rule_flag("and92", rflag) && rewrite(y && (x || (z && y)), y && (x || z), "and92")) ||

        (get_rule_flag("and94", rflag) && rewrite(((y && z) || x) && y, (z || x) && y, "and94")) ||
        (get_rule_flag("and95", rflag) && rewrite(((z && y) || x) && y, (z || x) && y, "and95")) ||
        (get_rule_flag("and96", rflag) && rewrite(y && ((y && z) || x), y && (z || x), "and96")) ||
        (get_rule_flag("and97", rflag) && rewrite(y && ((z && y) || x), y && (z || x), "and97")) ||

        (get_rule_flag("and99", rflag) && rewrite((x && (y || z)) && y, x && y, "and99")) ||
        (get_rule_flag("and100", rflag) && rewrite((x && (z || y)) && y, x && y, "and100")) ||
        (get_rule_flag("and101", rflag) && rewrite(y && (x && (y || z)), y && x, "and101")) ||
        (get_rule_flag("and102", rflag) && rewrite(y && (x && (z || y)), y && x, "and102")) ||

        (get_rule_flag("and104", rflag) && rewrite(((y || z) && x) && y, x && y, "and104")) ||
        (get_rule_flag("and105", rflag) && rewrite(((z || y) && x) && y, x && y, "and105")) ||
        (get_rule_flag("and106", rflag) && rewrite(y && ((y || z) && x), y && x, "and106")) ||
        (get_rule_flag("and107", rflag) && rewrite(y && ((z || y) && x), y && x, "and107")) ||

        (get_rule_flag("and109", rflag) && rewrite((x || y) && (x || z), x || (y && z), "and109")) ||
        (get_rule_flag("and110", rflag) && rewrite((x || y) && (z || x), x || (y && z), "and110")) ||
        (get_rule_flag("and111", rflag) && rewrite((y || x) && (x || z), x || (y && z), "and111")) ||
        (get_rule_flag("and112", rflag) && rewrite((y || x) && (z || x), x || (y && z), "and112")) ||

        (get_rule_flag("and114", rflag) && rewrite(x < y && x < z, x < min(y, z), "and114")) ||
        (get_rule_flag("and115", rflag) && rewrite(y < x && z < x, max(y, z) < x, "and115")) ||

        (get_rule_flag("and117", rflag) && rewrite(x <= y && y <= x, x == y, "and117")) ||
        (get_rule_flag("and118", rflag) && rewrite((z && x <= y) && y <= x, z && (x == y), "and118")) ||
        (get_rule_flag("and119", rflag) && rewrite((x <= y && z) && y <= x, z && (x == y), "and119")) ||

        (get_rule_flag("and120", rflag) && rewrite(x <= y && x <= z, x <= min(y, z), "and120")) ||
        (get_rule_flag("and121", rflag) && rewrite(y <= x && z <= x, max(y, z) <= x, "and121")) ||
        false) {

        return mutate(std::move(rewrite.result), bounds);
    }

    if (use_synthesized_rules &&
        (
#include "Simplify_And.inc"
         )) {
        return mutate(std::move(rewrite.result), bounds);
    }

    if (a.same_as(op->a) &&
        b.same_as(op->b)) {
        return op;
    } else {
        return And::make(a, b);
    }
}

}
}
