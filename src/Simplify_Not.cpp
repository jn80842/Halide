#include "Simplify_Internal.h"

namespace Halide {
namespace Internal {

Expr Simplify::visit(const Not *op, ExprInfo *bounds) {
    Expr a = mutate(op->a, nullptr);

    auto rewrite = IRMatcher::rewriter(IRMatcher::not_op(a), op->type);

    if ((get_rule_flag("not11", rflag) && rewrite(!c0, fold(!c0), "not11")) ||
        (get_rule_flag("not12", rflag) && rewrite(!(x < y), y <= x, "not12")) ||
        (get_rule_flag("not13", rflag) && rewrite(!(x <= y), y < x, "not13")) ||
        (get_rule_flag("not14", rflag) && rewrite(!(x > y), y >= x, "not14")) ||
        (get_rule_flag("not15", rflag) && rewrite(!(x >= y), y > x, "not15")) ||
        (get_rule_flag("not16", rflag) && rewrite(!(x == y), x != y, "not16")) ||
        (get_rule_flag("not17", rflag) && rewrite(!(x != y), x == y, "not17")) ||
        (get_rule_flag("not18", rflag) && rewrite(!!x, x, "not18"))) {
        return rewrite.result;
    }

    if ((get_rule_flag("not22", rflag) && rewrite(!broadcast(x), broadcast(!x, op->type.lanes()), "not22")) ||
        (get_rule_flag("not23", rflag) && rewrite(!intrin(Call::likely, x), intrin(Call::likely, !x), "not23")) ||
        (get_rule_flag("not24", rflag) && rewrite(!intrin(Call::likely_if_innermost, x), intrin(Call::likely_if_innermost, !x), "not24"))) {
        return mutate(std::move(rewrite.result), bounds);
    }

    if (a.same_as(op->a)) {
        return op;
    } else {
        return Not::make(a);
    }
}

}  // namespace Internal
}  // namespace Halide