#include "Interval.h"
#include "IREquality.h"
#include "IRMatch.h"
#include "IROperator.h"

namespace Halide {
namespace Internal {

namespace {

IRMatcher::Wild<0> x;
IRMatcher::Wild<1> y;
IRMatcher::WildConst<0> c0;
IRMatcher::WildConst<1> c1;

Expr make_max_helper(const Expr &a, const Expr &b) {
    auto rewrite = IRMatcher::rewriter(IRMatcher::max(a, b), a.type());

    Expr pos_inf = Interval::pos_inf();
    Expr neg_inf = Interval::neg_inf();
    if (rewrite(max(x, x), x, "itvl21") ||
        rewrite(max(x, pos_inf), pos_inf, "itvl22") ||
        rewrite(max(pos_inf, x), pos_inf, "itvl23") ||
        rewrite(max(x, neg_inf), x, "itvl24") ||
        rewrite(max(neg_inf, x), x, "itvl25") ||
        rewrite(max(c0, c1), fold(max(c0, c1)), "itvl26") ||
        rewrite(max(c0, x), max(x, c0), "itvl27") ||
        rewrite(max(max(x, c0), c1), max(x, fold(max(c0, c1))), "itvl28") ||
        rewrite(max(max(x, c0), y), max(max(x, y), c0), "itvl29") ||
        rewrite(max(x, max(y, c0)), max(max(x, y), c0), "itvl30") ||
        rewrite(max(max(x, y), x), max(x, y), "itvl31") ||
        rewrite(max(max(x, y), y), max(x, y), "itvl32") ||
        rewrite(max(x, max(x, y)), max(x, y), "itvl33") ||
        rewrite(max(y, max(x, y)), max(x, y), "itvl34")) {
        return rewrite.result;
    } else {
        return max(a, b);
    }
}

Expr make_min_helper(const Expr &a, const Expr &b) {
    auto rewrite = IRMatcher::rewriter(IRMatcher::min(a, b), a.type());

    Expr pos_inf = Interval::pos_inf();
    Expr neg_inf = Interval::neg_inf();
    if (rewrite(min(x, x), x, "itvl46") ||
        rewrite(min(x, pos_inf), x, "itvl47") ||
        rewrite(min(pos_inf, x), x, "itvl48") ||
        rewrite(min(x, neg_inf), neg_inf, "itvl49") ||
        rewrite(min(neg_inf, x), neg_inf, "itvl50") ||
        rewrite(min(c0, c1), fold(min(c0, c1)), "itvl51") ||
        rewrite(min(c0, x), min(x, c0), "itvl52") ||
        rewrite(min(min(x, c0), c1), min(x, fold(min(c0, c1))), "itvl53") ||
        rewrite(min(min(x, c0), y), min(min(x, y), c0), "itvl54") ||
        rewrite(min(x, min(y, c0)), min(min(x, y), c0), "itvl55") ||
        rewrite(min(min(x, y), x), min(x, y), "itvl56") ||
        rewrite(min(min(x, y), y), min(x, y), "itvl57") ||
        rewrite(min(x, min(x, y)), min(x, y), "itvl58") ||
        rewrite(min(y, min(x, y)), min(x, y), "itvl59")) {
        return rewrite.result;
    } else {
        return min(a, b);
    }
}

}  // namespace

// This is called repeatedly by bounds inference and the solver to
// build large expressions, so we want to simplify eagerly to avoid
// monster expressions.
Expr Interval::make_max(const Expr &a, const Expr &b) {
    return make_max_helper(a, b);
}

Expr Interval::make_min(const Expr &a, const Expr &b) {
    return make_min_helper(a, b);
}

void Interval::include(const Interval &i) {
    max = Interval::make_max(max, i.max);
    min = Interval::make_min(min, i.min);
}

void Interval::include(const Expr &e) {
    max = Interval::make_max(max, e);
    min = Interval::make_min(min, e);
}

Interval Interval::make_union(const Interval &a, const Interval &b) {
    Interval result = a;
    result.include(b);
    return result;
}

Interval Interval::make_intersection(const Interval &a, const Interval &b) {
    return Interval(Interval::make_max(a.min, b.min),
                    Interval::make_min(a.max, b.max));
}

// Use Handle types for positive and negative infinity, to prevent
// accidentally doing arithmetic on them.
Expr Interval::pos_inf_expr = Variable::make(Handle(), "pos_inf");
Expr Interval::neg_inf_expr = Variable::make(Handle(), "neg_inf");

Expr Interval::pos_inf_noinline() {
    return Interval::pos_inf_expr;
}
Expr Interval::neg_inf_noinline() {
    return Interval::neg_inf_expr;
}

}  // namespace Internal
}  // namespace Halide