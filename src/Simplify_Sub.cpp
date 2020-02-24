#include "Simplify_Internal.h"

namespace Halide {
namespace Internal {

Expr Simplify::visit(const Sub *op, ExprInfo *bounds) {
    ExprInfo a_bounds, b_bounds;
    Expr a = mutate(op->a, &a_bounds);
    Expr b = mutate(op->b, &b_bounds);

    if (bounds && no_overflow_int(op->type)) {
        // Doesn't account for correlated a, b, so any
        // cancellation rule that exploits that should always
        // remutate to recalculate the bounds.
        bounds->min_defined = a_bounds.min_defined && b_bounds.max_defined;
        bounds->max_defined = a_bounds.max_defined && b_bounds.min_defined;
        if (sub_would_overflow(64, a_bounds.min, b_bounds.max)) {
            bounds->min_defined = false;
            bounds->min = 0;
        } else {
            bounds->min = a_bounds.min - b_bounds.max;
        }
        if (sub_would_overflow(64, a_bounds.max, b_bounds.min)) {
            bounds->max_defined = false;
            bounds->max = 0;
        } else {
            bounds->max = a_bounds.max - b_bounds.min;
        }
        bounds->alignment = a_bounds.alignment - b_bounds.alignment;
        bounds->trim_bounds_using_alignment();
    }

    if (may_simplify(op->type)) {

        auto rewrite = IRMatcher::rewriter(IRMatcher::sub(a, b), op->type);
        const int lanes = op->type.lanes();

        if (rewrite(c0 - c1, fold(c0 - c1), "sub38") ||
            rewrite(IRMatcher::Overflow() - x, IRMatcher::Overflow(), "sub39") ||
            rewrite(x - IRMatcher::Overflow(), IRMatcher::Overflow(), "sub40") ||
            rewrite(x - 0, x, "sub41")) {
            return rewrite.result;
        }

        // clang-format off
        if (EVAL_IN_LAMBDA
            ((!op->type.is_uint() && rewrite(x - c0, x + fold(-c0), !overflows(-c0), "sub47")) ||
             rewrite(x - x, 0, "sub48") || // We want to remutate this just to get better bounds
             rewrite(ramp(x, y) - ramp(z, w), ramp(x - z, y - w, lanes), "sub49") ||
             rewrite(ramp(x, y) - broadcast(z), ramp(x - z, y, lanes), "sub50") ||
             rewrite(broadcast(x) - ramp(z, w), ramp(x - z, -w, lanes), "sub51") ||
             rewrite(broadcast(x) - broadcast(y), broadcast(x - y, lanes), "sub52") ||
             rewrite(select(x, y, z) - select(x, w, u), select(x, y - w, z - u), "sub53") ||
             rewrite(select(x, y, z) - y, select(x, 0, z - y), "sub54") ||
             rewrite(select(x, y, z) - z, select(x, y - z, 0), "sub55") ||
             rewrite(y - select(x, y, z), select(x, 0, y - z), "sub56") ||
             rewrite(z - select(x, y, z), select(x, z - y, 0), "sub57") ||

             rewrite(select(x, y + w, z) - y, select(x, w, z - y), "sub59") ||
             rewrite(select(x, w + y, z) - y, select(x, w, z - y), "sub60") ||
             rewrite(select(x, y, z + w) - z, select(x, y - z, w), "sub61") ||
             rewrite(select(x, y, w + z) - z, select(x, y - z, w), "sub62") ||
             rewrite(y - select(x, y + w, z), 0 - select(x, w, z - y), "sub63") ||
             rewrite(y - select(x, w + y, z), 0 - select(x, w, z - y), "sub64") ||
             rewrite(z - select(x, y, z + w), 0 - select(x, y - z, w), "sub65") ||
             rewrite(z - select(x, y, w + z), 0 - select(x, y - z, w), "sub66") ||

             rewrite((x + y) - x, y, "sub68") ||
             rewrite((x + y) - y, x, "sub69") ||
             rewrite(x - (x + y), -y, "sub70") ||
             rewrite(y - (x + y), -x, "sub71") ||
             rewrite((x - y) - x, -y, "sub72") ||
             rewrite((select(x, y, z) + w) - select(x, u, v), select(x, y - u, z - v) + w, "sub73") ||
             rewrite((w + select(x, y, z)) - select(x, u, v), select(x, y - u, z - v) + w, "sub74") ||
             rewrite(select(x, y, z) - (select(x, u, v) + w), select(x, y - u, z - v) - w, "sub75") ||
             rewrite(select(x, y, z) - (w + select(x, u, v)), select(x, y - u, z - v) - w, "sub76") ||
             rewrite((select(x, y, z) - w) - select(x, u, v), select(x, y - u, z - v) - w, "sub77") ||
             rewrite(c0 - select(x, c1, c2), select(x, fold(c0 - c1), fold(c0 - c2)), "sub78") ||
             rewrite((x + c0) - c1, x + fold(c0 - c1), "sub79") ||
             rewrite((x + c0) - (c1 - y), (x + y) + fold(c0 - c1), "sub80") ||
             rewrite((x + c0) - (y + c1), (x - y) + fold(c0 - c1), "sub81") ||
             rewrite((x + c0) - y, (x - y) + c0, "sub82") ||
             rewrite((c0 - x) - (c1 - y), (y - x) + fold(c0 - c1), "sub83") ||
             rewrite((c0 - x) - (y + c1), fold(c0 - c1) - (x + y), "sub84") ||
             rewrite(x - (y - z), x + (z - y), "sub85") ||
             rewrite(x - y*c0, x + y*fold(-c0), c0 < 0 && -c0 > 0, "sub86") ||
             rewrite(x - (y + c0), (x - y) - c0, "sub87") ||
             rewrite((c0 - x) - c1, fold(c0 - c1) - x, "sub88") ||
             rewrite(x*y - z*y, (x - z)*y, "sub89") ||
             rewrite(x*y - y*z, (x - z)*y, "sub90") ||
             rewrite(y*x - z*y, y*(x - z), "sub91") ||
             rewrite(y*x - y*z, y*(x - z), "sub92") ||
             rewrite((x + y) - (x + z), y - z, "sub93") ||
             rewrite((x + y) - (z + x), y - z, "sub94") ||
             rewrite((y + x) - (x + z), y - z, "sub95") ||
             rewrite((y + x) - (z + x), y - z, "sub96") ||
             rewrite(((x + y) + z) - x, y + z, "sub97") ||
             rewrite(((y + x) + z) - x, y + z, "sub98") ||
             rewrite((z + (x + y)) - x, z + y, "sub99") ||
             rewrite((z + (y + x)) - x, z + y, "sub100") ||

             rewrite((x - y) - (x + z), 0 - y - z, "sub102") ||
             rewrite((x - y) - (z + x), 0 - y - z, "sub103") ||

             (no_overflow(op->type) &&
              (rewrite(max(x, y) - x, max(0, y - x), "sub106") ||
               rewrite(min(x, y) - x, min(0, y - x), "sub107") ||
               rewrite(max(x, y) - y, max(x - y, 0), "sub108") ||
               rewrite(min(x, y) - y, min(x - y, 0), "sub109") ||
               rewrite(x - max(x, y), min(0, x - y), !is_const(x), "sub110") ||
               rewrite(x - min(x, y), max(0, x - y), !is_const(x), "sub111") ||
               rewrite(y - max(x, y), min(y - x, 0), !is_const(y), "sub112") ||
               rewrite(y - min(x, y), max(y - x, 0), !is_const(y), "sub113") ||
               rewrite(x*y - x, x*(y - 1), "sub114") ||
               rewrite(x*y - y, (x - 1)*y, "sub115") ||
               rewrite(x - x*y, x*(1 - y), "sub116") ||
               rewrite(x - y*x, (1 - y)*x, "sub117") ||
               rewrite(x - min(x + y, z), max(-y, x - z), "sub118") ||
               rewrite(x - min(y + x, z), max(-y, x - z), "sub119") ||
               rewrite(x - min(z, x + y), max(x - z, -y), "sub120") ||
               rewrite(x - min(z, y + x), max(x - z, -y), "sub121") ||
               rewrite(min(x + y, z) - x, min(y, z - x), "sub122") ||
               rewrite(min(y + x, z) - x, min(y, z - x), "sub123") ||
               rewrite(min(z, x + y) - x, min(z - x, y), "sub124") ||
               rewrite(min(z, y + x) - x, min(z - x, y), "sub125") ||
               rewrite(min(x, y) - min(y, x), 0, "sub126") ||
               rewrite(min(x, y) - min(z, w), y - w, can_prove(x - y == z - w, this), "sub127") ||
               rewrite(min(x, y) - min(w, z), y - w, can_prove(x - y == z - w, this), "sub128") ||

               rewrite(x - max(x + y, z), min(-y, x - z), "sub130") ||
               rewrite(x - max(y + x, z), min(-y, x - z), "sub131") ||
               rewrite(x - max(z, x + y), min(x - z, -y), "sub132") ||
               rewrite(x - max(z, y + x), min(x - z, -y), "sub133") ||
               rewrite(max(x + y, z) - x, max(y, z - x), "sub134") ||
               rewrite(max(y + x, z) - x, max(y, z - x), "sub135") ||
               rewrite(max(z, x + y) - x, max(z - x, y), "sub136") ||
               rewrite(max(z, y + x) - x, max(z - x, y), "sub137") ||
               rewrite(max(x, y) - max(y, x), 0, "sub138") ||
               rewrite(max(x, y) - max(z, w), y - w, can_prove(x - y == z - w, this), "sub139") ||
               rewrite(max(x, y) - max(w, z), y - w, can_prove(x - y == z - w, this), "sub140") ||

               // When you have min(x, y) - min(z, w) and no further
               // information, there are four possible ways for the
               // mins to resolve. However if you can prove that the
               // decisions are correlated (i.e. x < y implies z < w or
               // vice versa), then there are simplifications to be
               // made that tame x. Whether or not these
               // simplifications are profitable depends on what terms
               // end up being constant.

               // If x < y implies z < w:
               //   min(x, y) - min(z, w)
               // = min(x - min(z, w), y - min(z, w))   using the distributive properties of min/max
               // = min(x - z, y - min(z, w))           using the implication
               // This duplicates z, so it's good if x - z causes some cancellation (e.g. they are equal)

               // If, on the other hand, z < w implies x < y:
               //   min(x, y) - min(z, w)
               // = max(min(x, y) - z, min(x, y) - w)   using the distributive properties of min/max
               // = max(x - z, min(x, y) - w)           using the implication
               // Again, this is profitable when x - z causes some cancellation

               // What follows are special cases of this general
               // transformation where it is easy to see that x - z
               // cancels and that there is an implication in one
               // direction or the other.

               // Then the actual rules. We consider only cases where x and z differ by a constant.
               rewrite(min(x, y) - min(x, w), min(0, y - min(x, w)), can_prove(y <= w, this), "sub169") ||
               rewrite(min(x, y) - min(x, w), max(0, min(x, y) - w), can_prove(y >= w, this), "sub170") ||
               rewrite(min(x + c0, y) - min(x, w), min(c0, y - min(x, w)), can_prove(y <= w + c0, this), "sub171") ||
               rewrite(min(x + c0, y) - min(x, w), max(c0, min(x + c0, y) - w), can_prove(y >= w + c0, this), "sub172") ||
               rewrite(min(x, y) - min(x + c1, w), min(fold(-c1), y - min(x + c1, w)), can_prove(y + c1 <= w, this), "sub173") ||
               rewrite(min(x, y) - min(x + c1, w), max(fold(-c1), min(x, y) - w), can_prove(y + c1 >= w, this), "sub174") ||
               rewrite(min(x + c0, y) - min(x + c1, w), min(fold(c0 - c1), y - min(x + c1, w)), can_prove(y + c1 <= w + c0, this), "sub175") ||
               rewrite(min(x + c0, y) - min(x + c1, w), max(fold(c0 - c1), min(x + c0, y) - w), can_prove(y + c1 >= w + c0, this), "sub176") ||

               rewrite(min(y, x) - min(w, x), min(0, y - min(x, w)), can_prove(y <= w, this), "sub178") ||
               rewrite(min(y, x) - min(w, x), max(0, min(x, y) - w), can_prove(y >= w, this), "sub179") ||
               rewrite(min(y, x + c0) - min(w, x), min(c0, y - min(x, w)), can_prove(y <= w + c0, this), "sub180") ||
               rewrite(min(y, x + c0) - min(w, x), max(c0, min(x + c0, y) - w), can_prove(y >= w + c0, this), "sub181") ||
               rewrite(min(y, x) - min(w, x + c1), min(fold(-c1), y - min(x + c1, w)), can_prove(y + c1 <= w, this), "sub182") ||
               rewrite(min(y, x) - min(w, x + c1), max(fold(-c1), min(x, y) - w), can_prove(y + c1 >= w, this), "sub183") ||
               rewrite(min(y, x + c0) - min(w, x + c1), min(fold(c0 - c1), y - min(x + c1, w)), can_prove(y + c1 <= w + c0, this), "sub184") ||
               rewrite(min(y, x + c0) - min(w, x + c1), max(fold(c0 - c1), min(x + c0, y) - w), can_prove(y + c1 >= w + c0, this), "sub185") ||

               rewrite(min(x, y) - min(w, x), min(0, y - min(x, w)), can_prove(y <= w, this), "sub187") ||
               rewrite(min(x, y) - min(w, x), max(0, min(x, y) - w), can_prove(y >= w, this), "sub188") ||
               rewrite(min(x + c0, y) - min(w, x), min(c0, y - min(x, w)), can_prove(y <= w + c0, this), "sub189") ||
               rewrite(min(x + c0, y) - min(w, x), max(c0, min(x + c0, y) - w), can_prove(y >= w + c0, this), "sub190") ||
               rewrite(min(x, y) - min(w, x + c1), min(fold(-c1), y - min(x + c1, w)), can_prove(y + c1 <= w, this), "sub191") ||
               rewrite(min(x, y) - min(w, x + c1), max(fold(-c1), min(x, y) - w), can_prove(y + c1 >= w, this), "sub192") ||
               rewrite(min(x + c0, y) - min(w, x + c1), min(fold(c0 - c1), y - min(x + c1, w)), can_prove(y + c1 <= w + c0, this), "sub193") ||
               rewrite(min(x + c0, y) - min(w, x + c1), max(fold(c0 - c1), min(x + c0, y) - w), can_prove(y + c1 >= w + c0, this), "sub194") ||

               rewrite(min(y, x) - min(x, w), min(0, y - min(x, w)), can_prove(y <= w, this), "sub196") ||
               rewrite(min(y, x) - min(x, w), max(0, min(x, y) - w), can_prove(y >= w, this), "sub197") ||
               rewrite(min(y, x + c0) - min(x, w), min(c0, y - min(x, w)), can_prove(y <= w + c0, this), "sub198") ||
               rewrite(min(y, x + c0) - min(x, w), max(c0, min(x + c0, y) - w), can_prove(y >= w + c0, this), "sub199") ||
               rewrite(min(y, x) - min(x + c1, w), min(fold(-c1), y - min(x + c1, w)), can_prove(y + c1 <= w, this), "sub200") ||
               rewrite(min(y, x) - min(x + c1, w), max(fold(-c1), min(x, y) - w), can_prove(y + c1 >= w, this), "sub201") ||
               rewrite(min(y, x + c0) - min(x + c1, w), min(fold(c0 - c1), y - min(x + c1, w)), can_prove(y + c1 <= w + c0, this), "sub202") ||
               rewrite(min(y, x + c0) - min(x + c1, w), max(fold(c0 - c1), min(x + c0, y) - w), can_prove(y + c1 >= w + c0, this), "sub203") ||

               // The equivalent rules for max are what you'd
               // expect. Just swap < and > and min and max (apply the
               // isomorphism x -> -x).
               rewrite(max(x, y) - max(x, w), max(0, y - max(x, w)), can_prove(y >= w, this), "sub208") ||
               rewrite(max(x, y) - max(x, w), min(0, max(x, y) - w), can_prove(y <= w, this), "sub209") ||
               rewrite(max(x + c0, y) - max(x, w), max(c0, y - max(x, w)), can_prove(y >= w + c0, this), "sub210") ||
               rewrite(max(x + c0, y) - max(x, w), min(c0, max(x + c0, y) - w), can_prove(y <= w + c0, this), "sub211") ||
               rewrite(max(x, y) - max(x + c1, w), max(fold(-c1), y - max(x + c1, w)), can_prove(y + c1 >= w, this), "sub212") ||
               rewrite(max(x, y) - max(x + c1, w), min(fold(-c1), max(x, y) - w), can_prove(y + c1 <= w, this), "sub213") ||
               rewrite(max(x + c0, y) - max(x + c1, w), max(fold(c0 - c1), y - max(x + c1, w)), can_prove(y + c1 >= w + c0, this), "sub214") ||
               rewrite(max(x + c0, y) - max(x + c1, w), min(fold(c0 - c1), max(x + c0, y) - w), can_prove(y + c1 <= w + c0, this), "sub215") ||

               rewrite(max(y, x) - max(w, x), max(0, y - max(x, w)), can_prove(y >= w, this), "sub217") ||
               rewrite(max(y, x) - max(w, x), min(0, max(x, y) - w), can_prove(y <= w, this), "sub218") ||
               rewrite(max(y, x + c0) - max(w, x), max(c0, y - max(x, w)), can_prove(y >= w + c0, this), "sub219") ||
               rewrite(max(y, x + c0) - max(w, x), min(c0, max(x + c0, y) - w), can_prove(y <= w + c0, this), "sub220") ||
               rewrite(max(y, x) - max(w, x + c1), max(fold(-c1), y - max(x + c1, w)), can_prove(y + c1 >= w, this), "sub221") ||
               rewrite(max(y, x) - max(w, x + c1), min(fold(-c1), max(x, y) - w), can_prove(y + c1 <= w, this), "sub222") ||
               rewrite(max(y, x + c0) - max(w, x + c1), max(fold(c0 - c1), y - max(x + c1, w)), can_prove(y + c1 >= w + c0, this), "sub223") ||
               rewrite(max(y, x + c0) - max(w, x + c1), min(fold(c0 - c1), max(x + c0, y) - w), can_prove(y + c1 <= w + c0, this), "sub224") ||

               rewrite(max(x, y) - max(w, x), max(0, y - max(x, w)), can_prove(y >= w, this), "sub226") ||
               rewrite(max(x, y) - max(w, x), min(0, max(x, y) - w), can_prove(y <= w, this), "sub227") ||
               rewrite(max(x + c0, y) - max(w, x), max(c0, y - max(x, w)), can_prove(y >= w + c0, this), "sub228") ||
               rewrite(max(x + c0, y) - max(w, x), min(c0, max(x + c0, y) - w), can_prove(y <= w + c0, this), "sub229") ||
               rewrite(max(x, y) - max(w, x + c1), max(fold(-c1), y - max(x + c1, w)), can_prove(y + c1 >= w, this), "sub230") ||
               rewrite(max(x, y) - max(w, x + c1), min(fold(-c1), max(x, y) - w), can_prove(y + c1 <= w, this), "sub231") ||
               rewrite(max(x + c0, y) - max(w, x + c1), max(fold(c0 - c1), y - max(x + c1, w)), can_prove(y + c1 >= w + c0, this), "sub232") ||
               rewrite(max(x + c0, y) - max(w, x + c1), min(fold(c0 - c1), max(x + c0, y) - w), can_prove(y + c1 <= w + c0, this), "sub233") ||

               rewrite(max(y, x) - max(x, w), max(0, y - max(x, w)), can_prove(y >= w, this), "sub235") ||
               rewrite(max(y, x) - max(x, w), min(0, max(x, y) - w), can_prove(y <= w, this), "sub236") ||
               rewrite(max(y, x + c0) - max(x, w), max(c0, y - max(x, w)), can_prove(y >= w + c0, this), "sub237") ||
               rewrite(max(y, x + c0) - max(x, w), min(c0, max(x + c0, y) - w), can_prove(y <= w + c0, this), "sub238") ||
               rewrite(max(y, x) - max(x + c1, w), max(fold(-c1), y - max(x + c1, w)), can_prove(y + c1 >= w, this), "sub239") ||
               rewrite(max(y, x) - max(x + c1, w), min(fold(-c1), max(x, y) - w), can_prove(y + c1 <= w, this), "sub240") ||
               rewrite(max(y, x + c0) - max(x + c1, w), max(fold(c0 - c1), y - max(x + c1, w)), can_prove(y + c1 >= w + c0, this), "sub241") ||
               rewrite(max(y, x + c0) - max(x + c1, w), min(fold(c0 - c1), max(x + c0, y) - w), can_prove(y + c1 <= w + c0, this), "sub242"))) ||

             (no_overflow_int(op->type) &&
              (rewrite(c0 - (c1 - x)/c2, (fold(c0*c2 - c1 + c2 - 1) + x)/c2, c2 > 0, "sub245") ||
               rewrite(c0 - (x + c1)/c2, (fold(c0*c2 - c1 + c2 - 1) - x)/c2, c2 > 0, "sub246") ||
               rewrite(x - (x + y)/c0, (x*fold(c0 - 1) - y + fold(c0 - 1))/c0, c0 > 0, "sub247") ||
               rewrite(x - (x - y)/c0, (x*fold(c0 - 1) + y + fold(c0 - 1))/c0, c0 > 0, "sub248") ||
               rewrite(x - (y + x)/c0, (x*fold(c0 - 1) - y + fold(c0 - 1))/c0, c0 > 0, "sub249") ||
               rewrite(x - (y - x)/c0, (x*fold(c0 + 1) - y + fold(c0 - 1))/c0, c0 > 0, "sub250") ||
               rewrite((x + y)/c0 - x, (x*fold(1 - c0) + y)/c0, "sub251") ||
               rewrite((y + x)/c0 - x, (y + x*fold(1 - c0))/c0, "sub252") ||
               rewrite((x - y)/c0 - x, (x*fold(1 - c0) - y)/c0, "sub253") ||
               rewrite((y - x)/c0 - x, (y - x*fold(1 + c0))/c0, "sub254") ||

               rewrite((x/c0)*c0 - x, -(x % c0), c0 > 0, "sub256") ||
               rewrite(x - (x/c0)*c0, x % c0, c0 > 0, "sub257") ||
               rewrite(((x + c0)/c1)*c1 - x, (-x) % c1, c1 > 0 && c0 + 1 == c1, "sub258") ||
               rewrite(x - ((x + c0)/c1)*c1, ((x + c0) % c1) + fold(-c0), c1 > 0 && c0 + 1 == c1, "sub259") ||
               rewrite(x * c0 - y * c1, (x * fold(c0 / c1) - y) * c1, c0 % c1 == 0, "sub260") ||
               rewrite(x * c0 - y * c1, (x - y * fold(c1 / c0)) * c0, c1 % c0 == 0, "sub261") ||
               // Various forms of (x +/- a)/c - (x +/- b)/c. We can
               // *almost* cancel the x.  The right thing to do depends
               // on which of a or b is a constant, and we also need to
               // catch the cases where that constant is zero.
               rewrite(((x + y) + z)/c0 - ((y + x) + w)/c0, ((x + y) + z)/c0 - ((x + y) + w)/c0, c0 > 0, "sub266") ||
               rewrite((x + y)/c0 - (y + x)/c0, 0, c0 != 0, "sub267") ||
               rewrite((x + y)/c0 - (x + c1)/c0, (((x + fold(c1 % c0)) % c0) + (y - c1))/c0, c0 > 0, "sub268") ||
               rewrite((x + c1)/c0 - (x + y)/c0, ((fold(c0 + c1 - 1) - y) - ((x + fold(c1 % c0)) % c0))/c0, c0 > 0, "sub269") ||
               rewrite((x - y)/c0 - (x + c1)/c0, (((x + fold(c1 % c0)) % c0) - y - c1)/c0, c0 > 0, "sub270") ||
               rewrite((x + c1)/c0 - (x - y)/c0, ((y + fold(c0 + c1 - 1)) - ((x + fold(c1 % c0)) % c0))/c0, c0 > 0, "sub271") ||
               rewrite(x/c0 - (x + y)/c0, ((fold(c0 - 1) - y) - (x % c0))/c0, c0 > 0, "sub272") ||
               rewrite((x + y)/c0 - x/c0, ((x % c0) + y)/c0, c0 > 0, "sub273") ||
               rewrite(x/c0 - (x - y)/c0, ((y + fold(c0 - 1)) - (x % c0))/c0, c0 > 0, "sub274") ||
               rewrite((x - y)/c0 - x/c0, ((x % c0) - y)/c0, c0 > 0, "sub275"))))) {
            return mutate(std::move(rewrite.result), bounds);
        }
    }
    // clang-format on

    const Shuffle *shuffle_a = a.as<Shuffle>();
    const Shuffle *shuffle_b = b.as<Shuffle>();
    if (shuffle_a && shuffle_b &&
        shuffle_a->is_slice() &&
        shuffle_b->is_slice()) {
        if (a.same_as(op->a) && b.same_as(op->b)) {
            return hoist_slice_vector<Sub>(op);
        } else {
            return hoist_slice_vector<Sub>(Sub::make(a, b));
        }
    }

    if (a.same_as(op->a) && b.same_as(op->b)) {
        return op;
    } else {
        return Sub::make(a, b);
    }
}

}  // namespace Internal
}  // namespace Halide
