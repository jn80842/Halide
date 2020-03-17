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

        if ((get_rule_flag("sub38", rflag) && rewrite(c0 - c1, fold(c0 - c1), "sub38")) ||
            (get_rule_flag("sub39", rflag) && rewrite(IRMatcher::Overflow() - x, IRMatcher::Overflow(), "sub39")) ||
            (get_rule_flag("sub40", rflag) && rewrite(x - IRMatcher::Overflow(), IRMatcher::Overflow(), "sub40")) ||
            (get_rule_flag("sub41", rflag) && rewrite(x - 0, x, "sub41"))) {
            return rewrite.result;
        }

        // clang-format off
        if (EVAL_IN_LAMBDA
            ((!op->type.is_uint() && (get_rule_flag("sub47", rflag) && rewrite(x - c0, x + fold(-c0), !overflows(-c0), "sub47"))) ||
             (get_rule_flag("sub48", rflag) && rewrite(x - x, 0, "sub48") || // We want to remutate this just to get better bounds
             (get_rule_flag("sub49", rflag) && rewrite(ramp(x, y) - ramp(z, w), ramp(x - z, y - w, lanes), "sub49")) ||
             (get_rule_flag("sub50", rflag) && rewrite(ramp(x, y) - broadcast(z), ramp(x - z, y, lanes), "sub50")) ||
             (get_rule_flag("sub51", rflag) && rewrite(broadcast(x) - ramp(z, w), ramp(x - z, -w, lanes), "sub51")) ||
             (get_rule_flag("sub52", rflag) && rewrite(broadcast(x) - broadcast(y), broadcast(x - y, lanes), "sub52")) ||
             (get_rule_flag("sub53", rflag) && rewrite(select(x, y, z) - select(x, w, u), select(x, y - w, z - u), "sub53")) ||
             (get_rule_flag("sub54", rflag) && rewrite(select(x, y, z) - y, select(x, 0, z - y), "sub54")) ||
             (get_rule_flag("sub55", rflag) && rewrite(select(x, y, z) - z, select(x, y - z, 0), "sub55")) ||
             (get_rule_flag("sub56", rflag) && rewrite(y - select(x, y, z), select(x, 0, y - z), "sub56")) ||
             (get_rule_flag("sub57", rflag) && rewrite(z - select(x, y, z), select(x, z - y, 0), "sub57")) ||

             (get_rule_flag("sub59", rflag) && rewrite(select(x, y + w, z) - y, select(x, w, z - y), "sub59")) ||
             (get_rule_flag("sub60", rflag) && rewrite(select(x, w + y, z) - y, select(x, w, z - y), "sub60")) ||
             (get_rule_flag("sub61", rflag) && rewrite(select(x, y, z + w) - z, select(x, y - z, w), "sub61")) ||
             (get_rule_flag("sub62", rflag) && rewrite(select(x, y, w + z) - z, select(x, y - z, w), "sub62")) ||
             (get_rule_flag("sub63", rflag) && rewrite(y - select(x, y + w, z), 0 - select(x, w, z - y), "sub63")) ||
             (get_rule_flag("sub64", rflag) && rewrite(y - select(x, w + y, z), 0 - select(x, w, z - y), "sub64")) ||
             (get_rule_flag("sub65", rflag) && rewrite(z - select(x, y, z + w), 0 - select(x, y - z, w), "sub65")) ||
             (get_rule_flag("sub66", rflag) && rewrite(z - select(x, y, w + z), 0 - select(x, y - z, w), "sub66")) ||

             (get_rule_flag("sub68", rflag) && rewrite((x + y) - x, y, "sub68")) ||
             (get_rule_flag("sub69", rflag) && rewrite((x + y) - y, x, "sub69")) ||
             (get_rule_flag("sub70", rflag) && rewrite(x - (x + y), -y, "sub70")) ||
             (get_rule_flag("sub71", rflag) && rewrite(y - (x + y), -x, "sub71")) ||
             (get_rule_flag("sub72", rflag) && rewrite((x - y) - x, -y, "sub72")) ||
             (get_rule_flag("sub73", rflag) && rewrite((select(x, y, z) + w) - select(x, u, v), select(x, y - u, z - v) + w, "sub73")) ||
             (get_rule_flag("sub74", rflag) && rewrite((w + select(x, y, z)) - select(x, u, v), select(x, y - u, z - v) + w, "sub74")) ||
             (get_rule_flag("sub75", rflag) && rewrite(select(x, y, z) - (select(x, u, v) + w), select(x, y - u, z - v) - w, "sub75")) ||
             (get_rule_flag("sub76", rflag) && rewrite(select(x, y, z) - (w + select(x, u, v)), select(x, y - u, z - v) - w, "sub76")) ||
             (get_rule_flag("sub77", rflag) && rewrite((select(x, y, z) - w) - select(x, u, v), select(x, y - u, z - v) - w, "sub77")) ||
             (get_rule_flag("sub78", rflag) && rewrite(c0 - select(x, c1, c2), select(x, fold(c0 - c1), fold(c0 - c2)), "sub78")) ||
             (get_rule_flag("sub79", rflag) && rewrite((x + c0) - c1, x + fold(c0 - c1), "sub79")) ||
             (get_rule_flag("sub80", rflag) && rewrite((x + c0) - (c1 - y), (x + y) + fold(c0 - c1), "sub80")) ||
             (get_rule_flag("sub81", rflag) && rewrite((x + c0) - (y + c1), (x - y) + fold(c0 - c1), "sub81")) ||
             (get_rule_flag("sub82", rflag) && rewrite((x + c0) - y, (x - y) + c0, "sub82")) ||
             (get_rule_flag("sub83", rflag) && rewrite((c0 - x) - (c1 - y), (y - x) + fold(c0 - c1), "sub83")) ||
             (get_rule_flag("sub84", rflag) && rewrite((c0 - x) - (y + c1), fold(c0 - c1) - (x + y), "sub84")) ||
             (get_rule_flag("sub85", rflag) && rewrite(x - (y - z), x + (z - y), "sub85")) ||
             (get_rule_flag("sub86", rflag) && rewrite(x - y*c0, x + y*fold(-c0), c0 < 0 && -c0 > 0, "sub86")) ||
             (get_rule_flag("sub87", rflag) && rewrite(x - (y + c0), (x - y) - c0, "sub87")) ||
             (get_rule_flag("sub88", rflag) && rewrite((c0 - x) - c1, fold(c0 - c1) - x, "sub88")) ||
             (get_rule_flag("sub89", rflag) && rewrite(x*y - z*y, (x - z)*y, "sub89")) ||
             (get_rule_flag("sub90", rflag) && rewrite(x*y - y*z, (x - z)*y, "sub90")) ||
             (get_rule_flag("sub91", rflag) && rewrite(y*x - z*y, y*(x - z), "sub91")) ||
             (get_rule_flag("sub92", rflag) && rewrite(y*x - y*z, y*(x - z), "sub92")) ||
             (get_rule_flag("sub93", rflag) && rewrite((x + y) - (x + z), y - z, "sub93")) ||
             (get_rule_flag("sub94", rflag) && rewrite((x + y) - (z + x), y - z, "sub94")) ||
             (get_rule_flag("sub95", rflag) && rewrite((y + x) - (x + z), y - z, "sub95")) ||
             (get_rule_flag("sub96", rflag) && rewrite((y + x) - (z + x), y - z, "sub96")) ||
             (get_rule_flag("sub97", rflag) && rewrite(((x + y) + z) - x, y + z, "sub97")) ||
             (get_rule_flag("sub98", rflag) && rewrite(((y + x) + z) - x, y + z, "sub98")) ||
             (get_rule_flag("sub99", rflag) && rewrite((z + (x + y)) - x, z + y, "sub99")) ||
             (get_rule_flag("sub100", rflag) && rewrite((z + (y + x)) - x, z + y, "sub100")) ||

             (get_rule_flag("sub102", rflag) && rewrite((x - y) - (x + z), 0 - y - z, "sub102")) ||
             (get_rule_flag("sub102", rflag) && rewrite((x - y) - (z + x), 0 - y - z, "sub103")) ||

             (no_overflow(op->type) &&
              ((get_rule_flag("sub106", rflag) && rewrite(max(x, y) - x, max(0, y - x), "sub106")) ||
               (get_rule_flag("sub107", rflag) && rewrite(min(x, y) - x, min(0, y - x), "sub107")) ||
               (get_rule_flag("sub108", rflag) && rewrite(max(x, y) - y, max(x - y, 0), "sub108")) ||
               (get_rule_flag("sub109", rflag) && rewrite(min(x, y) - y, min(x - y, 0), "sub109")) ||
               (get_rule_flag("sub110", rflag) && rewrite(x - max(x, y), min(0, x - y), !is_const(x), "sub110")) ||
               (get_rule_flag("sub111", rflag) && rewrite(x - min(x, y), max(0, x - y), !is_const(x), "sub111")) ||
               (get_rule_flag("sub112", rflag) && rewrite(y - max(x, y), min(y - x, 0), !is_const(y), "sub112")) ||
               (get_rule_flag("sub113", rflag) && rewrite(y - min(x, y), max(y - x, 0), !is_const(y), "sub113")) ||
               (get_rule_flag("sub114", rflag) && rewrite(x*y - x, x*(y - 1), "sub114")) ||
               (get_rule_flag("sub115", rflag) && rewrite(x*y - y, (x - 1)*y, "sub115")) ||
               (get_rule_flag("sub116", rflag) && rewrite(x - x*y, x*(1 - y), "sub116")) ||
               (get_rule_flag("sub117", rflag) && rewrite(x - y*x, (1 - y)*x, "sub117")) ||
               (get_rule_flag("sub118", rflag) && rewrite(x - min(x + y, z), max(-y, x - z), "sub118")) ||
               (get_rule_flag("sub119", rflag) && rewrite(x - min(y + x, z), max(-y, x - z), "sub119")) ||
               (get_rule_flag("sub120", rflag) && rewrite(x - min(z, x + y), max(x - z, -y), "sub120")) ||
               (get_rule_flag("sub121", rflag) && rewrite(x - min(z, y + x), max(x - z, -y), "sub121")) ||
               (get_rule_flag("sub122", rflag) && rewrite(min(x + y, z) - x, min(y, z - x), "sub122")) ||
               (get_rule_flag("sub123", rflag) && rewrite(min(y + x, z) - x, min(y, z - x), "sub123")) ||
               (get_rule_flag("sub124", rflag) && rewrite(min(z, x + y) - x, min(z - x, y), "sub124")) ||
               (get_rule_flag("sub125", rflag) && rewrite(min(z, y + x) - x, min(z - x, y), "sub125")) ||
               (get_rule_flag("sub126", rflag) && rewrite(min(x, y) - min(y, x), 0, "sub126")) ||
               (get_rule_flag("sub127", rflag) && rewrite(min(x, y) - min(z, w), y - w, can_prove(x - y == z - w, this), "sub127")) ||
               (get_rule_flag("sub128", rflag) && rewrite(min(x, y) - min(w, z), y - w, can_prove(x - y == z - w, this), "sub128")) ||

               (get_rule_flag("sub130", rflag) && rewrite(x - max(x + y, z), min(-y, x - z), "sub130")) ||
               (get_rule_flag("sub131", rflag) && rewrite(x - max(y + x, z), min(-y, x - z), "sub131")) ||
               (get_rule_flag("sub132", rflag) && rewrite(x - max(z, x + y), min(x - z, -y), "sub132")) ||
               (get_rule_flag("sub133", rflag) && rewrite(x - max(z, y + x), min(x - z, -y), "sub133")) ||
               (get_rule_flag("sub134", rflag) && rewrite(max(x + y, z) - x, max(y, z - x), "sub134")) ||
               (get_rule_flag("sub135", rflag) && rewrite(max(y + x, z) - x, max(y, z - x), "sub135")) ||
               (get_rule_flag("sub136", rflag) && rewrite(max(z, x + y) - x, max(z - x, y), "sub136")) ||
               (get_rule_flag("sub137", rflag) && rewrite(max(z, y + x) - x, max(z - x, y), "sub137")) ||
               (get_rule_flag("sub138", rflag) && rewrite(max(x, y) - max(y, x), 0, "sub138")) ||
               (get_rule_flag("sub139", rflag) && rewrite(max(x, y) - max(z, w), y - w, can_prove(x - y == z - w, this), "sub139")) ||
               (get_rule_flag("sub140", rflag) && rewrite(max(x, y) - max(w, z), y - w, can_prove(x - y == z - w, this), "sub140")) ||

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
               (get_rule_flag("sub169", rflag) && rewrite(min(x, y) - min(x, w), min(0, y - min(x, w)), can_prove(y <= w, this), "sub169")) ||
               (get_rule_flag("sub170", rflag) && rewrite(min(x, y) - min(x, w), max(0, min(x, y) - w), can_prove(y >= w, this), "sub170")) ||
               (get_rule_flag("sub171", rflag) && rewrite(min(x + c0, y) - min(x, w), min(c0, y - min(x, w)), can_prove(y <= w + c0, this), "sub171")) ||
               (get_rule_flag("sub172", rflag) && rewrite(min(x + c0, y) - min(x, w), max(c0, min(x + c0, y) - w), can_prove(y >= w + c0, this), "sub172")) ||
               (get_rule_flag("sub173", rflag) && rewrite(min(x, y) - min(x + c1, w), min(fold(-c1), y - min(x + c1, w)), can_prove(y + c1 <= w, this), "sub173")) ||
               (get_rule_flag("sub174", rflag) && rewrite(min(x, y) - min(x + c1, w), max(fold(-c1), min(x, y) - w), can_prove(y + c1 >= w, this), "sub174")) ||
               (get_rule_flag("sub175", rflag) && rewrite(min(x + c0, y) - min(x + c1, w), min(fold(c0 - c1), y - min(x + c1, w)), can_prove(y + c1 <= w + c0, this), "sub175")) ||
               (get_rule_flag("sub176", rflag) && rewrite(min(x + c0, y) - min(x + c1, w), max(fold(c0 - c1), min(x + c0, y) - w), can_prove(y + c1 >= w + c0, this), "sub176")) ||

               (get_rule_flag("sub178", rflag) && rewrite(min(y, x) - min(w, x), min(0, y - min(x, w)), can_prove(y <= w, this), "sub178")) ||
               (get_rule_flag("sub179", rflag) && rewrite(min(y, x) - min(w, x), max(0, min(x, y) - w), can_prove(y >= w, this), "sub179")) ||
               (get_rule_flag("sub180", rflag) && rewrite(min(y, x + c0) - min(w, x), min(c0, y - min(x, w)), can_prove(y <= w + c0, this), "sub180")) ||
               (get_rule_flag("sub181", rflag) && rewrite(min(y, x + c0) - min(w, x), max(c0, min(x + c0, y) - w), can_prove(y >= w + c0, this), "sub181")) ||
               (get_rule_flag("sub182", rflag) && rewrite(min(y, x) - min(w, x + c1), min(fold(-c1), y - min(x + c1, w)), can_prove(y + c1 <= w, this), "sub182")) ||
               (get_rule_flag("sub183", rflag) && rewrite(min(y, x) - min(w, x + c1), max(fold(-c1), min(x, y) - w), can_prove(y + c1 >= w, this), "sub183")) ||
               (get_rule_flag("sub184", rflag) && rewrite(min(y, x + c0) - min(w, x + c1), min(fold(c0 - c1), y - min(x + c1, w)), can_prove(y + c1 <= w + c0, this), "sub184")) ||
               (get_rule_flag("sub185", rflag) && rewrite(min(y, x + c0) - min(w, x + c1), max(fold(c0 - c1), min(x + c0, y) - w), can_prove(y + c1 >= w + c0, this), "sub185")) ||

               (get_rule_flag("sub187", rflag) && rewrite(min(x, y) - min(w, x), min(0, y - min(x, w)), can_prove(y <= w, this), "sub187")) ||
               (get_rule_flag("sub188", rflag) && rewrite(min(x, y) - min(w, x), max(0, min(x, y) - w), can_prove(y >= w, this), "sub188")) ||
               (get_rule_flag("sub189", rflag) && rewrite(min(x + c0, y) - min(w, x), min(c0, y - min(x, w)), can_prove(y <= w + c0, this), "sub189")) ||
               (get_rule_flag("sub190", rflag) && rewrite(min(x + c0, y) - min(w, x), max(c0, min(x + c0, y) - w), can_prove(y >= w + c0, this), "sub190")) ||
               (get_rule_flag("sub191", rflag) && rewrite(min(x, y) - min(w, x + c1), min(fold(-c1), y - min(x + c1, w)), can_prove(y + c1 <= w, this), "sub191")) ||
               (get_rule_flag("sub192", rflag) && rewrite(min(x, y) - min(w, x + c1), max(fold(-c1), min(x, y) - w), can_prove(y + c1 >= w, this), "sub192")) ||
               (get_rule_flag("sub193", rflag) && rewrite(min(x + c0, y) - min(w, x + c1), min(fold(c0 - c1), y - min(x + c1, w)), can_prove(y + c1 <= w + c0, this), "sub193")) ||
               (get_rule_flag("sub194", rflag) && rewrite(min(x + c0, y) - min(w, x + c1), max(fold(c0 - c1), min(x + c0, y) - w), can_prove(y + c1 >= w + c0, this), "sub194")) ||

               (get_rule_flag("sub196", rflag) && rewrite(min(y, x) - min(x, w), min(0, y - min(x, w)), can_prove(y <= w, this), "sub196")) ||
               (get_rule_flag("sub197", rflag) && rewrite(min(y, x) - min(x, w), max(0, min(x, y) - w), can_prove(y >= w, this), "sub197")) ||
               (get_rule_flag("sub198", rflag) && rewrite(min(y, x + c0) - min(x, w), min(c0, y - min(x, w)), can_prove(y <= w + c0, this), "sub198")) ||
               (get_rule_flag("sub199", rflag) && rewrite(min(y, x + c0) - min(x, w), max(c0, min(x + c0, y) - w), can_prove(y >= w + c0, this), "sub199")) ||
               (get_rule_flag("sub200", rflag) && rewrite(min(y, x) - min(x + c1, w), min(fold(-c1), y - min(x + c1, w)), can_prove(y + c1 <= w, this), "sub200")) ||
               (get_rule_flag("sub201", rflag) && rewrite(min(y, x) - min(x + c1, w), max(fold(-c1), min(x, y) - w), can_prove(y + c1 >= w, this), "sub201")) ||
               (get_rule_flag("sub202", rflag) && rewrite(min(y, x + c0) - min(x + c1, w), min(fold(c0 - c1), y - min(x + c1, w)), can_prove(y + c1 <= w + c0, this), "sub202")) ||
               (get_rule_flag("sub203", rflag) && rewrite(min(y, x + c0) - min(x + c1, w), max(fold(c0 - c1), min(x + c0, y) - w), can_prove(y + c1 >= w + c0, this), "sub203")) ||

               // The equivalent rules for max are what you'd
               // expect. Just swap < and > and min and max (apply the
               // isomorphism x -> -x).
               (get_rule_flag("sub208", rflag) && rewrite(max(x, y) - max(x, w), max(0, y - max(x, w)), can_prove(y >= w, this), "sub208")) ||
               (get_rule_flag("sub209", rflag) && rewrite(max(x, y) - max(x, w), min(0, max(x, y) - w), can_prove(y <= w, this), "sub209")) ||
               (get_rule_flag("sub210", rflag) && rewrite(max(x + c0, y) - max(x, w), max(c0, y - max(x, w)), can_prove(y >= w + c0, this), "sub210")) ||
               (get_rule_flag("sub211", rflag) && rewrite(max(x + c0, y) - max(x, w), min(c0, max(x + c0, y) - w), can_prove(y <= w + c0, this), "sub211")) ||
               (get_rule_flag("sub212", rflag) && rewrite(max(x, y) - max(x + c1, w), max(fold(-c1), y - max(x + c1, w)), can_prove(y + c1 >= w, this), "sub212")) ||
               (get_rule_flag("sub213", rflag) && rewrite(max(x, y) - max(x + c1, w), min(fold(-c1), max(x, y) - w), can_prove(y + c1 <= w, this), "sub213")) ||
               (get_rule_flag("sub214", rflag) && rewrite(max(x + c0, y) - max(x + c1, w), max(fold(c0 - c1), y - max(x + c1, w)), can_prove(y + c1 >= w + c0, this), "sub214")) ||
               (get_rule_flag("sub215", rflag) && rewrite(max(x + c0, y) - max(x + c1, w), min(fold(c0 - c1), max(x + c0, y) - w), can_prove(y + c1 <= w + c0, this), "sub215")) ||

               (get_rule_flag("sub217", rflag) && rewrite(max(y, x) - max(w, x), max(0, y - max(x, w)), can_prove(y >= w, this), "sub217")) ||
               (get_rule_flag("sub218", rflag) && rewrite(max(y, x) - max(w, x), min(0, max(x, y) - w), can_prove(y <= w, this), "sub218")) ||
               (get_rule_flag("sub219", rflag) && rewrite(max(y, x + c0) - max(w, x), max(c0, y - max(x, w)), can_prove(y >= w + c0, this), "sub219")) ||
               (get_rule_flag("sub220", rflag) && rewrite(max(y, x + c0) - max(w, x), min(c0, max(x + c0, y) - w), can_prove(y <= w + c0, this), "sub220")) ||
               (get_rule_flag("sub221", rflag) && rewrite(max(y, x) - max(w, x + c1), max(fold(-c1), y - max(x + c1, w)), can_prove(y + c1 >= w, this), "sub221")) ||
               (get_rule_flag("sub222", rflag) && rewrite(max(y, x) - max(w, x + c1), min(fold(-c1), max(x, y) - w), can_prove(y + c1 <= w, this), "sub222")) ||
               (get_rule_flag("sub223", rflag) && rewrite(max(y, x + c0) - max(w, x + c1), max(fold(c0 - c1), y - max(x + c1, w)), can_prove(y + c1 >= w + c0, this), "sub223")) ||
               (get_rule_flag("sub224", rflag) && rewrite(max(y, x + c0) - max(w, x + c1), min(fold(c0 - c1), max(x + c0, y) - w), can_prove(y + c1 <= w + c0, this), "sub224")) ||

               (get_rule_flag("sub226", rflag) && rewrite(max(x, y) - max(w, x), max(0, y - max(x, w)), can_prove(y >= w, this), "sub226")) ||
               (get_rule_flag("sub227", rflag) && rewrite(max(x, y) - max(w, x), min(0, max(x, y) - w), can_prove(y <= w, this), "sub227")) ||
               (get_rule_flag("sub228", rflag) && rewrite(max(x + c0, y) - max(w, x), max(c0, y - max(x, w)), can_prove(y >= w + c0, this), "sub228")) ||
               (get_rule_flag("sub229", rflag) && rewrite(max(x + c0, y) - max(w, x), min(c0, max(x + c0, y) - w), can_prove(y <= w + c0, this), "sub229")) ||
               (get_rule_flag("sub230", rflag) && rewrite(max(x, y) - max(w, x + c1), max(fold(-c1), y - max(x + c1, w)), can_prove(y + c1 >= w, this), "sub230")) ||
               (get_rule_flag("sub231", rflag) && rewrite(max(x, y) - max(w, x + c1), min(fold(-c1), max(x, y) - w), can_prove(y + c1 <= w, this), "sub231")) ||
               (get_rule_flag("sub232", rflag) && rewrite(max(x + c0, y) - max(w, x + c1), max(fold(c0 - c1), y - max(x + c1, w)), can_prove(y + c1 >= w + c0, this), "sub232")) ||
               (get_rule_flag("sub233", rflag) && rewrite(max(x + c0, y) - max(w, x + c1), min(fold(c0 - c1), max(x + c0, y) - w), can_prove(y + c1 <= w + c0, this), "sub233")) ||

               (get_rule_flag("sub235", rflag) && rewrite(max(y, x) - max(x, w), max(0, y - max(x, w)), can_prove(y >= w, this), "sub235")) ||
               (get_rule_flag("sub236", rflag) && rewrite(max(y, x) - max(x, w), min(0, max(x, y) - w), can_prove(y <= w, this), "sub236")) ||
               (get_rule_flag("sub237", rflag) && rewrite(max(y, x + c0) - max(x, w), max(c0, y - max(x, w)), can_prove(y >= w + c0, this), "sub237")) ||
               (get_rule_flag("sub238", rflag) && rewrite(max(y, x + c0) - max(x, w), min(c0, max(x + c0, y) - w), can_prove(y <= w + c0, this), "sub238")) ||
               (get_rule_flag("sub239", rflag) && rewrite(max(y, x) - max(x + c1, w), max(fold(-c1), y - max(x + c1, w)), can_prove(y + c1 >= w, this), "sub239")) ||
               (get_rule_flag("sub240", rflag) && rewrite(max(y, x) - max(x + c1, w), min(fold(-c1), max(x, y) - w), can_prove(y + c1 <= w, this), "sub240")) ||
               (get_rule_flag("sub241", rflag) && rewrite(max(y, x + c0) - max(x + c1, w), max(fold(c0 - c1), y - max(x + c1, w)), can_prove(y + c1 >= w + c0, this), "sub241")) ||
               (get_rule_flag("sub242", rflag) && rewrite(max(y, x + c0) - max(x + c1, w), min(fold(c0 - c1), max(x + c0, y) - w), can_prove(y + c1 <= w + c0, this), "sub242")))) ||

             (no_overflow_int(op->type) &&
              ((get_rule_flag("sub245", rflag) && rewrite(c0 - (c1 - x)/c2, (fold(c0*c2 - c1 + c2 - 1) + x)/c2, c2 > 0, "sub245")) ||
               (get_rule_flag("sub246", rflag) && rewrite(c0 - (x + c1)/c2, (fold(c0*c2 - c1 + c2 - 1) - x)/c2, c2 > 0, "sub246")) ||
               (get_rule_flag("sub247", rflag) && rewrite(x - (x + y)/c0, (x*fold(c0 - 1) - y + fold(c0 - 1))/c0, c0 > 0, "sub247")) ||
               (get_rule_flag("sub248", rflag) && rewrite(x - (x - y)/c0, (x*fold(c0 - 1) + y + fold(c0 - 1))/c0, c0 > 0, "sub248")) ||
               (get_rule_flag("sub249", rflag) && rewrite(x - (y + x)/c0, (x*fold(c0 - 1) - y + fold(c0 - 1))/c0, c0 > 0, "sub249")) ||
               (get_rule_flag("sub250", rflag) && rewrite(x - (y - x)/c0, (x*fold(c0 + 1) - y + fold(c0 - 1))/c0, c0 > 0, "sub250")) ||
               (get_rule_flag("sub251", rflag) && rewrite((x + y)/c0 - x, (x*fold(1 - c0) + y)/c0, "sub251")) ||
               (get_rule_flag("sub252", rflag) && rewrite((y + x)/c0 - x, (y + x*fold(1 - c0))/c0, "sub252")) ||
               (get_rule_flag("sub253", rflag) && rewrite((x - y)/c0 - x, (x*fold(1 - c0) - y)/c0, "sub253")) ||
               (get_rule_flag("sub254", rflag) && rewrite((y - x)/c0 - x, (y - x*fold(1 + c0))/c0, "sub254")) ||

               (get_rule_flag("sub256", rflag) && rewrite((x/c0)*c0 - x, -(x % c0), c0 > 0, "sub256")) ||
               (get_rule_flag("sub257", rflag) && rewrite(x - (x/c0)*c0, x % c0, c0 > 0, "sub257")) ||
               (get_rule_flag("sub258", rflag) && rewrite(((x + c0)/c1)*c1 - x, (-x) % c1, c1 > 0 && c0 + 1 == c1, "sub258")) ||
               (get_rule_flag("sub259", rflag) && rewrite(x - ((x + c0)/c1)*c1, ((x + c0) % c1) + fold(-c0), c1 > 0 && c0 + 1 == c1, "sub259")) ||
               (get_rule_flag("sub260", rflag) && rewrite(x * c0 - y * c1, (x * fold(c0 / c1) - y) * c1, c0 % c1 == 0, "sub260")) ||
               (get_rule_flag("sub261", rflag) && rewrite(x * c0 - y * c1, (x - y * fold(c1 / c0)) * c0, c1 % c0 == 0, "sub261")) ||
               // Various forms of (x +/- a)/c - (x +/- b)/c. We can
               // *almost* cancel the x.  The right thing to do depends
               // on which of a or b is a constant, and we also need to
               // catch the cases where that constant is zero.
               (get_rule_flag("sub266", rflag) && rewrite(((x + y) + z)/c0 - ((y + x) + w)/c0, ((x + y) + z)/c0 - ((x + y) + w)/c0, c0 > 0, "sub266")) ||
               (get_rule_flag("sub267", rflag) && rewrite((x + y)/c0 - (y + x)/c0, 0, c0 != 0, "sub267")) ||
               (get_rule_flag("sub268", rflag) && rewrite((x + y)/c0 - (x + c1)/c0, (((x + fold(c1 % c0)) % c0) + (y - c1))/c0, c0 > 0, "sub268")) ||
               (get_rule_flag("sub269", rflag) && rewrite((x + c1)/c0 - (x + y)/c0, ((fold(c0 + c1 - 1) - y) - ((x + fold(c1 % c0)) % c0))/c0, c0 > 0, "sub269")) ||
               (get_rule_flag("sub270", rflag) && rewrite((x - y)/c0 - (x + c1)/c0, (((x + fold(c1 % c0)) % c0) - y - c1)/c0, c0 > 0, "sub270")) ||
               (get_rule_flag("sub271", rflag) && rewrite((x + c1)/c0 - (x - y)/c0, ((y + fold(c0 + c1 - 1)) - ((x + fold(c1 % c0)) % c0))/c0, c0 > 0, "sub271")) ||
               (get_rule_flag("sub272", rflag) && rewrite(x/c0 - (x + y)/c0, ((fold(c0 - 1) - y) - (x % c0))/c0, c0 > 0, "sub272")) ||
               (get_rule_flag("sub273", rflag) && rewrite((x + y)/c0 - x/c0, ((x % c0) + y)/c0, c0 > 0, "sub273")) ||
               (get_rule_flag("sub274", rflag) && rewrite(x/c0 - (x - y)/c0, ((y + fold(c0 - 1)) - (x % c0))/c0, c0 > 0, "sub274")) ||
               (get_rule_flag("sub275", rflag) && rewrite((x - y)/c0 - x/c0, ((x % c0) - y)/c0, c0 > 0, "sub275"))))))) {
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