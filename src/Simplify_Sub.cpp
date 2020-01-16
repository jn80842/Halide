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
        bounds->min = a_bounds.min - b_bounds.max;
        bounds->max = a_bounds.max - b_bounds.min;
        bounds->alignment = a_bounds.alignment - b_bounds.alignment;
        bounds->trim_bounds_using_alignment();
    }

    if (may_simplify(op->type)) {

        auto rewrite = IRMatcher::rewriter(IRMatcher::sub(a, b), op->type);
        const int lanes = op->type.lanes();

        if ((get_rule_flag("sub28", rflag) && rewrite(c0 - c1, fold(c0 - c1), "sub28")) ||
            (get_rule_flag("sub29", rflag) && rewrite(IRMatcher::Indeterminate() - x, a, "sub29")) ||
            (get_rule_flag("sub30", rflag) && rewrite(x - IRMatcher::Indeterminate(), b, "sub30")) ||
            (get_rule_flag("sub31", rflag) && rewrite(IRMatcher::Overflow() - x, a, "sub31")) ||
            (get_rule_flag("sub32", rflag) && rewrite(x - IRMatcher::Overflow(), b, "sub32")) ||
            (get_rule_flag("sub33", rflag) && rewrite(x - 0, x, "sub33"))) {
            return rewrite.result;
        }

        if (EVAL_IN_LAMBDA
            ((!op->type.is_uint() && 
             (get_rule_flag("sub39", rflag) && rewrite(x - c0, x + fold(-c0), !overflows(-c0), "sub39"))) ||
             (get_rule_flag("sub40", rflag) && rewrite(x - x, 0, "sub40")) || // We want to remutate this just to get better bounds
             (get_rule_flag("sub41", rflag) && rewrite(ramp(x, y) - ramp(z, w), ramp(x - z, y - w, lanes), "sub41")) ||
             (get_rule_flag("sub42", rflag) && rewrite(ramp(x, y) - broadcast(z), ramp(x - z, y, lanes), "sub42")) ||
             (get_rule_flag("sub43", rflag) && rewrite(broadcast(x) - ramp(z, w), ramp(x - z, -w, lanes), "sub43")) ||
             (get_rule_flag("sub44", rflag) && rewrite(broadcast(x) - broadcast(y), broadcast(x - y, lanes), "sub44")) ||
             (get_rule_flag("sub45", rflag) && rewrite(select(x, y, z) - select(x, w, u), select(x, y - w, z - u), "sub45")) ||
             (get_rule_flag("sub46", rflag) && rewrite(select(x, y, z) - y, select(x, 0, z - y), "sub46")) ||
             (get_rule_flag("sub47", rflag) && rewrite(select(x, y, z) - z, select(x, y - z, 0), "sub47")) ||
             (get_rule_flag("sub48", rflag) && rewrite(y - select(x, y, z), select(x, 0, y - z), "sub48")) ||
             (get_rule_flag("sub49", rflag) && rewrite(z - select(x, y, z), select(x, z - y, 0), "sub49")) ||
             (get_rule_flag("sub50", rflag) && rewrite((x + y) - x, y, "sub50")) ||
             (get_rule_flag("sub51", rflag) && rewrite((x + y) - y, x, "sub51")) ||
             (get_rule_flag("sub52", rflag) && rewrite(x - (x + y), -y, "sub52")) ||
             (get_rule_flag("sub53", rflag) && rewrite(y - (x + y), -x, "sub53")) ||
             (get_rule_flag("sub54", rflag) && rewrite((x - y) - x, -y, "sub54")) ||
             (get_rule_flag("sub55", rflag) && rewrite((select(x, y, z) + w) - select(x, u, v), select(x, y - u, z - v) + w, "sub55")) ||
             (get_rule_flag("sub56", rflag) && rewrite((w + select(x, y, z)) - select(x, u, v), select(x, y - u, z - v) + w, "sub56")) ||
             (get_rule_flag("sub57", rflag) && rewrite(select(x, y, z) - (select(x, u, v) + w), select(x, y - u, z - v) - w, "sub57")) ||
             (get_rule_flag("sub58", rflag) && rewrite(select(x, y, z) - (w + select(x, u, v)), select(x, y - u, z - v) - w, "sub58")) ||
             (get_rule_flag("sub59", rflag) && rewrite((select(x, y, z) - w) - select(x, u, v), select(x, y - u, z - v) - w, "sub59")) ||
             (get_rule_flag("sub60", rflag) && rewrite(c0 - select(x, c1, c2), select(x, fold(c0 - c1), fold(c0 - c2)), "sub60")) ||
             (get_rule_flag("sub61", rflag) && rewrite((x + c0) - c1, x + fold(c0 - c1), "sub61")) ||
             (get_rule_flag("sub62", rflag) && rewrite((x + c0) - (c1 - y), (x + y) + fold(c0 - c1), "sub62")) ||
             (get_rule_flag("sub63", rflag) && rewrite((x + c0) - (y + c1), (x - y) + fold(c0 - c1), "sub63")) ||
             (get_rule_flag("sub64", rflag) && rewrite((x + c0) - y, (x - y) + c0, "sub64")) ||
             (get_rule_flag("sub65", rflag) && rewrite((c0 - x) - (c1 - y), (y - x) + fold(c0 - c1), "sub65")) ||
             (get_rule_flag("sub66", rflag) && rewrite((c0 - x) - (y + c1), fold(c0 - c1) - (x + y), "sub66")) ||
             (get_rule_flag("sub67", rflag) && rewrite(x - (y - z), x + (z - y), "sub67")) ||
             (get_rule_flag("sub68", rflag) && rewrite(x - y*c0, x + y*fold(-c0), c0 < 0 && -c0 > 0, "sub68")) ||
             (get_rule_flag("sub69", rflag) && rewrite(x - (y + c0), (x - y) - c0, "sub69")) ||
             (get_rule_flag("sub70", rflag) && rewrite((c0 - x) - c1, fold(c0 - c1) - x, "sub70")) ||
             (get_rule_flag("sub71", rflag) && rewrite(x*y - z*y, (x - z)*y, "sub71")) ||
             (get_rule_flag("sub72", rflag) && rewrite(x*y - y*z, (x - z)*y, "sub72")) ||
             (get_rule_flag("sub73", rflag) && rewrite(y*x - z*y, y*(x - z), "sub73")) ||
             (get_rule_flag("sub74", rflag) && rewrite(y*x - y*z, y*(x - z), "sub74")) ||
             (get_rule_flag("sub75", rflag) && rewrite((x + y) - (x + z), y - z, "sub75")) ||
             (get_rule_flag("sub76", rflag) && rewrite((x + y) - (z + x), y - z, "sub76")) ||
             (get_rule_flag("sub77", rflag) && rewrite((y + x) - (x + z), y - z, "sub77")) ||
             (get_rule_flag("sub78", rflag) && rewrite((y + x) - (z + x), y - z, "sub78")) ||
             (get_rule_flag("sub79", rflag) && rewrite(((x + y) + z) - x, y + z, "sub79")) ||
             (get_rule_flag("sub80", rflag) && rewrite(((y + x) + z) - x, y + z, "sub80")) ||
             (get_rule_flag("sub81", rflag) && rewrite((z + (x + y)) - x, z + y, "sub81")) ||
             (get_rule_flag("sub82", rflag) && rewrite((z + (y + x)) - x, z + y, "sub82")) ||
             (no_overflow(op->type) &&
              ((get_rule_flag("sub84", rflag) && rewrite(max(x, y) - x, max(0, y - x), "sub84")) ||
               (get_rule_flag("sub85", rflag) && rewrite(min(x, y) - x, min(0, y - x), "sub85")) ||
               (get_rule_flag("sub88", rflag) && rewrite(max(x, y) - y, max(x - y, 0), "sub86")) ||
               (get_rule_flag("sub87", rflag) && rewrite(min(x, y) - y, min(x - y, 0), "sub87")) ||
               (get_rule_flag("sub88", rflag) && rewrite(x - max(x, y), min(0, x - y), !is_const(x), "sub88")) ||
               (get_rule_flag("sub89", rflag) && rewrite(x - min(x, y), max(0, x - y), !is_const(x), "sub89")) ||
               (get_rule_flag("sub90", rflag) && rewrite(y - max(x, y), min(y - x, 0), !is_const(y), "sub90")) ||
               (get_rule_flag("sub91", rflag) && rewrite(y - min(x, y), max(y - x, 0), !is_const(y), "sub91")) ||
               (get_rule_flag("sub92", rflag) && rewrite(x*y - x, x*(y - 1), "sub92")) ||
               (get_rule_flag("sub93", rflag) && rewrite(x*y - y, (x - 1)*y, "sub93")) ||
               (get_rule_flag("sub94", rflag) && rewrite(x - x*y, x*(1 - y), "sub94")) ||
               (get_rule_flag("sub95", rflag) && rewrite(x - y*x, (1 - y)*x, "sub95")) ||
               (get_rule_flag("sub96", rflag) && rewrite(x - min(x + y, z), max(-y, x - z), "sub96")) ||
               (get_rule_flag("sub97", rflag) && rewrite(x - min(y + x, z), max(-y, x - z), "sub97")) ||
               (get_rule_flag("sub98", rflag) && rewrite(x - min(z, x + y), max(x - z, -y), "sub98")) ||
               (get_rule_flag("sub99", rflag) && rewrite(x - min(z, y + x), max(x - z, -y), "sub99")) ||
               (get_rule_flag("sub100", rflag) && rewrite(min(x + y, z) - x, min(y, z - x), "sub100")) ||
               (get_rule_flag("sub101", rflag) && rewrite(min(y + x, z) - x, min(y, z - x), "sub101")) ||
               (get_rule_flag("sub102", rflag) && rewrite(min(z, x + y) - x, min(z - x, y), "sub102")) ||
               (get_rule_flag("sub103", rflag) && rewrite(min(z, y + x) - x, min(z - x, y), "sub103")) ||
               (get_rule_flag("sub104", rflag) && rewrite(min(x, y) - min(y, x), 0, "sub104")) ||
               (get_rule_flag("sub105", rflag) && rewrite(min(x, y) - min(z, w), y - w, can_prove(x - y == z - w, this), "sub105")) ||
               (get_rule_flag("sub106", rflag) && rewrite(min(x, y) - min(w, z), y - w, can_prove(x - y == z - w, this), "sub106")) ||

               (get_rule_flag("sub108", rflag) && rewrite(x - max(x + y, z), min(-y, x - z), "sub108")) ||
               (get_rule_flag("sub109", rflag) && rewrite(x - max(y + x, z), min(-y, x - z), "sub109")) ||
               (get_rule_flag("sub110", rflag) && rewrite(x - max(z, x + y), min(x - z, -y), "sub110")) ||
               (get_rule_flag("sub111", rflag) && rewrite(x - max(z, y + x), min(x - z, -y), "sub111")) ||
               (get_rule_flag("sub112", rflag) && rewrite(max(x + y, z) - x, max(y, z - x), "sub112")) ||
               (get_rule_flag("sub113", rflag) && rewrite(max(y + x, z) - x, max(y, z - x), "sub113")) ||
               (get_rule_flag("sub114", rflag) && rewrite(max(z, x + y) - x, max(z - x, y), "sub114")) ||
               (get_rule_flag("sub115", rflag) && rewrite(max(z, y + x) - x, max(z - x, y), "sub115")) ||
               (get_rule_flag("sub116", rflag) && rewrite(max(x, y) - max(y, x), 0, "sub116")) ||
               (get_rule_flag("sub117", rflag) && rewrite(max(x, y) - max(z, w), y - w, can_prove(x - y == z - w, this), "sub117")) ||
               (get_rule_flag("sub118", rflag) && rewrite(max(x, y) - max(w, z), y - w, can_prove(x - y == z - w, this), "sub118")) ||

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
               (get_rule_flag("sub147", rflag) && rewrite(min(x, y) - min(x, w), min(0, y - min(x, w)), can_prove(y <= w, this), "sub147")) ||
               (get_rule_flag("sub148", rflag) && rewrite(min(x, y) - min(x, w), max(0, min(x, y) - w), can_prove(y >= w, this), "sub148")) ||
               (get_rule_flag("sub149", rflag) && rewrite(min(x + c0, y) - min(x, w), min(c0, y - min(x, w)), can_prove(y <= w + c0, this), "sub149")) ||
               (get_rule_flag("sub150", rflag) && rewrite(min(x + c0, y) - min(x, w), max(c0, min(x + c0, y) - w), can_prove(y >= w + c0, this), "sub150")) ||
               (get_rule_flag("sub151", rflag) && rewrite(min(x, y) - min(x + c1, w), min(fold(-c1), y - min(x + c1, w)), can_prove(y + c1 <= w, this), "sub151")) ||
               (get_rule_flag("sub152", rflag) && rewrite(min(x, y) - min(x + c1, w), max(fold(-c1), min(x, y) - w), can_prove(y + c1 >= w, this), "sub152")) ||
               (get_rule_flag("sub153", rflag) && rewrite(min(x + c0, y) - min(x + c1, w), min(fold(c0 - c1), y - min(x + c1, w)), can_prove(y + c1 <= w + c0, this), "sub153")) ||
               (get_rule_flag("sub154", rflag) && rewrite(min(x + c0, y) - min(x + c1, w), max(fold(c0 - c1), min(x + c0, y) - w), can_prove(y + c1 >= w + c0, this), "sub154")) ||

               (get_rule_flag("sub156", rflag) && rewrite(min(y, x) - min(w, x), min(0, y - min(x, w)), can_prove(y <= w, this), "sub156")) ||
               (get_rule_flag("sub157", rflag) && rewrite(min(y, x) - min(w, x), max(0, min(x, y) - w), can_prove(y >= w, this), "sub157")) ||
               (get_rule_flag("sub158", rflag) && rewrite(min(y, x + c0) - min(w, x), min(c0, y - min(x, w)), can_prove(y <= w + c0, this), "sub158")) ||
               (get_rule_flag("sub159", rflag) && rewrite(min(y, x + c0) - min(w, x), max(c0, min(x + c0, y) - w), can_prove(y >= w + c0, this), "sub159")) ||
               (get_rule_flag("sub160", rflag) && rewrite(min(y, x) - min(w, x + c1), min(fold(-c1), y - min(x + c1, w)), can_prove(y + c1 <= w, this), "sub160")) ||
               (get_rule_flag("sub161", rflag) && rewrite(min(y, x) - min(w, x + c1), max(fold(-c1), min(x, y) - w), can_prove(y + c1 >= w, this), "sub161")) ||
               (get_rule_flag("sub162", rflag) && rewrite(min(y, x + c0) - min(w, x + c1), min(fold(c0 - c1), y - min(x + c1, w)), can_prove(y + c1 <= w + c0, this), "sub162")) ||
               (get_rule_flag("sub163", rflag) && rewrite(min(y, x + c0) - min(w, x + c1), max(fold(c0 - c1), min(x + c0, y) - w), can_prove(y + c1 >= w + c0, this), "sub163")) ||

               (get_rule_flag("sub165", rflag) && rewrite(min(x, y) - min(w, x), min(0, y - min(x, w)), can_prove(y <= w, this), "sub165")) ||
               (get_rule_flag("sub166", rflag) && rewrite(min(x, y) - min(w, x), max(0, min(x, y) - w), can_prove(y >= w, this), "sub166")) ||
               (get_rule_flag("sub167", rflag) && rewrite(min(x + c0, y) - min(w, x), min(c0, y - min(x, w)), can_prove(y <= w + c0, this), "sub167")) ||
               (get_rule_flag("sub168", rflag) && rewrite(min(x + c0, y) - min(w, x), max(c0, min(x + c0, y) - w), can_prove(y >= w + c0, this), "sub168")) ||
               (get_rule_flag("sub169", rflag) && rewrite(min(x, y) - min(w, x + c1), min(fold(-c1), y - min(x + c1, w)), can_prove(y + c1 <= w, this), "sub169")) ||
               (get_rule_flag("sub170", rflag) && rewrite(min(x, y) - min(w, x + c1), max(fold(-c1), min(x, y) - w), can_prove(y + c1 >= w, this), "sub170")) ||
               (get_rule_flag("sub171", rflag) && rewrite(min(x + c0, y) - min(w, x + c1), min(fold(c0 - c1), y - min(x + c1, w)), can_prove(y + c1 <= w + c0, this), "sub171")) ||
               (get_rule_flag("sub172", rflag) && rewrite(min(x + c0, y) - min(w, x + c1), max(fold(c0 - c1), min(x + c0, y) - w), can_prove(y + c1 >= w + c0, this), "sub172")) ||

               (get_rule_flag("sub174", rflag) && rewrite(min(y, x) - min(x, w), min(0, y - min(x, w)), can_prove(y <= w, this), "sub174")) ||
               (get_rule_flag("sub175", rflag) && rewrite(min(y, x) - min(x, w), max(0, min(x, y) - w), can_prove(y >= w, this), "sub175")) ||
               (get_rule_flag("sub176", rflag) && rewrite(min(y, x + c0) - min(x, w), min(c0, y - min(x, w)), can_prove(y <= w + c0, this), "sub176")) ||
               (get_rule_flag("sub177", rflag) && rewrite(min(y, x + c0) - min(x, w), max(c0, min(x + c0, y) - w), can_prove(y >= w + c0, this), "sub177")) ||
               (get_rule_flag("sub178", rflag) && rewrite(min(y, x) - min(x + c1, w), min(fold(-c1), y - min(x + c1, w)), can_prove(y + c1 <= w, this), "sub178")) ||
               (get_rule_flag("sub179", rflag) && rewrite(min(y, x) - min(x + c1, w), max(fold(-c1), min(x, y) - w), can_prove(y + c1 >= w, this), "sub179")) ||
               (get_rule_flag("sub180", rflag) && rewrite(min(y, x + c0) - min(x + c1, w), min(fold(c0 - c1), y - min(x + c1, w)), can_prove(y + c1 <= w + c0, this), "sub180")) ||
               (get_rule_flag("sub181", rflag) && rewrite(min(y, x + c0) - min(x + c1, w), max(fold(c0 - c1), min(x + c0, y) - w), can_prove(y + c1 >= w + c0, this), "sub181")) ||

               // The equivalent rules for max are what you'd
               // expect. Just swap < and > and min and max (apply the
               // isomorphism x -> -x).
               (get_rule_flag("sub186", rflag) && rewrite(max(x, y) - max(x, w), max(0, y - max(x, w)), can_prove(y >= w, this), "sub186")) ||
               (get_rule_flag("sub187", rflag) && rewrite(max(x, y) - max(x, w), min(0, max(x, y) - w), can_prove(y <= w, this), "sub187")) ||
               (get_rule_flag("sub188", rflag) && rewrite(max(x + c0, y) - max(x, w), max(c0, y - max(x, w)), can_prove(y >= w + c0, this), "sub188")) ||
               (get_rule_flag("sub189", rflag) && rewrite(max(x + c0, y) - max(x, w), min(c0, max(x + c0, y) - w), can_prove(y <= w + c0, this), "sub189")) ||
               (get_rule_flag("sub190", rflag) && rewrite(max(x, y) - max(x + c1, w), max(fold(-c1), y - max(x + c1, w)), can_prove(y + c1 >= w, this), "sub190")) ||
               (get_rule_flag("sub191", rflag) && rewrite(max(x, y) - max(x + c1, w), min(fold(-c1), max(x, y) - w), can_prove(y + c1 <= w, this), "sub191")) ||
               (get_rule_flag("sub192", rflag) && rewrite(max(x + c0, y) - max(x + c1, w), max(fold(c0 - c1), y - max(x + c1, w)), can_prove(y + c1 >= w + c0, this), "sub192")) ||
               (get_rule_flag("sub193", rflag) && rewrite(max(x + c0, y) - max(x + c1, w), min(fold(c0 - c1), max(x + c0, y) - w), can_prove(y + c1 <= w + c0, this), "sub193")) ||

               (get_rule_flag("sub195", rflag) && rewrite(max(y, x) - max(w, x), max(0, y - max(x, w)), can_prove(y >= w, this), "sub195")) ||
               (get_rule_flag("sub196", rflag) && rewrite(max(y, x) - max(w, x), min(0, max(x, y) - w), can_prove(y <= w, this), "sub196")) ||
               (get_rule_flag("sub197", rflag) && rewrite(max(y, x + c0) - max(w, x), max(c0, y - max(x, w)), can_prove(y >= w + c0, this), "sub197")) ||
               (get_rule_flag("sub198", rflag) && rewrite(max(y, x + c0) - max(w, x), min(c0, max(x + c0, y) - w), can_prove(y <= w + c0, this), "sub198")) ||
               (get_rule_flag("sub199", rflag) && rewrite(max(y, x) - max(w, x + c1), max(fold(-c1), y - max(x + c1, w)), can_prove(y + c1 >= w, this), "sub199")) ||
               (get_rule_flag("sub200", rflag) && rewrite(max(y, x) - max(w, x + c1), min(fold(-c1), max(x, y) - w), can_prove(y + c1 <= w, this), "sub200")) ||
               (get_rule_flag("sub201", rflag) && rewrite(max(y, x + c0) - max(w, x + c1), max(fold(c0 - c1), y - max(x + c1, w)), can_prove(y + c1 >= w + c0, this), "sub201")) ||
               (get_rule_flag("sub202", rflag) && rewrite(max(y, x + c0) - max(w, x + c1), min(fold(c0 - c1), max(x + c0, y) - w), can_prove(y + c1 <= w + c0, this), "sub202")) ||

               (get_rule_flag("sub204", rflag) && rewrite(max(x, y) - max(w, x), max(0, y - max(x, w)), can_prove(y >= w, this), "sub204")) ||
               (get_rule_flag("sub205", rflag) && rewrite(max(x, y) - max(w, x), min(0, max(x, y) - w), can_prove(y <= w, this), "sub205")) ||
               (get_rule_flag("sub206", rflag) && rewrite(max(x + c0, y) - max(w, x), max(c0, y - max(x, w)), can_prove(y >= w + c0, this), "sub206")) ||
               (get_rule_flag("sub207", rflag) && rewrite(max(x + c0, y) - max(w, x), min(c0, max(x + c0, y) - w), can_prove(y <= w + c0, this), "sub207")) ||
               (get_rule_flag("sub208", rflag) && rewrite(max(x, y) - max(w, x + c1), max(fold(-c1), y - max(x + c1, w)), can_prove(y + c1 >= w, this), "sub208")) ||
               (get_rule_flag("sub209", rflag) && rewrite(max(x, y) - max(w, x + c1), min(fold(-c1), max(x, y) - w), can_prove(y + c1 <= w, this), "sub209")) ||
               (get_rule_flag("sub210", rflag) && rewrite(max(x + c0, y) - max(w, x + c1), max(fold(c0 - c1), y - max(x + c1, w)), can_prove(y + c1 >= w + c0, this), "sub210"))||
               (get_rule_flag("sub211", rflag) && rewrite(max(x + c0, y) - max(w, x + c1), min(fold(c0 - c1), max(x + c0, y) - w), can_prove(y + c1 <= w + c0, this), "sub211")) ||

               (get_rule_flag("sub213", rflag) && rewrite(max(y, x) - max(x, w), max(0, y - max(x, w)), can_prove(y >= w, this), "sub213")) ||
               (get_rule_flag("sub214", rflag) && rewrite(max(y, x) - max(x, w), min(0, max(x, y) - w), can_prove(y <= w, this), "sub214")) ||
               (get_rule_flag("sub215", rflag) && rewrite(max(y, x + c0) - max(x, w), max(c0, y - max(x, w)), can_prove(y >= w + c0, this), "sub215")) ||
               (get_rule_flag("sub216", rflag) && rewrite(max(y, x + c0) - max(x, w), min(c0, max(x + c0, y) - w), can_prove(y <= w + c0, this), "sub216")) ||
               (get_rule_flag("sub217", rflag) && rewrite(max(y, x) - max(x + c1, w), max(fold(-c1), y - max(x + c1, w)), can_prove(y + c1 >= w, this), "sub217")) ||
               (get_rule_flag("sub218", rflag) && rewrite(max(y, x) - max(x + c1, w), min(fold(-c1), max(x, y) - w), can_prove(y + c1 <= w, this), "sub218")) ||
               (get_rule_flag("sub219", rflag) && rewrite(max(y, x + c0) - max(x + c1, w), max(fold(c0 - c1), y - max(x + c1, w)), can_prove(y + c1 >= w + c0, this), "sub219")) ||
               (get_rule_flag("sub220", rflag) && rewrite(max(y, x + c0) - max(x + c1, w), min(fold(c0 - c1), max(x + c0, y) - w), can_prove(y + c1 <= w + c0, this), "sub220")))) ||

             (no_overflow_int(op->type) &&
              ((get_rule_flag("sub223", rflag) && rewrite(c0 - (c1 - x)/c2, (fold(c0*c2 - c1 + c2 - 1) + x)/c2, c2 > 0, "sub223")) ||
               (get_rule_flag("sub224", rflag) && rewrite(c0 - (x + c1)/c2, (fold(c0*c2 - c1 + c2 - 1) - x)/c2, c2 > 0, "sub224")) ||
               (get_rule_flag("sub225", rflag) && rewrite(x - (x + y)/c0, (x*fold(c0 - 1) - y + fold(c0 - 1))/c0, c0 > 0, "sub225")) ||
               (get_rule_flag("sub226", rflag) && rewrite(x - (x - y)/c0, (x*fold(c0 - 1) + y + fold(c0 - 1))/c0, c0 > 0, "sub226")) ||
               (get_rule_flag("sub227", rflag) && rewrite(x - (y + x)/c0, (x*fold(c0 - 1) - y + fold(c0 - 1))/c0, c0 > 0, "sub227")) ||
               (get_rule_flag("sub228", rflag) && rewrite(x - (y - x)/c0, (x*fold(c0 + 1) - y + fold(c0 - 1))/c0, c0 > 0, "sub228")) ||
               (get_rule_flag("sub229", rflag) && rewrite((x + y)/c0 - x, (x*fold(1 - c0) + y)/c0, "sub229")) ||
               (get_rule_flag("sub230", rflag) && rewrite((y + x)/c0 - x, (y + x*fold(1 - c0))/c0, "sub230")) ||
               (get_rule_flag("sub231", rflag) && rewrite((x - y)/c0 - x, (x*fold(1 - c0) - y)/c0, "sub231")) ||
               (get_rule_flag("sub232", rflag) && rewrite((y - x)/c0 - x, (y - x*fold(1 + c0))/c0, "sub232")) ||

               (get_rule_flag("sub234", rflag) && rewrite((x/c0)*c0 - x, -(x % c0), c0 > 0, "sub234")) ||
               (get_rule_flag("sub235", rflag) && rewrite(x - (x/c0)*c0, x % c0, c0 > 0, "sub235")) ||
               (get_rule_flag("sub236", rflag) && rewrite(((x + c0)/c1)*c1 - x, (-x) % c1, c1 > 0 && c0 + 1 == c1, "sub236")) ||
               (get_rule_flag("sub237", rflag) && rewrite(x - ((x + c0)/c1)*c1, ((x + c0) % c1) + fold(-c0), c1 > 0 && c0 + 1 == c1, "sub237")) ||
               (get_rule_flag("sub238", rflag) && rewrite(x * c0 - y * c1, (x * fold(c0 / c1) - y) * c1, c0 % c1 == 0, "sub238")) ||
               (get_rule_flag("sub239", rflag) && rewrite(x * c0 - y * c1, (x - y * fold(c1 / c0)) * c0, c1 % c0 == 0, "sub239")) ||
               // Various forms of (x +/- a)/c - (x +/- b)/c. We can
               // *almost* cancel the x.  The right thing to do depends
               // on which of a or b is a constant, and we also need to
               // catch the cases where that constant is zero.
               (get_rule_flag("sub244", rflag) && rewrite(((x + y) + z)/c0 - ((y + x) + w)/c0, ((x + y) + z)/c0 - ((x + y) + w)/c0, c0 > 0, "sub244")) ||
               (get_rule_flag("sub245", rflag) && rewrite((x + y)/c0 - (y + x)/c0, 0, c0 != 0, "sub245")) ||
               (get_rule_flag("sub246", rflag) && rewrite((x + y)/c0 - (x + c1)/c0, (((x + fold(c1 % c0)) % c0) + (y - c1))/c0, c0 > 0, "sub246")) ||
               (get_rule_flag("sub247", rflag) && rewrite((x + c1)/c0 - (x + y)/c0, ((fold(c0 + c1 - 1) - y) - ((x + fold(c1 % c0)) % c0))/c0, c0 > 0, "sub247")) ||
               (get_rule_flag("sub248", rflag) && rewrite((x - y)/c0 - (x + c1)/c0, (((x + fold(c1 % c0)) % c0) - y - c1)/c0, c0 > 0, "sub248")) ||
               (get_rule_flag("sub249", rflag) && rewrite((x + c1)/c0 - (x - y)/c0, ((y + fold(c0 + c1 - 1)) - ((x + fold(c1 % c0)) % c0))/c0, c0 > 0, "sub249")) ||
               (get_rule_flag("sub250", rflag) && rewrite(x/c0 - (x + y)/c0, ((fold(c0 - 1) - y) - (x % c0))/c0, c0 > 0, "sub250")) ||
               (get_rule_flag("sub251", rflag) && rewrite((x + y)/c0 - x/c0, ((x % c0) + y)/c0, c0 > 0, "sub251")) ||
               (get_rule_flag("sub252", rflag) && rewrite(x/c0 - (x - y)/c0, ((y + fold(c0 - 1)) - (x % c0))/c0, c0 > 0, "sub252")) ||
               (get_rule_flag("sub253", rflag) && rewrite((x - y)/c0 - x/c0, ((x % c0) - y)/c0, c0 > 0, "sub253")) ||
               false)))) {
            return mutate(std::move(rewrite.result), bounds);
        }

        if (no_overflow_int(op->type) &&
            use_synthesized_rules &&
            (
#include "Simplify_Sub.inc"
             )) {
            return mutate(std::move(rewrite.result), bounds);
        }
    }

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


}
}
