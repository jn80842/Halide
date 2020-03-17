#include "Simplify_Internal.h"

namespace Halide {
namespace Internal {

Expr Simplify::visit(const LT *op, ExprInfo *bounds) {
    ExprInfo a_bounds, b_bounds;
    Expr a = mutate(op->a, &a_bounds);
    Expr b = mutate(op->b, &b_bounds);

    const int lanes = op->type.lanes();
    Type ty = a.type();

    if (truths.count(op)) {
        return const_true(lanes);
    } else if (falsehoods.count(op)) {
        return const_false(lanes);
    }

    if (may_simplify(ty)) {

        // Prove or disprove using bounds analysis
        if (a_bounds.max_defined && b_bounds.min_defined && a_bounds.max < b_bounds.min) {
            return const_true(lanes);
        }

        if (a_bounds.min_defined && b_bounds.max_defined && a_bounds.min >= b_bounds.max) {
            return const_false(lanes);
        }

        auto rewrite = IRMatcher::rewriter(IRMatcher::lt(a, b), op->type, ty);

        // clang-format off
        if (EVAL_IN_LAMBDA
            ((get_rule_flag("lt35", rflag) && rewrite(c0 < c1, fold(c0 < c1), "lt35")) ||
             (get_rule_flag("lt36", rflag) && rewrite(x < x, false, "lt36")) ||
             (get_rule_flag("lt37", rflag) && rewrite(x < ty.min(), false, "lt37")) ||
             (get_rule_flag("lt38", rflag) && rewrite(ty.max() < x, false, "lt38")) ||

             (get_rule_flag("lt40", rflag) && rewrite(max(x, y) < x, false, "lt40")) ||
             (get_rule_flag("lt41", rflag) && rewrite(max(y, x) < x, false, "lt41")) ||
             (get_rule_flag("lt42", rflag) && rewrite(x < min(x, y), false, "lt42")) ||
             (get_rule_flag("lt43", rflag) && rewrite(x < min(y, x), false, "lt43")) ||

             // Comparisons of ramps and broadcasts. If the first
             // and last lanes are provably < or >= the broadcast
             // we can collapse the comparison.
             (no_overflow(op->type) &&
              ((get_rule_flag("lt49", rflag) && rewrite(ramp(x, c1) < broadcast(z), true, can_prove(x + fold(max(0, c1 * (lanes - 1))) < z, this), "lt49")) ||
               (get_rule_flag("lt50", rflag) && rewrite(ramp(x, c1) < broadcast(z), false, can_prove(x + fold(min(0, c1 * (lanes - 1))) >= z, this), "lt50")) ||
               (get_rule_flag("lt51", rflag) && rewrite(broadcast(z) < ramp(x, c1), true, can_prove(z < x + fold(min(0, c1 * (lanes - 1))), this), "lt51")) ||
               (get_rule_flag("lt52", rflag) && rewrite(broadcast(z) < ramp(x, c1), false, can_prove(z >= x + fold(max(0, c1 * (lanes - 1))), this), "lt52")))))){
            return rewrite.result;
        }
        // clang-format on

        // clang-format off
        if ((get_rule_flag("lt58", rflag) && rewrite(broadcast(x) < broadcast(y), broadcast(x < y, lanes), "lt58")) ||
            (no_overflow(ty) && EVAL_IN_LAMBDA
             ((get_rule_flag("lt60", rflag) && rewrite(ramp(x, y) < ramp(z, y), broadcast(x < z, lanes), "lt60")) ||
              // Move constants to the RHS
              (get_rule_flag("lt62", rflag) && rewrite(x + c0 < y, x < y + fold(-c0), "lt62")) ||

              // Merge RHS constant additions with a constant LHS
              (get_rule_flag("lt65", rflag) && rewrite(c0 < x + c1, fold(c0 - c1) < x, "lt65")) ||

              // Normalize subtractions to additions to cut down on cases to consider
              (get_rule_flag("lt68", rflag) && rewrite(x - y < z, x < z + y, "lt68")) ||
              (get_rule_flag("lt69", rflag) && rewrite(z < x - y, z + y < x, "lt69")) ||

              (get_rule_flag("lt71", rflag) && rewrite((x - y) + z < w, x + z < y + w, "lt71")) ||
              (get_rule_flag("lt72", rflag) && rewrite(z + (x - y) < w, x + z < y + w, "lt72")) ||
              (get_rule_flag("lt73", rflag) && rewrite(w < (x - y) + z, w + y < x + z, "lt73")) ||
              (get_rule_flag("lt74", rflag) && rewrite(w < z + (x - y), w + y < x + z, "lt74")) ||

              (get_rule_flag("lt76", rflag) && rewrite(((x - y) + z) + u < w, x + z + u < w + y, "lt76")) ||
              (get_rule_flag("lt77", rflag) && rewrite((z + (x - y)) + u < w, x + z + u < w + y, "lt77")) ||
              (get_rule_flag("lt78", rflag) && rewrite(u + ((x - y) + z) < w, x + z + u < w + y, "lt78")) ||
              (get_rule_flag("lt79", rflag) && rewrite(u + (z + (x - y)) < w, x + z + u < w + y, "lt79")) ||

              (get_rule_flag("lt81", rflag) && rewrite(w < ((x - y) + z) + u, w + y < x + z + u, "lt81")) ||
              (get_rule_flag("lt82", rflag) && rewrite(w < (z + (x - y)) + u, w + y < x + z + u, "lt82")) ||
              (get_rule_flag("lt83", rflag) && rewrite(w < u + ((x - y) + z), w + y < x + z + u, "lt83")) ||
              (get_rule_flag("lt84", rflag) && rewrite(w < u + (z + (x - y)), w + y < x + z + u, "lt84")) ||

              // Cancellations in linear expressions
              // 1 < 2
              (get_rule_flag("lt88", rflag) && rewrite(x < x + y, 0 < y, "lt88")) ||
              (get_rule_flag("lt89", rflag) && rewrite(x < y + x, 0 < y, "lt89")) ||

              // 2 < 1
              (get_rule_flag("lt92", rflag) && rewrite(x + y < x, y < 0, "lt92")) ||
              (get_rule_flag("lt93", rflag) && rewrite(y + x < x, y < 0, "lt93")) ||

              // 2 < 2
              (get_rule_flag("lt96", rflag) && rewrite(x + y < x + z, y < z, "lt96")) ||
              (get_rule_flag("lt97", rflag) && rewrite(x + y < z + x, y < z, "lt97")) ||
              (get_rule_flag("lt98", rflag) && rewrite(y + x < x + z, y < z, "lt98")) ||
              (get_rule_flag("lt99", rflag) && rewrite(y + x < z + x, y < z, "lt99")) ||

              // 3 < 2
              (get_rule_flag("lt102", rflag) && rewrite((x + y) + w < x + z, y + w < z, "lt102")) ||
              (get_rule_flag("lt103", rflag) && rewrite((y + x) + w < x + z, y + w < z, "lt103")) ||
              (get_rule_flag("lt104", rflag) && rewrite(w + (x + y) < x + z, y + w < z, "lt104")) ||
              (get_rule_flag("lt105", rflag) && rewrite(w + (y + x) < x + z, y + w < z, "lt105")) ||
              (get_rule_flag("lt106", rflag) && rewrite((x + y) + w < z + x, y + w < z, "lt106")) ||
              (get_rule_flag("lt107", rflag) && rewrite((y + x) + w < z + x, y + w < z, "lt107")) ||
              (get_rule_flag("lt108", rflag) && rewrite(w + (x + y) < z + x, y + w < z, "lt108")) ||
              (get_rule_flag("lt109", rflag) && rewrite(w + (y + x) < z + x, y + w < z, "lt109")) ||

              // 2 < 3
              (get_rule_flag("lt112", rflag) && rewrite(x + z < (x + y) + w, z < y + w, "lt112")) ||
              (get_rule_flag("lt113", rflag) && rewrite(x + z < (y + x) + w, z < y + w, "lt113")) ||
              (get_rule_flag("lt114", rflag) && rewrite(x + z < w + (x + y), z < y + w, "lt114")) ||
              (get_rule_flag("lt115", rflag) && rewrite(x + z < w + (y + x), z < y + w, "lt115")) ||
              (get_rule_flag("lt116", rflag) && rewrite(z + x < (x + y) + w, z < y + w, "lt116")) ||
              (get_rule_flag("lt117", rflag) && rewrite(z + x < (y + x) + w, z < y + w, "lt117")) ||
              (get_rule_flag("lt118", rflag) && rewrite(z + x < w + (x + y), z < y + w, "lt118")) ||
              (get_rule_flag("lt119", rflag) && rewrite(z + x < w + (y + x), z < y + w, "lt119")) ||

              // 3 < 3
              (get_rule_flag("lt122", rflag) && rewrite((x + y) + w < (x + z) + u, y + w < z + u, "lt122")) ||
              (get_rule_flag("lt123", rflag) && rewrite((y + x) + w < (x + z) + u, y + w < z + u, "lt123")) ||
              (get_rule_flag("lt124", rflag) && rewrite((x + y) + w < (z + x) + u, y + w < z + u, "lt124")) ||
              (get_rule_flag("lt125", rflag) && rewrite((y + x) + w < (z + x) + u, y + w < z + u, "lt125")) ||
              (get_rule_flag("lt126", rflag) && rewrite(w + (x + y) < (x + z) + u, y + w < z + u, "lt126")) ||
              (get_rule_flag("lt127", rflag) && rewrite(w + (y + x) < (x + z) + u, y + w < z + u, "lt127")) ||
              (get_rule_flag("lt128", rflag) && rewrite(w + (x + y) < (z + x) + u, y + w < z + u, "lt128")) ||
              (get_rule_flag("lt129", rflag) && rewrite(w + (y + x) < (z + x) + u, y + w < z + u, "lt129")) ||
              (get_rule_flag("lt130", rflag) && rewrite((x + y) + w < u + (x + z), y + w < z + u, "lt130")) ||
              (get_rule_flag("lt131", rflag) && rewrite((y + x) + w < u + (x + z), y + w < z + u, "lt131")) ||
              (get_rule_flag("lt132", rflag) && rewrite((x + y) + w < u + (z + x), y + w < z + u, "lt132")) ||
              (get_rule_flag("lt133", rflag) && rewrite((y + x) + w < u + (z + x), y + w < z + u, "lt133")) ||
              (get_rule_flag("lt134", rflag) && rewrite(w + (x + y) < u + (x + z), y + w < z + u, "lt134")) ||
              (get_rule_flag("lt135", rflag) && rewrite(w + (y + x) < u + (x + z), y + w < z + u, "lt135")) ||
              (get_rule_flag("lt136", rflag) && rewrite(w + (x + y) < u + (z + x), y + w < z + u, "lt136")) ||
              (get_rule_flag("lt137", rflag) && rewrite(w + (y + x) < u + (z + x), y + w < z + u, "lt137")) ||

              // Cancel a multiplication
              (get_rule_flag("lt140", rflag) && rewrite(x * c0 < y * c0, x < y, c0 > 0, "lt140")) ||
              (get_rule_flag("lt141", rflag) && rewrite(x * c0 < y * c0, y < x, c0 < 0, "lt141")) ||

              (ty.is_int()   && (get_rule_flag("lt143", rflag) && rewrite(x * c0 < c1, x < fold((c1 + c0 - 1) / c0), c0 > 0, "lt143"))) ||
              (ty.is_float() && (get_rule_flag("lt143", rflag) && rewrite(x * c0 < c1, x < fold(c1 / c0), c0 > 0, "lt144"))) ||
              (get_rule_flag("lt145", rflag) && (get_rule_flag("lt145", rflag) && rewrite(c1 < x * c0, fold(c1 / c0) < x, c0 > 0, "lt145"))) ||

              // Multiply-out a division
              (get_rule_flag("lt148", rflag) && rewrite(x / c0 < c1, x < c1 * c0, c0 > 0, "lt148")) ||
              (ty.is_int() && (get_rule_flag("lt149", rflag) && rewrite(c0 < x / c1, fold((c0 + 1) * c1 - 1) < x, c1 > 0, "lt149"))) ||
              (ty.is_float() && (get_rule_flag("lt150", rflag) && rewrite(c0 < x / c1, fold(c0 * c1) < x, c1 > 0, "lt150"))) ||

              // We want to break max(x, y) < z into x < z && y <
              // z in cases where one of those two terms is going
              // to fold.
              (get_rule_flag("lt155", rflag) && rewrite(min(x + c0, y) < x + c1, fold(c0 < c1) || y < x + c1, "lt155")) ||
              (get_rule_flag("lt156", rflag) && rewrite(min(y, x + c0) < x + c1, fold(c0 < c1) || y < x + c1, "lt156")) ||
              (get_rule_flag("lt157", rflag) && rewrite(max(x + c0, y) < x + c1, fold(c0 < c1) && y < x + c1, "lt157")) ||
              (get_rule_flag("lt158", rflag) && rewrite(max(y, x + c0) < x + c1, fold(c0 < c1) && y < x + c1, "lt158")) ||

              (get_rule_flag("lt160", rflag) && rewrite(x < min(x + c0, y) + c1, fold(0 < c0 + c1) && x < y + c1, "lt160")) ||
              (get_rule_flag("lt161", rflag) && rewrite(x < min(y, x + c0) + c1, fold(0 < c0 + c1) && x < y + c1, "lt161")) ||
              (get_rule_flag("lt162", rflag) && rewrite(x < max(x + c0, y) + c1, fold(0 < c0 + c1) || x < y + c1, "lt162")) ||
              (get_rule_flag("lt163", rflag) && rewrite(x < max(y, x + c0) + c1, fold(0 < c0 + c1) || x < y + c1, "lt163")) ||

              // Special cases where c0 == 0
              (get_rule_flag("lt166", rflag) && rewrite(min(x, y) < x + c1, fold(0 < c1) || y < x + c1, "lt166")) ||
              (get_rule_flag("lt167", rflag) && rewrite(min(y, x) < x + c1, fold(0 < c1) || y < x + c1, "lt167")) ||
              (get_rule_flag("lt168", rflag) && rewrite(max(x, y) < x + c1, fold(0 < c1) && y < x + c1, "lt168")) ||
              (get_rule_flag("lt169", rflag) && rewrite(max(y, x) < x + c1, fold(0 < c1) && y < x + c1, "lt169")) ||

              (get_rule_flag("lt171", rflag) && rewrite(x < min(x, y) + c1, fold(0 < c1) && x < y + c1, "lt171")) ||
              (get_rule_flag("lt172", rflag) && rewrite(x < min(y, x) + c1, fold(0 < c1) && x < y + c1, "lt172")) ||
              (get_rule_flag("lt173", rflag) && rewrite(x < max(x, y) + c1, fold(0 < c1) || x < y + c1, "lt173")) ||
              (get_rule_flag("lt174", rflag) && rewrite(x < max(y, x) + c1, fold(0 < c1) || x < y + c1, "lt174")) ||

              // Special cases where c1 == 0
              (get_rule_flag("lt177", rflag) && rewrite(min(x + c0, y) < x, fold(c0 < 0) || y < x, "lt177")) ||
              (get_rule_flag("lt178", rflag) && rewrite(min(y, x + c0) < x, fold(c0 < 0) || y < x, "lt178")) ||
              (get_rule_flag("lt179", rflag) && rewrite(max(x + c0, y) < x, fold(c0 < 0) && y < x, "lt179")) ||
              (get_rule_flag("lt180", rflag) && rewrite(max(y, x + c0) < x, fold(c0 < 0) && y < x, "lt180")) ||

              (get_rule_flag("lt182", rflag) && rewrite(x < min(x + c0, y), fold(0 < c0) && x < y, "lt182")) ||
              (get_rule_flag("lt183", rflag) && rewrite(x < min(y, x + c0), fold(0 < c0) && x < y, "lt183")) ||
              (get_rule_flag("lt184", rflag) && rewrite(x < max(x + c0, y), fold(0 < c0) || x < y, "lt184")) ||
              (get_rule_flag("lt185", rflag) && rewrite(x < max(y, x + c0), fold(0 < c0) || x < y, "lt185")) ||

              // Special cases where c0 == c1 == 0
              (get_rule_flag("lt188", rflag) && rewrite(min(x, y) < x, y < x, "lt188")) ||
              (get_rule_flag("lt189", rflag) && rewrite(min(y, x) < x, y < x, "lt189")) ||
              (get_rule_flag("lt190", rflag) && rewrite(x < max(x, y), x < y, "lt190")) ||
              (get_rule_flag("lt191", rflag) && rewrite(x < max(y, x), x < y, "lt191")) ||

              // Special case where x is constant
              (get_rule_flag("lt194", rflag) && rewrite(min(y, c0) < c1, fold(c0 < c1) || y < c1, "lt194")) ||
              (get_rule_flag("lt195", rflag) && rewrite(max(y, c0) < c1, fold(c0 < c1) && y < c1, "lt195")) ||
              (get_rule_flag("lt196", rflag) && rewrite(c1 < min(y, c0), fold(c1 < c0) && c1 < y, "lt196")) ||
              (get_rule_flag("lt197", rflag) && rewrite(c1 < max(y, c0), fold(c1 < c0) || c1 < y, "lt197")) ||

              // Comparisons with selects:
              // x < select(c, t, f) == c && (x < t) || !c && (x < f)
              // This is profitable when x < t or x < f is statically provable
              (get_rule_flag("lt202", rflag) && rewrite(x < select(y, x + c0, z), !y && (x < z), c0 <= 0, "lt202")) ||
              (get_rule_flag("lt203", rflag) && rewrite(x < select(y, x + c0, z), y || (x < z), c0 > 0, "lt203")) ||
              (get_rule_flag("lt204", rflag) && rewrite(x < select(y, z, x + c0), y && (x < z), c0 <= 0, "lt204")) ||
              (get_rule_flag("lt205", rflag) && rewrite(x < select(y, z, x + c0), !y || (x < z), c0 > 0, "lt205")) ||

              (get_rule_flag("lt207", rflag) && rewrite(x < select(y, x + c0, z) + c1, !y && (x < z + c1), c0 + c1 <= 0, "lt207")) ||
              (get_rule_flag("lt208", rflag) && rewrite(x < select(y, x + c0, z) + c1, y || (x < z + c1), c0 + c1 > 0, "lt208")) ||
              (get_rule_flag("lt209", rflag) && rewrite(x < select(y, z, x + c0) + c1, y && (x < z + c1), c0 + c1 <= 0, "lt209")) ||
              (get_rule_flag("lt210", rflag) && rewrite(x < select(y, z, x + c0) + c1, !y || (x < z + c1), c0 + c1 > 0, "lt210")) ||

              (get_rule_flag("lt212", rflag) && rewrite(select(y, x + c0, z) < x, !y && (z < x), c0 >= 0, "lt212")) ||
              (get_rule_flag("lt213", rflag) && rewrite(select(y, x + c0, z) < x, y || (z < x), c0 < 0, "lt213")) ||
              (get_rule_flag("lt214", rflag) && rewrite(select(y, z, x + c0) < x, y && (z < x), c0 >= 0, "lt214")) ||
              (get_rule_flag("lt215", rflag) && rewrite(select(y, z, x + c0) < x, !y || (z < x), c0 < 0, "lt215")) ||

              (get_rule_flag("lt217", rflag) && rewrite(select(y, x + c0, z) < x + c1, !y && (z < x + c1), c0 >= c1, "lt217")) ||
              (get_rule_flag("lt218", rflag) && rewrite(select(y, x + c0, z) < x + c1, y || (z < x + c1), c0 < c1, "lt218")) ||
              (get_rule_flag("lt219", rflag) && rewrite(select(y, z, x + c0) < x + c1, y && (z < x + c1), c0 >= c1, "lt219")) ||
              (get_rule_flag("lt220", rflag) && rewrite(select(y, z, x + c0) < x + c1, !y || (z < x + c1), c0 < c1, "lt220")) ||

              // Normalize comparison of ramps to a comparison of a ramp and a broadacst
              (get_rule_flag("lt223", rflag) && rewrite(ramp(x, y) < ramp(z, w), ramp(x - z, y - w, lanes) < 0, "lt223")))) ||

            (no_overflow_int(ty) && EVAL_IN_LAMBDA
             ((get_rule_flag("lt226", rflag) && rewrite(x * c0 < y * c1, x < y * fold(c1 / c0), c1 % c0 == 0 && c0 > 0, "lt226")) ||
              (get_rule_flag("lt227", rflag) && rewrite(x * c0 < y * c1, x * fold(c0 / c1) < y, c0 % c1 == 0 && c1 > 0, "lt227")) ||

              (get_rule_flag("lt229", rflag) && rewrite(x * c0 < y * c0 + c1, x < y + fold((c1 + c0 - 1)/c0), c0 > 0, "lt229")) ||
              (get_rule_flag("lt230", rflag) && rewrite(x * c0 + c1 < y * c0, x + fold(c1/c0) < y, c0 > 0, "lt230")) ||

              // Comparison of stair-step functions. The basic transformation is:
              //   ((x + y)/c1)*c1 < x
              // = (x + y) - (x + y) % c1 < x (when c1 > 0)
              // = y - (x + y) % c1 < 0
              // = y < (x + y) % c1
              // This cancels x but duplicates y, so we only do it when y is a constant.

              // A more general version with extra terms w and z
              (get_rule_flag("lt240", rflag) && rewrite(((x + c0)/c1)*c1 + w < x + z, (w + c0) < ((x + c0) % c1) + z, c1 > 0, "lt240")) ||
              (get_rule_flag("lt241", rflag) && rewrite(w + ((x + c0)/c1)*c1 < x + z, (w + c0) < ((x + c0) % c1) + z, c1 > 0, "lt241")) ||
              (get_rule_flag("lt242", rflag) && rewrite(((x + c0)/c1)*c1 + w < z + x, (w + c0) < ((x + c0) % c1) + z, c1 > 0, "lt242")) ||
              (get_rule_flag("lt243", rflag) && rewrite(w + ((x + c0)/c1)*c1 < z + x, (w + c0) < ((x + c0) % c1) + z, c1 > 0, "lt243")) ||
              (get_rule_flag("lt244", rflag) && rewrite(x + z < ((x + c0)/c1)*c1 + w, ((x + c0) % c1) + z < w + c0, c1 > 0, "lt244")) ||
              (get_rule_flag("lt245", rflag) && rewrite(x + z < w + ((x + c0)/c1)*c1, ((x + c0) % c1) + z < w + c0, c1 > 0, "lt245")) ||
              (get_rule_flag("lt246", rflag) && rewrite(z + x < ((x + c0)/c1)*c1 + w, ((x + c0) % c1) + z < w + c0, c1 > 0, "lt246")) ||
              (get_rule_flag("lt247", rflag) && rewrite(z + x < w + ((x + c0)/c1)*c1, ((x + c0) % c1) + z < w + c0, c1 > 0, "lt247")) ||

              // w = 0
              (get_rule_flag("lt250", rflag) && rewrite(((x + c0)/c1)*c1 < x + z, c0 < ((x + c0) % c1) + z, c1 > 0, "lt250")) ||
              (get_rule_flag("lt251", rflag) && rewrite(((x + c0)/c1)*c1 < z + x, c0 < ((x + c0) % c1) + z, c1 > 0, "lt251")) ||
              (get_rule_flag("lt252", rflag) && rewrite(x + z < ((x + c0)/c1)*c1, ((x + c0) % c1) + z < c0, c1 > 0, "lt252")) ||
              (get_rule_flag("lt253", rflag) && rewrite(z + x < ((x + c0)/c1)*c1, ((x + c0) % c1) + z < c0, c1 > 0, "lt253")) ||

              // z = 0
              (get_rule_flag("lt256", rflag) && rewrite(((x + c0)/c1)*c1 + w < x, (w + c0) < ((x + c0) % c1), c1 > 0, "lt256")) ||
              (get_rule_flag("lt257", rflag) && rewrite(w + ((x + c0)/c1)*c1 < x, (w + c0) < ((x + c0) % c1), c1 > 0, "lt257")) ||
              (get_rule_flag("lt258", rflag) && rewrite(x < ((x + c0)/c1)*c1 + w, ((x + c0) % c1) < w + c0, c1 > 0, "lt258")) ||
              (get_rule_flag("lt259", rflag) && rewrite(x < w + ((x + c0)/c1)*c1, ((x + c0) % c1) < w + c0, c1 > 0, "lt259")) ||

              // c0 = 0
              (get_rule_flag("lt262", rflag) && rewrite((x/c1)*c1 + w < x + z, w < (x % c1) + z, c1 > 0, "lt262")) ||
              (get_rule_flag("lt263", rflag) && rewrite(w + (x/c1)*c1 < x + z, w < (x % c1) + z, c1 > 0, "lt263")) ||
              (get_rule_flag("lt264", rflag) && rewrite((x/c1)*c1 + w < z + x, w < (x % c1) + z, c1 > 0, "lt264")) ||
              (get_rule_flag("lt265", rflag) && rewrite(w + (x/c1)*c1 < z + x, w < (x % c1) + z, c1 > 0, "lt265")) ||
              (get_rule_flag("lt266", rflag) && rewrite(x + z < (x/c1)*c1 + w, (x % c1) + z < w, c1 > 0, "lt266")) ||
              (get_rule_flag("lt267", rflag) && rewrite(x + z < w + (x/c1)*c1, (x % c1) + z < w, c1 > 0, "lt267")) ||
              (get_rule_flag("lt268", rflag) && rewrite(z + x < (x/c1)*c1 + w, (x % c1) + z < w, c1 > 0, "lt268")) ||
              (get_rule_flag("lt269", rflag) && rewrite(z + x < w + (x/c1)*c1, (x % c1) + z < w, c1 > 0, "lt269")) ||

              // w = 0, z = 0
              (get_rule_flag("lt272", rflag) && rewrite(((x + c0)/c1)*c1 < x, c0 < ((x + c0) % c1), c1 > 0, "lt272")) ||
              (get_rule_flag("lt273", rflag) && rewrite(x < ((x + c0)/c1)*c1, ((x + c0) % c1) < c0, c1 > 0, "lt273")) ||

              // w = 0, c0 = 0
              (get_rule_flag("lt276", rflag) && rewrite((x/c1)*c1 < x + z, 0 < (x % c1) + z, c1 > 0, "lt276")) ||
              (get_rule_flag("lt277", rflag) && rewrite((x/c1)*c1 < z + x, 0 < (x % c1) + z, c1 > 0, "lt277")) ||
              (get_rule_flag("lt278", rflag) && rewrite(x + z < (x/c1)*c1, (x % c1) + z < 0, c1 > 0, "lt278")) ||
              (get_rule_flag("lt279", rflag) && rewrite(z + x < (x/c1)*c1, (x % c1) + z < 0, c1 > 0, "lt279")) ||

              // z = 0, c0 = 0
              (get_rule_flag("lt282", rflag) && rewrite((x/c1)*c1 + w < x, w < (x % c1), c1 > 0, "lt282")) ||
              (get_rule_flag("lt283", rflag) && rewrite(w + (x/c1)*c1 < x, w < (x % c1), c1 > 0, "lt283")) ||
              (get_rule_flag("lt284", rflag) && rewrite(x < (x/c1)*c1 + w, (x % c1) < w, c1 > 0, "lt284")) ||
              (get_rule_flag("lt285", rflag) && rewrite(x < w + (x/c1)*c1, (x % c1) < w, c1 > 0, "lt285")) ||

              // z = 0, c0 = 0, w = 0
              (get_rule_flag("lt288", rflag) && rewrite((x/c1)*c1 < x, (x % c1) != 0, c1 > 0, "lt288")) ||
              (get_rule_flag("lt289", rflag) && rewrite(x < (x/c1)*c1, false, c1 > 0, "lt289")) ||

              // Cancel a division
              (get_rule_flag("lt292", rflag) && rewrite((x + c1)/c0 < (x + c2)/c0, false, c0 > 0 && c1 >= c2, "lt292")) ||
              (get_rule_flag("lt293", rflag) && rewrite((x + c1)/c0 < (x + c2)/c0, true, c0 > 0 && c1 <= c2 - c0, "lt293")) ||
              // c1 == 0
              (get_rule_flag("lt295", rflag) && rewrite(x/c0 < (x + c2)/c0, false, c0 > 0 && 0 >= c2, "lt295")) ||
              (get_rule_flag("lt296", rflag) && rewrite(x/c0 < (x + c2)/c0, true, c0 > 0 && 0 <= c2 - c0, "lt296")) ||
              // c2 == 0
              (get_rule_flag("lt298", rflag) && rewrite((x + c1)/c0 < x/c0, false, c0 > 0 && c1 >= 0, "lt298")) ||
              (get_rule_flag("lt299", rflag) && rewrite((x + c1)/c0 < x/c0, true, c0 > 0 && c1 <= 0 - c0, "lt299")) ||

              // The addition on the right could be outside
              (get_rule_flag("lt302", rflag) && rewrite((x + c1)/c0 < x/c0 + c2, false, c0 > 0 && c1 >= c2 * c0, "lt302")) ||
              (get_rule_flag("lt302", rflag) && rewrite((x + c1)/c0 < x/c0 + c2, true, c0 > 0 && c1 <= c2 * c0 - c0, "lt303")) ||

              // With a confounding max or min
              (get_rule_flag("lt306", rflag) && rewrite((x + c1)/c0 < (min(x/c0, y) + c2), false, c0 > 0 && c1 >= c2 * c0, "lt306")) ||
              (get_rule_flag("lt307", rflag) && rewrite((x + c1)/c0 < (max(x/c0, y) + c2), true, c0 > 0 && c1 <= c2 * c0 - c0, "lt307")) ||
              (get_rule_flag("lt308", rflag) && rewrite((x + c1)/c0 < min((x + c2)/c0, y), false, c0 > 0 && c1 >= c2, "lt308")) ||
              (get_rule_flag("lt309", rflag) && rewrite((x + c1)/c0 < max((x + c2)/c0, y), true, c0 > 0 && c1 <= c2 - c0, "lt309")) ||
              (get_rule_flag("lt310", rflag) && rewrite((x + c1)/c0 < min(x/c0, y), false, c0 > 0 && c1 >= 0, "lt310")) ||
              (get_rule_flag("lt311", rflag) && rewrite((x + c1)/c0 < max(x/c0, y), true, c0 > 0 && c1 <= 0 - c0, "lt311")) ||

              (get_rule_flag("lt313", rflag) && rewrite((x + c1)/c0 < (min(y, x/c0) + c2), false, c0 > 0 && c1 >= c2 * c0, "lt313")) ||
              (get_rule_flag("lt314", rflag) && rewrite((x + c1)/c0 < (max(y, x/c0) + c2), true, c0 > 0 && c1 <= c2 * c0 - c0, "lt314")) ||
              (get_rule_flag("lt315", rflag) && rewrite((x + c1)/c0 < min(y, (x + c2)/c0), false, c0 > 0 && c1 >= c2, "lt315")) ||
              (get_rule_flag("lt316", rflag) && rewrite((x + c1)/c0 < max(y, (x + c2)/c0), true, c0 > 0 && c1 <= c2 - c0, "lt316")) ||
              (get_rule_flag("lt317", rflag) && rewrite((x + c1)/c0 < min(y, x/c0), false, c0 > 0 && c1 >= 0, "lt317")) ||
              (get_rule_flag("lt318", rflag) && rewrite((x + c1)/c0 < max(y, x/c0), true, c0 > 0 && c1 <= 0 - c0, "lt318")) ||

              (get_rule_flag("lt320", rflag) && rewrite(max((x + c2)/c0, y) < (x + c1)/c0, false, c0 > 0 && c2 >= c1, "lt320")) ||
              (get_rule_flag("lt321", rflag) && rewrite(min((x + c2)/c0, y) < (x + c1)/c0, true, c0 > 0 && c2 <= c1 - c0, "lt321")) ||
              (get_rule_flag("lt322", rflag) && rewrite(max(x/c0, y) < (x + c1)/c0, false, c0 > 0 && 0 >= c1, "lt322")) ||
              (get_rule_flag("lt323", rflag) && rewrite(min(x/c0, y) < (x + c1)/c0, true, c0 > 0 && 0 <= c1 - c0, "lt323")) ||
              (get_rule_flag("lt324", rflag) && rewrite(max(y, (x + c2)/c0) < (x + c1)/c0, false, c0 > 0 && c2 >= c1, "lt324")) ||
              (get_rule_flag("lt325", rflag) && rewrite(min(y, (x + c2)/c0) < (x + c1)/c0, true, c0 > 0 && c2 <= c1 - c0, "lt325")) ||
              (get_rule_flag("lt326", rflag) && rewrite(max(y, x/c0) < (x + c1)/c0, false, c0 > 0 && 0 >= c1, "lt326")) ||
              (get_rule_flag("lt327", rflag) && rewrite(min(y, x/c0) < (x + c1)/c0, true, c0 > 0 && 0 <= c1 - c0, "lt327")) ||

              // Same as above with c1 outside the division, with redundant cases removed.
              (get_rule_flag("lt330", rflag) && rewrite(max((x + c2)/c0, y) < x/c0 + c1, false, c0 > 0 && c2 >= c1 * c0, "lt330")) ||
              (get_rule_flag("lt331", rflag) && rewrite(min((x + c2)/c0, y) < x/c0 + c1, true, c0 > 0 && c2 <= c1 * c0 - c0, "lt331")) ||
              (get_rule_flag("lt332", rflag) && rewrite(max(y, (x + c2)/c0) < x/c0 + c1, false, c0 > 0 && c2 >= c1 * c0, "lt332")) ||
              (get_rule_flag("lt333", rflag) && rewrite(min(y, (x + c2)/c0) < x/c0 + c1, true, c0 > 0 && c2 <= c1 * c0 - c0, "lt333")) ||

              // Same as above with c1 = 0 and the predicates and redundant cases simplified accordingly.
              (get_rule_flag("lt336", rflag) && rewrite(x/c0 < min((x + c2)/c0, y), false, c0 > 0 && c2 < 0, "lt336")) ||
              (get_rule_flag("lt337", rflag) && rewrite(x/c0 < max((x + c2)/c0, y), true, c0 > 0 && c0 <= c2, "lt337")) ||
              (get_rule_flag("lt338", rflag) && rewrite(x/c0 < min(y, (x + c2)/c0), false, c0 > 0 && c2 < 0, "lt338")) ||
              (get_rule_flag("lt339", rflag) && rewrite(x/c0 < max(y, (x + c2)/c0), true, c0 > 0 && c0 <= c2, "lt339")) ||
              (get_rule_flag("lt340", rflag) && rewrite(max((x + c2)/c0, y) < x/c0, false, c0 > 0 && c2 >= 0, "lt340")) ||
              (get_rule_flag("lt341", rflag) && rewrite(min((x + c2)/c0, y) < x/c0, true, c0 > 0 && c2 + c0 <= 0, "lt341")) ||
              (get_rule_flag("lt342", rflag) && rewrite(max(y, (x + c2)/c0) < x/c0, false, c0 > 0 && c2 >= 0, "lt342")) ||
              (get_rule_flag("lt343", rflag) && rewrite(min(y, (x + c2)/c0) < x/c0, true, c0 > 0 && c2 + c0 <= 0, "lt343")) ||

              // Comparison of two mins/maxes that don't cancel when subtracted
              (get_rule_flag("lt346", rflag) && rewrite(min(x, c0) < min(x, c1), false, c0 >= c1, "lt346")) ||
              (get_rule_flag("lt347", rflag) && rewrite(min(x, c0) < min(x, c1) + c2, false, c0 >= c1 + c2 && c2 <= 0, "lt347")) ||
              (get_rule_flag("lt348", rflag) && rewrite(max(x, c0) < max(x, c1), false, c0 >= c1, "lt348")) ||
              (get_rule_flag("lt349", rflag) && rewrite(max(x, c0) < max(x, c1) + c2, false, c0 >= c1 + c2 && c2 <= 0, "lt349")) ||

              // Comparison of aligned ramps can simplify to a comparison of the base
              (get_rule_flag("lt352", rflag) && rewrite(ramp(x * c3 + c2, c1) < broadcast(z * c0),
                      broadcast(x * fold(c3/c0) + fold(c2/c0) < z, lanes),
                      c0 > 0 && (c3 % c0 == 0) &&
                      (c2 % c0) + c1 * (lanes - 1) < c0 &&
                      (c2 % c0) + c1 * (lanes - 1) >= 0, "lt352")) ||
              // c2 = 0
              (get_rule_flag("lt358", rflag) && rewrite(ramp(x * c3, c1) < broadcast(z * c0),
                      broadcast(x * fold(c3/c0) < z, lanes),
                      c0 > 0 && (c3 % c0 == 0) &&
                      c1 * (lanes - 1) < c0 &&
                      c1 * (lanes - 1) >= 0, "lt358"))))) {
            return mutate(std::move(rewrite.result), bounds);
        }
        // clang-format on
    }

    if (a.same_as(op->a) && b.same_as(op->b)) {
        return op;
    } else {
        return LT::make(a, b);
    }
}

// The other comparison operators redirect to the less-than operator
Expr Simplify::visit(const LE *op, ExprInfo *bounds) {
    if (!may_simplify(op->a.type())) {
        Expr a = mutate(op->a, nullptr);
        Expr b = mutate(op->b, nullptr);
        if (a.same_as(op->a) && b.same_as(op->b)) {
            return op;
        } else {
            return LE::make(a, b);
        }
    }

    Expr mutated = mutate(!(op->b < op->a), bounds);
    if (const LE *le = mutated.as<LE>()) {
        if (le->a.same_as(op->a) && le->b.same_as(op->b)) {
            return op;
        }
    }
    return mutated;
}

Expr Simplify::visit(const GT *op, ExprInfo *bounds) {
    if (!may_simplify(op->a.type())) {
        Expr a = mutate(op->a, nullptr);
        Expr b = mutate(op->b, nullptr);
        if (a.same_as(op->a) && b.same_as(op->b)) {
            return op;
        } else {
            return GT::make(a, b);
        }
    }

    return mutate(op->b < op->a, bounds);
}

Expr Simplify::visit(const GE *op, ExprInfo *bounds) {
    if (!may_simplify(op->a.type())) {
        Expr a = mutate(op->a, nullptr);
        Expr b = mutate(op->b, nullptr);
        if (a.same_as(op->a) && b.same_as(op->b)) {
            return op;
        } else {
            return GE::make(a, b);
        }
    }

    return mutate(!(op->a < op->b), bounds);
}

}  // namespace Internal
}  // namespace Halide