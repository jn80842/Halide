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

        if (EVAL_IN_LAMBDA
            ((get_rule_flag("lt34", rflag) && rewrite(c0 < c1, fold(c0 < c1), "lt34")) ||
             (get_rule_flag("lt35", rflag) && rewrite(x < x, false, "lt35")) ||
             (get_rule_flag("lt36", rflag) && rewrite(x < ty.min(), false, "lt36")) ||
             (get_rule_flag("lt37", rflag) && rewrite(ty.max() < x, false, "lt37")) ||

             (get_rule_flag("lt39", rflag) && rewrite(max(x, y) < x, false, "lt39")) ||
             (get_rule_flag("lt40", rflag) && rewrite(max(y, x) < x, false, "lt40")) ||
             (get_rule_flag("lt41", rflag) && rewrite(x < min(x, y), false, "lt41")) ||
             (get_rule_flag("lt42", rflag) && rewrite(x < min(y, x), false, "lt42")) ||

             // Comparisons of ramps and broadcasts. If the first
             // and last lanes are provably < or >= the broadcast
             // we can collapse the comparison.
             (no_overflow(op->type) &&
              ((get_rule_flag("lt48", rflag) && rewrite(ramp(x, c1) < broadcast(z), true, can_prove(x + fold(max(0, c1 * (lanes - 1))) < z, this), "lt48")) ||
               (get_rule_flag("lt49", rflag) && rewrite(ramp(x, c1) < broadcast(z), false, can_prove(x + fold(min(0, c1 * (lanes - 1))) >= z, this), "lt49")) ||
               (get_rule_flag("lt50", rflag) && rewrite(broadcast(z) < ramp(x, c1), true, can_prove(z < x + fold(min(0, c1 * (lanes - 1))), this), "lt50")) ||
               (get_rule_flag("lt51", rflag) && rewrite(broadcast(z) < ramp(x, c1), false, can_prove(z >= x + fold(max(0, c1 * (lanes - 1))), this), "lt51")))))) {
            return rewrite.result;
        }

        if ((get_rule_flag("lt55", rflag) && rewrite(broadcast(x) < broadcast(y), broadcast(x < y, lanes), "lt55")) ||
            (no_overflow(ty) && EVAL_IN_LAMBDA
             ((get_rule_flag("lt57", rflag) && rewrite(ramp(x, y) < ramp(z, y), broadcast(x < z, lanes), "lt57")) ||
              // Merge RHS constant additions with a constant LHS
              (get_rule_flag("lt59", rflag) && rewrite(x + c0 < c1, x < fold(c1 - c0), "lt59")) ||
              (get_rule_flag("lt60", rflag) && rewrite(c0 < x + c1, fold(c0 - c1) < x, "lt60")) ||

              // Move constants to the RHS
              (get_rule_flag("lt63", rflag) && rewrite(x + c0 < y, x < y + fold(-c0), "lt63")) ||
              // Normalize subtractions to additions to cut down on cases to consider
              (get_rule_flag("lt65", rflag) && rewrite(x - y < z, x < z + y, "lt65")) ||
              (get_rule_flag("lt66", rflag) && rewrite(z < x - y, z + y < x, "lt66")) ||
              (get_rule_flag("lt67", rflag) && rewrite((x - y) + z < w, x + z < y + w, "lt67")) ||
              (get_rule_flag("lt68", rflag) && rewrite(z + (x - y) < w, x + z < y + w, "lt68")) ||
              (get_rule_flag("lt69", rflag) && rewrite(w < (x - y) + z, w + y < x + z, "lt69")) ||
              (get_rule_flag("lt70", rflag) && rewrite(w < z + (x - y), w + y < x + z, "lt70")) ||
              (get_rule_flag("lt71", rflag) && rewrite(((x - y) + z) + u < w, x + z + u < w + y, "lt71")) ||
              (get_rule_flag("lt72", rflag) && rewrite((z + (x - y)) + u < w, x + z + u < w + y, "lt72")) ||
              (get_rule_flag("lt73", rflag) && rewrite(u + ((x - y) + z) < w, x + z + u < w + y, "lt73")) ||
              (get_rule_flag("lt74", rflag) && rewrite(u + (z + (x - y)) < w, x + z + u < w + y, "lt74")) ||
              (get_rule_flag("lt75", rflag) && rewrite(w < ((x - y) + z) + u, w + y < x + z + u, "lt75")) ||
              (get_rule_flag("lt76", rflag) && rewrite(w < (z + (x - y)) + u, w + y < x + z + u, "lt76")) ||
              (get_rule_flag("lt77", rflag) && rewrite(w < u + ((x - y) + z), w + y < x + z + u, "lt77")) ||
              (get_rule_flag("lt78", rflag) && rewrite(w < u + (z + (x - y)), w + y < x + z + u, "lt78")) ||
              // Cancellations in linear expressions
              // 1 < 2
              (get_rule_flag("lt81", rflag) && rewrite(x < x + y, 0 < y, "lt81")) ||
              (get_rule_flag("lt82", rflag) && rewrite(x < y + x, 0 < y, "lt82")) ||

              // 2 < 1
              (get_rule_flag("lt85", rflag) && rewrite(x + y < x, y < 0, "lt85")) ||
              (get_rule_flag("lt86", rflag) && rewrite(y + x < x, y < 0, "lt86")) ||

              // 2 < 2
              (get_rule_flag("lt89", rflag) && rewrite(x + y < x + z, y < z, "lt89")) ||
              (get_rule_flag("lt90", rflag) && rewrite(x + y < z + x, y < z, "lt90")) ||
              (get_rule_flag("lt91", rflag) && rewrite(y + x < x + z, y < z, "lt91")) ||
              (get_rule_flag("lt92", rflag) && rewrite(y + x < z + x, y < z, "lt92")) ||

              // 3 < 2
              (get_rule_flag("lt95", rflag) && rewrite((x + y) + w < x + z, y + w < z, "lt95")) ||
              (get_rule_flag("lt96", rflag) && rewrite((y + x) + w < x + z, y + w < z, "lt96")) ||
              (get_rule_flag("lt97", rflag) && rewrite(w + (x + y) < x + z, y + w < z, "lt97")) ||
              (get_rule_flag("lt98", rflag) && rewrite(w + (y + x) < x + z, y + w < z, "lt98")) ||
              (get_rule_flag("lt99", rflag) && rewrite((x + y) + w < z + x, y + w < z, "lt99")) ||
              (get_rule_flag("lt100", rflag) && rewrite((y + x) + w < z + x, y + w < z, "lt100")) ||
              (get_rule_flag("lt101", rflag) && rewrite(w + (x + y) < z + x, y + w < z, "lt101")) ||
              (get_rule_flag("lt102", rflag) && rewrite(w + (y + x) < z + x, y + w < z, "lt102")) ||

              // 2 < 3
              (get_rule_flag("lt105", rflag) && rewrite(x + z < (x + y) + w, z < y + w, "lt105")) ||
              (get_rule_flag("lt106", rflag) && rewrite(x + z < (y + x) + w, z < y + w, "lt106")) ||
              (get_rule_flag("lt107", rflag) && rewrite(x + z < w + (x + y), z < y + w, "lt107")) ||
              (get_rule_flag("lt108", rflag) && rewrite(x + z < w + (y + x), z < y + w, "lt108")) ||
              (get_rule_flag("lt109", rflag) && rewrite(z + x < (x + y) + w, z < y + w, "lt109")) ||
              (get_rule_flag("lt110", rflag) && rewrite(z + x < (y + x) + w, z < y + w, "lt110")) ||
              (get_rule_flag("lt111", rflag) && rewrite(z + x < w + (x + y), z < y + w, "lt111")) ||
              (get_rule_flag("lt112", rflag) && rewrite(z + x < w + (y + x), z < y + w, "lt112")) ||

              // 3 < 3
              (get_rule_flag("lt115", rflag) && rewrite((x + y) + w < (x + z) + u, y + w < z + u, "lt115")) ||
              (get_rule_flag("lt116", rflag) && rewrite((y + x) + w < (x + z) + u, y + w < z + u, "lt116")) ||
              (get_rule_flag("lt117", rflag) && rewrite((x + y) + w < (z + x) + u, y + w < z + u, "lt117")) ||
              (get_rule_flag("lt118", rflag) && rewrite((y + x) + w < (z + x) + u, y + w < z + u, "lt118")) ||
              (get_rule_flag("lt119", rflag) && rewrite(w + (x + y) < (x + z) + u, y + w < z + u, "lt119")) ||
              (get_rule_flag("lt120", rflag) && rewrite(w + (y + x) < (x + z) + u, y + w < z + u, "lt120")) ||
              (get_rule_flag("lt121", rflag) && rewrite(w + (x + y) < (z + x) + u, y + w < z + u, "lt121")) ||
              (get_rule_flag("lt122", rflag) && rewrite(w + (y + x) < (z + x) + u, y + w < z + u, "lt122")) ||
              (get_rule_flag("lt123", rflag) && rewrite((x + y) + w < u + (x + z), y + w < z + u, "lt123")) ||
              (get_rule_flag("lt124", rflag) && rewrite((y + x) + w < u + (x + z), y + w < z + u, "lt124")) ||
              (get_rule_flag("lt125", rflag) && rewrite((x + y) + w < u + (z + x), y + w < z + u, "lt125")) ||
              (get_rule_flag("lt126", rflag) && rewrite((y + x) + w < u + (z + x), y + w < z + u, "lt126")) ||
              (get_rule_flag("lt127", rflag) && rewrite(w + (x + y) < u + (x + z), y + w < z + u, "lt127")) ||
              (get_rule_flag("lt128", rflag) && rewrite(w + (y + x) < u + (x + z), y + w < z + u, "lt128")) ||
              (get_rule_flag("lt129", rflag) && rewrite(w + (x + y) < u + (z + x), y + w < z + u, "lt129")) ||
              (get_rule_flag("lt130", rflag) && rewrite(w + (y + x) < u + (z + x), y + w < z + u, "lt130")) ||

              // Cancel a multiplication
              (get_rule_flag("lt133", rflag) && rewrite(x * c0 < y * c0, x < y, c0 > 0, "lt133")) ||
              (get_rule_flag("lt134", rflag) && rewrite(x * c0 < y * c0, y < x, c0 < 0, "lt134")) ||

              (ty.is_int()   && (get_rule_flag("lt136", rflag) && rewrite(x * c0 < c1, x < fold((c1 + c0 - 1) / c0), c0 > 0, "lt136"))) ||
              (ty.is_float() && (get_rule_flag("lt137", rflag) && rewrite(x * c0 < c1, x < fold(c1 / c0), c0 > 0, "lt137"))) ||
              (get_rule_flag("lt138", rflag) && rewrite(c1 < x * c0, fold(c1 / c0) < x, c0 > 0, "lt138")) ||

              // Multiply-out a division
              (get_rule_flag("lt141", rflag) && rewrite(x / c0 < c1, x < c1 * c0, c0 > 0, "lt141")) ||
              (ty.is_int() && (get_rule_flag("lt142", rflag) && rewrite(c0 < x / c1, fold((c0 + 1) * c1 - 1) < x, c1 > 0, "lt142"))) ||
              (ty.is_float() && (get_rule_flag("lt143", rflag) && rewrite(c0 < x / c1, fold(c0 * c1) < x, c1 > 0, "lt143"))) ||

              // We want to break max(x, y) < z into x < z && y <
              // z in cases where one of those two terms is going
              // to fold.
              (get_rule_flag("lt148", rflag) && rewrite(min(x + c0, y) < x + c1, fold(c0 < c1) || y < x + c1, "lt148")) ||
              (get_rule_flag("lt149", rflag) && rewrite(min(y, x + c0) < x + c1, fold(c0 < c1) || y < x + c1, "lt149")) ||
              (get_rule_flag("lt150", rflag) && rewrite(max(x + c0, y) < x + c1, fold(c0 < c1) && y < x + c1, "lt150")) ||
              (get_rule_flag("lt151", rflag) && rewrite(max(y, x + c0) < x + c1, fold(c0 < c1) && y < x + c1, "lt151")) ||

              (get_rule_flag("lt153", rflag) && rewrite(x < min(x + c0, y) + c1, fold(0 < c0 + c1) && x < y + c1, "lt153")) ||
              (get_rule_flag("lt154", rflag) && rewrite(x < min(y, x + c0) + c1, fold(0 < c0 + c1) && x < y + c1, "lt154")) ||
              (get_rule_flag("lt155", rflag) && rewrite(x < max(x + c0, y) + c1, fold(0 < c0 + c1) || x < y + c1, "lt155")) ||
              (get_rule_flag("lt156", rflag) && rewrite(x < max(y, x + c0) + c1, fold(0 < c0 + c1) || x < y + c1, "lt156")) ||

              // Special cases where c0 == 0
              (get_rule_flag("lt159", rflag) && rewrite(min(x, y) < x + c1, fold(0 < c1) || y < x + c1, "lt159")) ||
              (get_rule_flag("lt160", rflag) && rewrite(min(y, x) < x + c1, fold(0 < c1) || y < x + c1, "lt160")) ||
              (get_rule_flag("lt161", rflag) && rewrite(max(x, y) < x + c1, fold(0 < c1) && y < x + c1, "lt161")) ||
              (get_rule_flag("lt162", rflag) && rewrite(max(y, x) < x + c1, fold(0 < c1) && y < x + c1, "lt162")) ||

              (get_rule_flag("lt164", rflag) && rewrite(x < min(x, y) + c1, fold(0 < c1) && x < y + c1, "lt164")) ||
              (get_rule_flag("lt165", rflag) && rewrite(x < min(y, x) + c1, fold(0 < c1) && x < y + c1, "lt165")) ||
              (get_rule_flag("lt166", rflag) && rewrite(x < max(x, y) + c1, fold(0 < c1) || x < y + c1, "lt166")) ||
              (get_rule_flag("lt167", rflag) && rewrite(x < max(y, x) + c1, fold(0 < c1) || x < y + c1, "lt167")) ||

              // Special cases where c1 == 0
              (get_rule_flag("lt170", rflag) && rewrite(min(x + c0, y) < x, fold(c0 < 0) || y < x, "lt170")) ||
              (get_rule_flag("lt171", rflag) && rewrite(min(y, x + c0) < x, fold(c0 < 0) || y < x, "lt171")) ||
              (get_rule_flag("lt172", rflag) && rewrite(max(x + c0, y) < x, fold(c0 < 0) && y < x, "lt172")) ||
              (get_rule_flag("lt173", rflag) && rewrite(max(y, x + c0) < x, fold(c0 < 0) && y < x, "lt173")) ||

              (get_rule_flag("lt175", rflag) && rewrite(x < min(x + c0, y), fold(0 < c0) && x < y, "lt175")) ||
              (get_rule_flag("lt176", rflag) && rewrite(x < min(y, x + c0), fold(0 < c0) && x < y, "lt176")) ||
              (get_rule_flag("lt177", rflag) && rewrite(x < max(x + c0, y), fold(0 < c0) || x < y, "lt177")) ||
              (get_rule_flag("lt178", rflag) && rewrite(x < max(y, x + c0), fold(0 < c0) || x < y, "lt178")) ||

              // Special cases where c0 == c1 == 0
              (get_rule_flag("lt181", rflag) && rewrite(min(x, y) < x, y < x, "lt181")) ||
              (get_rule_flag("lt182", rflag) && rewrite(min(y, x) < x, y < x, "lt182")) ||
              (get_rule_flag("lt183", rflag) && rewrite(x < max(x, y), x < y, "lt183")) ||
              (get_rule_flag("lt184", rflag) && rewrite(x < max(y, x), x < y, "lt184")) ||

              // Special case where x is constant
              (get_rule_flag("lt187", rflag) && rewrite(min(y, c0) < c1, fold(c0 < c1) || y < c1, "lt187")) ||
              (get_rule_flag("lt188", rflag) && rewrite(max(y, c0) < c1, fold(c0 < c1) && y < c1, "lt188")) ||
              (get_rule_flag("lt189", rflag) && rewrite(c1 < min(y, c0), fold(c1 < c0) && c1 < y, "lt189")) ||
              (get_rule_flag("lt190", rflag) && rewrite(c1 < max(y, c0), fold(c1 < c0) || c1 < y, "lt190")) ||

              // Comparisons with selects:
              // x < select(c, t, f) == c && (x < t) || !c && (x < f)
              // This is profitable when x < t or x < f is statically provable
              (get_rule_flag("lt195", rflag) && rewrite(x < select(y, x + c0, z), !y && (x < z), c0 <= 0, "lt195")) ||
              (get_rule_flag("lt196", rflag) && rewrite(x < select(y, x + c0, z), y || (x < z), c0 > 0, "lt196")) ||
              (get_rule_flag("lt197", rflag) && rewrite(x < select(y, z, x + c0), y && (x < z), c0 <= 0, "lt197")) ||
              (get_rule_flag("lt198", rflag) && rewrite(x < select(y, z, x + c0), !y || (x < z), c0 > 0, "lt198")) ||

              (get_rule_flag("lt200", rflag) && rewrite(x < select(y, x + c0, z) + c1, !y && (x < z + c1), c0 + c1 <= 0, "lt200")) ||
              (get_rule_flag("lt201", rflag) && rewrite(x < select(y, x + c0, z) + c1, y || (x < z + c1), c0 + c1 > 0, "lt201")) ||
              (get_rule_flag("lt202", rflag) && rewrite(x < select(y, z, x + c0) + c1, y && (x < z + c1), c0 + c1 <= 0, "lt202")) ||
              (get_rule_flag("lt203", rflag) && rewrite(x < select(y, z, x + c0) + c1, !y || (x < z + c1), c0 + c1 > 0, "lt203")) ||

              (get_rule_flag("lt205", rflag) && rewrite(select(y, x + c0, z) < x, !y && (z < x), c0 >= 0, "lt205")) ||
              (get_rule_flag("lt206", rflag) && rewrite(select(y, x + c0, z) < x, y || (z < x), c0 < 0, "lt206")) ||
              (get_rule_flag("lt207", rflag) && rewrite(select(y, z, x + c0) < x, y && (z < x), c0 >= 0, "lt207")) ||
              (get_rule_flag("lt208", rflag) && rewrite(select(y, z, x + c0) < x, !y || (z < x), c0 < 0, "lt208")) ||

              (get_rule_flag("lt210", rflag) && rewrite(select(y, x + c0, z) < x + c1, !y && (z < x + c1), c0 >= c1, "lt210")) ||
              (get_rule_flag("lt211", rflag) && rewrite(select(y, x + c0, z) < x + c1, y || (z < x + c1), c0 < c1, "lt211")) ||
              (get_rule_flag("lt212", rflag) && rewrite(select(y, z, x + c0) < x + c1, y && (z < x + c1), c0 >= c1, "lt212")) ||
              (get_rule_flag("lt213", rflag) && rewrite(select(y, z, x + c0) < x + c1, !y || (z < x + c1), c0 < c1, "lt213")) ||

              // Normalize comparison of ramps to a comparison of a ramp and a broadacst
              (get_rule_flag("lt216", rflag) && rewrite(ramp(x, y) < ramp(z, w), ramp(x - z, y - w, lanes) < 0, "lt216")))) ||

            (no_overflow_int(ty) && EVAL_IN_LAMBDA
             ((get_rule_flag("lt219", rflag) && rewrite(x * c0 < y * c1, x < y * fold(c1 / c0), c1 % c0 == 0 && c0 > 0, "lt219")) ||
              (get_rule_flag("lt220", rflag) && rewrite(x * c0 < y * c1, x * fold(c0 / c1) < y, c0 % c1 == 0 && c1 > 0, "lt220")) ||

              (get_rule_flag("lt222", rflag) && rewrite(x * c0 < y * c0 + c1, x < y + fold((c1 + c0 - 1)/c0), c0 > 0, "lt222")) ||
              (get_rule_flag("lt223", rflag) && rewrite(x * c0 + c1 < y * c0, x + fold(c1/c0) < y, c0 > 0, "lt223")) ||

              // Comparison of stair-step functions. The basic transformation is:
              //   ((x + y)/c1)*c1 < x
              // = (x + y) - (x + y) % c1 < x (when c1 > 0)
              // = y - (x + y) % c1 < 0
              // = y < (x + y) % c1
              // This cancels x but duplicates y, so we only do it when y is a constant.

              // A more general version with extra terms w and z
              (get_rule_flag("lt233", rflag) && rewrite(((x + c0)/c1)*c1 + w < x + z, (w + c0) < ((x + c0) % c1) + z, c1 > 0, "lt233")) ||
              (get_rule_flag("lt234", rflag) && rewrite(w + ((x + c0)/c1)*c1 < x + z, (w + c0) < ((x + c0) % c1) + z, c1 > 0, "lt234")) ||
              (get_rule_flag("lt235", rflag) && rewrite(((x + c0)/c1)*c1 + w < z + x, (w + c0) < ((x + c0) % c1) + z, c1 > 0, "lt235")) ||
              (get_rule_flag("lt236", rflag) && rewrite(w + ((x + c0)/c1)*c1 < z + x, (w + c0) < ((x + c0) % c1) + z, c1 > 0, "lt236")) ||
              (get_rule_flag("lt237", rflag) && rewrite(x + z < ((x + c0)/c1)*c1 + w, ((x + c0) % c1) + z < w + c0, c1 > 0, "lt237")) ||
              (get_rule_flag("lt238", rflag) && rewrite(x + z < w + ((x + c0)/c1)*c1, ((x + c0) % c1) + z < w + c0, c1 > 0, "lt238")) ||
              (get_rule_flag("lt239", rflag) && rewrite(z + x < ((x + c0)/c1)*c1 + w, ((x + c0) % c1) + z < w + c0, c1 > 0, "lt239")) ||
              (get_rule_flag("lt240", rflag) && rewrite(z + x < w + ((x + c0)/c1)*c1, ((x + c0) % c1) + z < w + c0, c1 > 0, "lt240")) ||

              // w = 0
              (get_rule_flag("lt243", rflag) && rewrite(((x + c0)/c1)*c1 < x + z, c0 < ((x + c0) % c1) + z, c1 > 0, "lt243")) ||
              (get_rule_flag("lt244", rflag) && rewrite(((x + c0)/c1)*c1 < z + x, c0 < ((x + c0) % c1) + z, c1 > 0, "lt244")) ||
              (get_rule_flag("lt245", rflag) && rewrite(x + z < ((x + c0)/c1)*c1, ((x + c0) % c1) + z < c0, c1 > 0, "lt245")) ||
              (get_rule_flag("lt246", rflag) && rewrite(z + x < ((x + c0)/c1)*c1, ((x + c0) % c1) + z < c0, c1 > 0, "lt246")) ||

              // z = 0
              (get_rule_flag("lt249", rflag) && rewrite(((x + c0)/c1)*c1 + w < x, (w + c0) < ((x + c0) % c1), c1 > 0, "lt249")) ||
              (get_rule_flag("lt250", rflag) && rewrite(w + ((x + c0)/c1)*c1 < x, (w + c0) < ((x + c0) % c1), c1 > 0, "lt250")) ||
              (get_rule_flag("lt251", rflag) && rewrite(x < ((x + c0)/c1)*c1 + w, ((x + c0) % c1) < w + c0, c1 > 0, "lt251")) ||
              (get_rule_flag("lt252", rflag) && rewrite(x < w + ((x + c0)/c1)*c1, ((x + c0) % c1) < w + c0, c1 > 0, "lt252")) ||

              // c0 = 0
              (get_rule_flag("lt255", rflag) && rewrite((x/c1)*c1 + w < x + z, w < (x % c1) + z, c1 > 0, "lt255")) ||
              (get_rule_flag("lt256", rflag) && rewrite(w + (x/c1)*c1 < x + z, w < (x % c1) + z, c1 > 0, "lt256")) ||
              (get_rule_flag("lt257", rflag) && rewrite((x/c1)*c1 + w < z + x, w < (x % c1) + z, c1 > 0, "lt257")) ||
              (get_rule_flag("lt258", rflag) && rewrite(w + (x/c1)*c1 < z + x, w < (x % c1) + z, c1 > 0, "lt258")) ||
              (get_rule_flag("lt259", rflag) && rewrite(x + z < (x/c1)*c1 + w, (x % c1) + z < w, c1 > 0, "lt259")) ||
              (get_rule_flag("lt260", rflag) && rewrite(x + z < w + (x/c1)*c1, (x % c1) + z < w, c1 > 0, "lt260")) ||
              (get_rule_flag("lt261", rflag) && rewrite(z + x < (x/c1)*c1 + w, (x % c1) + z < w, c1 > 0, "lt261")) ||
              (get_rule_flag("lt262", rflag) && rewrite(z + x < w + (x/c1)*c1, (x % c1) + z < w, c1 > 0, "lt262")) ||

              // w = 0, z = 0
              (get_rule_flag("lt265", rflag) && rewrite(((x + c0)/c1)*c1 < x, c0 < ((x + c0) % c1), c1 > 0, "lt265")) ||
              (get_rule_flag("lt266", rflag) && rewrite(x < ((x + c0)/c1)*c1, ((x + c0) % c1) < c0, c1 > 0, "lt266")) ||

              // w = 0, c0 = 0
              (get_rule_flag("lt269", rflag) && rewrite((x/c1)*c1 < x + z, 0 < (x % c1) + z, c1 > 0, "lt269")) ||
              (get_rule_flag("lt270", rflag) && rewrite((x/c1)*c1 < z + x, 0 < (x % c1) + z, c1 > 0, "lt270")) ||
              (get_rule_flag("lt271", rflag) && rewrite(x + z < (x/c1)*c1, (x % c1) + z < 0, c1 > 0, "lt271")) ||
              (get_rule_flag("lt272", rflag) && rewrite(z + x < (x/c1)*c1, (x % c1) + z < 0, c1 > 0, "lt272")) ||

              // z = 0, c0 = 0
              (get_rule_flag("lt275", rflag) && rewrite((x/c1)*c1 + w < x, w < (x % c1), c1 > 0, "lt275")) ||
              (get_rule_flag("lt276", rflag) && rewrite(w + (x/c1)*c1 < x, w < (x % c1), c1 > 0, "lt276")) ||
              (get_rule_flag("lt277", rflag) && rewrite(x < (x/c1)*c1 + w, (x % c1) < w, c1 > 0, "lt277")) ||
              (get_rule_flag("lt278", rflag) && rewrite(x < w + (x/c1)*c1, (x % c1) < w, c1 > 0, "lt278")) ||

              // z = 0, c0 = 0, w = 0
              (get_rule_flag("lt281", rflag) && rewrite((x/c1)*c1 < x, (x % c1) != 0, c1 > 0, "lt281")) ||
              (get_rule_flag("lt282", rflag) && rewrite(x < (x/c1)*c1, false, c1 > 0, "lt282")) ||

              // Cancel a division
              (get_rule_flag("lt285", rflag) && rewrite((x + c1)/c0 < (x + c2)/c0, false, c0 > 0 && c1 >= c2, "lt285")) ||
              (get_rule_flag("lt286", rflag) && rewrite((x + c1)/c0 < (x + c2)/c0, true, c0 > 0 && c1 <= c2 - c0, "lt286")) ||
              // c1 == 0
              (get_rule_flag("lt288", rflag) && rewrite(x/c0 < (x + c2)/c0, false, c0 > 0 && 0 >= c2, "lt288")) ||
              (get_rule_flag("lt289", rflag) && rewrite(x/c0 < (x + c2)/c0, true, c0 > 0 && 0 <= c2 - c0, "lt289")) ||
              // c2 == 0
              (get_rule_flag("lt291", rflag) && rewrite((x + c1)/c0 < x/c0, false, c0 > 0 && c1 >= 0, "lt291")) ||
              (get_rule_flag("lt292", rflag) && rewrite((x + c1)/c0 < x/c0, true, c0 > 0 && c1 <= 0 - c0, "lt292")) ||

              // The addition on the right could be outside
              (get_rule_flag("lt295", rflag) && rewrite((x + c1)/c0 < x/c0 + c2, false, c0 > 0 && c1 >= c2 * c0, "lt295")) ||
              (get_rule_flag("lt296", rflag) && rewrite((x + c1)/c0 < x/c0 + c2, true, c0 > 0 && c1 <= c2 * c0 - c0, "lt296")) ||

              // With a confounding max or min
              (get_rule_flag("lt299", rflag) && rewrite((x + c1)/c0 < (min(x/c0, y) + c2), false, c0 > 0 && c1 >= c2 * c0, "lt299")) ||
              (get_rule_flag("lt300", rflag) && rewrite((x + c1)/c0 < (max(x/c0, y) + c2), true, c0 > 0 && c1 <= c2 * c0 - c0, "lt300")) ||
              (get_rule_flag("lt301", rflag) && rewrite((x + c1)/c0 < min((x + c2)/c0, y), false, c0 > 0 && c1 >= c2, "lt301")) ||
              (get_rule_flag("lt302", rflag) && rewrite((x + c1)/c0 < max((x + c2)/c0, y), true, c0 > 0 && c1 <= c2 - c0, "lt302")) ||
              (get_rule_flag("lt303", rflag) && rewrite((x + c1)/c0 < min(x/c0, y), false, c0 > 0 && c1 >= 0, "lt303")) ||
              (get_rule_flag("lt304", rflag) && rewrite((x + c1)/c0 < max(x/c0, y), true, c0 > 0 && c1 <= 0 - c0, "lt304")) ||

              (get_rule_flag("lt306", rflag) && rewrite((x + c1)/c0 < (min(y, x/c0) + c2), false, c0 > 0 && c1 >= c2 * c0, "lt306")) ||
              (get_rule_flag("lt307", rflag) && rewrite((x + c1)/c0 < (max(y, x/c0) + c2), true, c0 > 0 && c1 <= c2 * c0 - c0, "lt307")) ||
              (get_rule_flag("lt308", rflag) && rewrite((x + c1)/c0 < min(y, (x + c2)/c0), false, c0 > 0 && c1 >= c2, "lt308")) ||
              (get_rule_flag("lt309", rflag) && rewrite((x + c1)/c0 < max(y, (x + c2)/c0), true, c0 > 0 && c1 <= c2 - c0, "lt309")) ||
              (get_rule_flag("lt310", rflag) && rewrite((x + c1)/c0 < min(y, x/c0), false, c0 > 0 && c1 >= 0, "lt310")) ||
              (get_rule_flag("lt311", rflag) && rewrite((x + c1)/c0 < max(y, x/c0), true, c0 > 0 && c1 <= 0 - c0, "lt311")) ||

              (get_rule_flag("lt313", rflag) && rewrite(max((x + c2)/c0, y) < (x + c1)/c0, false, c0 > 0 && c2 >= c1, "lt313")) ||
              (get_rule_flag("lt314", rflag) && rewrite(min((x + c2)/c0, y) < (x + c1)/c0, true, c0 > 0 && c2 <= c1 - c0, "lt314")) ||
              (get_rule_flag("lt315", rflag) && rewrite(max(x/c0, y) < (x + c1)/c0, false, c0 > 0 && 0 >= c1, "lt315")) ||
              (get_rule_flag("lt316", rflag) && rewrite(min(x/c0, y) < (x + c1)/c0, true, c0 > 0 && 0 <= c1 - c0, "lt316")) ||
              (get_rule_flag("lt317", rflag) && rewrite(max(y, (x + c2)/c0) < (x + c1)/c0, false, c0 > 0 && c2 >= c1, "lt317")) ||
              (get_rule_flag("lt318", rflag) && rewrite(min(y, (x + c2)/c0) < (x + c1)/c0, true, c0 > 0 && c2 <= c1 - c0, "lt318")) ||
              (get_rule_flag("lt319", rflag) && rewrite(max(y, x/c0) < (x + c1)/c0, false, c0 > 0 && 0 >= c1, "lt319")) ||
              (get_rule_flag("lt320", rflag) && rewrite(min(y, x/c0) < (x + c1)/c0, true, c0 > 0 && 0 <= c1 - c0, "lt320")) ||

              // Same as above with c1 outside the division, with redundant cases removed.
              (get_rule_flag("lt323", rflag) && rewrite(max((x + c2)/c0, y) < x/c0 + c1, false, c0 > 0 && c2 >= c1 * c0, "lt323")) ||
              (get_rule_flag("lt324", rflag) && rewrite(min((x + c2)/c0, y) < x/c0 + c1, true, c0 > 0 && c2 <= c1 * c0 - c0, "lt324")) ||
              (get_rule_flag("lt325", rflag) && rewrite(max(y, (x + c2)/c0) < x/c0 + c1, false, c0 > 0 && c2 >= c1 * c0, "lt325")) ||
              (get_rule_flag("lt326", rflag) && rewrite(min(y, (x + c2)/c0) < x/c0 + c1, true, c0 > 0 && c2 <= c1 * c0 - c0, "lt326")) ||

              // Same as above with c1 = 0 and the predicates and redundant cases simplified accordingly.
              (rewrite(x/c0 < min((x + c2)/c0, y), false, c0 > 0 && c2 < 0, "lt329")) ||
              (rewrite(x/c0 < max((x + c2)/c0, y), true, c0 > 0 && c0 <= c2, "lt330")) ||
              (rewrite(x/c0 < min(y, (x + c2)/c0), false, c0 > 0 && c2 < 0, "lt331")) ||
              (rewrite(x/c0 < max(y, (x + c2)/c0), true, c0 > 0 && c0 <= c2, "lt332")) ||
              (rewrite(max((x + c2)/c0, y) < x/c0, false, c0 > 0 && c2 >= 0, "lt333")) ||
              (rewrite(min((x + c2)/c0, y) < x/c0, true, c0 > 0 && c2 + c0 <= 0, "lt334")) ||
              (rewrite(max(y, (x + c2)/c0) < x/c0, false, c0 > 0 && c2 >= 0, "lt335")) ||
              (rewrite(min(y, (x + c2)/c0) < x/c0, true, c0 > 0 && c2 + c0 <= 0, "lt336")) ||

              // Comparison of two mins/maxes that don't cancel when subtracted
              (get_rule_flag("lt337", rflag) && rewrite(min(x, c0) < min(x, c1), false, c0 >= c1, "lt337")) ||
              (get_rule_flag("lt338", rflag) && rewrite(min(x, c0) < min(x, c1) + c2, false, c0 >= c1 + c2, "lt338")) ||
              (get_rule_flag("lt339", rflag) && rewrite(max(x, c0) < max(x, c1), false, c0 >= c1, "lt339")) ||
              (get_rule_flag("lt340", rflag) && rewrite(max(x, c0) < max(x, c1) + c2, false, c0 >= c1 + c2, "lt340")) ||

              // Comparison of aligned ramps can simplify to a comparison of the base
              (get_rule_flag("lt349", rflag) && rewrite(ramp(x * c3 + c2, c1) < broadcast(z * c0),
                                     broadcast(x * fold(c3/c0) + fold(c2/c0) < z, lanes),
                                     c0 > 0 && (c3 % c0 == 0) &&
                                     (c2 % c0) + c1 * (lanes - 1) < c0 &&
                                     (c2 % c0) + c1 * (lanes - 1) >= 0, "lt349")) ||
              // c2 = 0
              (get_rule_flag("lt355", rflag) && rewrite(ramp(x * c3, c1) < broadcast(z * c0),
                                     broadcast(x * fold(c3/c0) < z, lanes),
                                     c0 > 0 && (c3 % c0 == 0) &&
                                     c1 * (lanes - 1) < c0 &&
                                     c1 * (lanes - 1) >= 0, "lt355")) ||
              false))) {
            return mutate(std::move(rewrite.result), bounds);
        }

        if (no_overflow_int(op->a.type()) &&
            use_synthesized_rules &&
            (
#include "Simplify_LT.inc"
             )) {
            return mutate(std::move(rewrite.result), bounds);
        }
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

}
}
