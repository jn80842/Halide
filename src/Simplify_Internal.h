#ifndef HALIDE_SIMPLIFY_VISITORS_H
#define HALIDE_SIMPLIFY_VISITORS_H

/** \file
 * The simplifier is separated into multiple compilation units with
 * this single shared header to speed up the build. This file is not
 * exported in Halide.h. */

#include "Bounds.h"
#include "IRMatch.h"
#include "IRVisitor.h"
#include "Scope.h"

// Because this file is only included by the simplify methods and
// doesn't go into Halide.h, we're free to use any old names for our
// macros.

#define LOG_EXPR_MUTATIONS 0
#define LOG_STMT_MUTATIONS 0

#define EXCLUDE_INVALID_ORDERING_RULES 0

// On old compilers, some visitors would use large stack frames,
// because they use expression templates that generate large numbers
// of temporary objects when they are built and matched against. If we
// wrap the expressions that imply lots of temporaries in a lambda, we
// can get these large frames out of the recursive path.
#define EVAL_IN_LAMBDA(x) (([&]() HALIDE_NEVER_INLINE {return (x);})())



namespace Halide {
namespace Internal {

class Simplify : public VariadicVisitor<Simplify, Expr, Stmt> {
    using Super = VariadicVisitor<Simplify, Expr, Stmt>;

    bool use_synthesized_rules = false;
    bool exclude_misordered_rules = false;
    bool rflag = false;

public:
    Simplify(bool r, const Scope<Interval> *bi, const Scope<ModulusRemainder> *ai);

    struct ExprInfo {
        // We track constant integer bounds when they exist
        int64_t min = 0, max = 0;
        bool min_defined = false, max_defined = false;
        // And the alignment of integer variables
        ModulusRemainder alignment;

        void trim_bounds_using_alignment() {
            if (alignment.modulus == 0) {
                min_defined = max_defined = true;
                min = max = alignment.remainder;
            } else if (alignment.modulus > 1) {
                if (min_defined) {
                    int64_t new_min = min - mod_imp(min, alignment.modulus) + alignment.remainder;
                    if (new_min < min) {
                        new_min += alignment.modulus;
                    }
                    min = new_min;
                }
                if (max_defined) {
                    int64_t new_max = max - mod_imp(max, alignment.modulus) + alignment.remainder;
                    if (new_max > max) {
                        new_max -= alignment.modulus;
                    }
                    max = new_max;
                }
            }

            if (min_defined && max_defined && min == max) {
                alignment.modulus = 0;
                alignment.remainder = min;
            }
        }

        // Mix in existing knowledge about this Expr
        void intersect(const ExprInfo &other) {
            if (min_defined && other.min_defined) {
                min = std::max(min, other.min);
            } else if (other.min_defined) {
                min_defined = true;
                min = other.min;
            }

            if (max_defined && other.max_defined) {
                max = std::min(max, other.max);
            } else if (other.max_defined) {
                max_defined = true;
                max = other.max;
            }

            alignment = ModulusRemainder::intersect(alignment, other.alignment);

            trim_bounds_using_alignment();
        }
    };

#if LOG_EXPR_MUTATIONS
    static int debug_indent;

    Expr mutate(const Expr &e, ExprInfo *b) {
        const std::string spaces(debug_indent, ' ');
        debug(1) << spaces << "Simplifying Expr: " << e << "\n";
        debug_indent++;
        Expr new_e = Super::dispatch(e, b);
        debug_indent--;
        if (!new_e.same_as(e)) {
            debug(1)
                << spaces << "Before: " << e << "\n"
                << spaces << "After:  " << new_e << "\n";
        }
        internal_assert(e.type() == new_e.type());
        return new_e;
    }

#else
    HALIDE_ALWAYS_INLINE
    Expr mutate(const Expr &e, ExprInfo *b) {

        int stack_marker = 0;
        ptrdiff_t depth = (ptrdiff_t)((intptr_t)this - (intptr_t)(&stack_marker));
        if (depth > 6 * 1024 * 1024) {
            debug(0) << "Exceeded 6MB of stack in a single simplifier instance on Expr:\n"
                     << e << "\n";
        }

        Expr new_e = Super::dispatch(e, b);
        internal_assert(new_e.type() == e.type()) << e << " -> " << new_e << "\n";
        return new_e;
    }
#endif

#if LOG_STMT_MUTATIONS
    Stmt mutate(const Stmt &s) {
        const std::string spaces(debug_indent, ' ');
        debug(1) << spaces << "Simplifying Stmt: " << s << "\n";
        debug_indent++;
        Stmt new_s = Super::dispatch(s);
        debug_indent--;
        if (!new_s.same_as(s)) {
            debug(1)
                << spaces << "Before: " << s << "\n"
                << spaces << "After:  " << new_s << "\n";
        }
        return new_s;
    }
#else
    Stmt mutate(const Stmt &s) {
        return Super::dispatch(s);
    }
#endif

    bool remove_dead_lets;
    bool no_float_simplify;

    HALIDE_ALWAYS_INLINE
    bool may_simplify(const Type &t) {
        return !no_float_simplify || !t.is_float();
    }

    // Returns true iff t is an integral type where overflow is undefined
    HALIDE_ALWAYS_INLINE
        bool no_overflow_int(Type t) {
        return t.is_int() && t.bits() >= 32;
    }

    HALIDE_ALWAYS_INLINE
        bool no_overflow_scalar_int(Type t) {
        return t.is_scalar() && no_overflow_int(t);
    }

    // Returns true iff t does not have a well defined overflow behavior.
    HALIDE_ALWAYS_INLINE
        bool no_overflow(Type t) {
        return t.is_float() || no_overflow_int(t);
    }

    struct VarInfo {
        Expr replacement;
        int old_uses, new_uses;
    };

    // Tracked for all let vars
    Scope<VarInfo> var_info;

    // Only tracked for integer let vars
    Scope<ExprInfo> bounds_and_alignment_info;

    // Symbols used by rewrite rules
    IRMatcher::Wild<0> x;
    IRMatcher::Wild<1> y;
    IRMatcher::Wild<2> z;
    IRMatcher::Wild<3> w;
    IRMatcher::Wild<4> u;
    IRMatcher::Wild<5> v;
    IRMatcher::WildConst<0> c0;
    IRMatcher::WildConst<1> c1;
    IRMatcher::WildConst<2> c2;
    IRMatcher::WildConst<3> c3;
    IRMatcher::WildConst<4> c4;
    IRMatcher::WildConst<5> c5;

    // If we encounter a reference to a buffer (a Load, Store, Call,
    // or Provide), there's an implicit dependence on some associated
    // symbols.
    void found_buffer_reference(const std::string &name, size_t dimensions = 0);

    // Wrappers for as_const_foo that are more convenient to use in
    // the large chains of conditions in the visit methods
    // below. Unlike the versions in IROperator, these only match
    // scalars.
    bool const_float(const Expr &e, double *f);
    bool const_int(const Expr &e, int64_t *i);
    bool const_uint(const Expr &e, uint64_t *u);

    // Put the args to a commutative op in a canonical order
    HALIDE_ALWAYS_INLINE
    bool should_commute(const Expr &a, const Expr &b) {
        if (a.node_type() < b.node_type()) return true;
        if (a.node_type() > b.node_type()) return false;

        if (a.node_type() == IRNodeType::Variable) {
            const Variable *va = a.as<Variable>();
            const Variable *vb = b.as<Variable>();
            return va->name.compare(vb->name) > 0;
        }

        return false;
    }

    std::set<Expr, IRDeepCompare> truths, falsehoods;

    struct ScopedFact {
        Simplify *simplify;

        std::vector<const Variable *> pop_list;
        std::vector<const Variable *> bounds_pop_list;
        std::vector<Expr> truths, falsehoods;

        void learn_false(const Expr &fact);
        void learn_true(const Expr &fact);
        void learn_info(const Variable *v, const ExprInfo &);

        ScopedFact(Simplify *s) : simplify(s) {}
        ~ScopedFact();

        // allow move but not copy
        ScopedFact(const ScopedFact& that) = delete;
        ScopedFact(ScopedFact&& that) = default;
    };

    // Tell the simplifier to learn from and exploit a boolean
    // condition, over the lifetime of the returned object.
    ScopedFact scoped_truth(const Expr &fact) {
        ScopedFact f(this);
        f.learn_true(fact);
        return f;
    }

    // Tell the simplifier to assume a boolean condition is false over
    // the lifetime of the returned object.
    ScopedFact scoped_falsehood(const Expr &fact) {
        ScopedFact f(this);
        f.learn_false(fact);
        return f;
    }

    // Learn some facts permanently, with no scoping.
    void learn_false(const Expr &fact);
    void learn_true(const Expr &fact);
    void learn_info(const Variable *v, const ExprInfo &);

    template <typename T>
    Expr hoist_slice_vector(Expr e);

    Stmt mutate_let_body(Stmt s, ExprInfo *) {return mutate(s);}
    Expr mutate_let_body(Expr e, ExprInfo *bounds) {return mutate(e, bounds);}

    template<typename T, typename Body>
    Body simplify_let(const T *op, ExprInfo *bounds);

    Expr visit(const IntImm *op, ExprInfo *bounds);
    Expr visit(const UIntImm *op, ExprInfo *bounds);
    Expr visit(const FloatImm *op, ExprInfo *bounds);
    Expr visit(const StringImm *op, ExprInfo *bounds);
    Expr visit(const Broadcast *op, ExprInfo *bounds);
    Expr visit(const Cast *op, ExprInfo *bounds);
    Expr visit(const Variable *op, ExprInfo *bounds);
    Expr visit(const Add *op, ExprInfo *bounds);
    Expr visit(const Sub *op, ExprInfo *bounds);
    Expr visit(const Mul *op, ExprInfo *bounds);
    Expr visit(const Div *op, ExprInfo *bounds);
    Expr visit(const Mod *op, ExprInfo *bounds);
    Expr visit(const Min *op, ExprInfo *bounds);
    Expr visit(const Max *op, ExprInfo *bounds);
    Expr visit(const EQ *op, ExprInfo *bounds);
    Expr visit(const NE *op, ExprInfo *bounds);
    Expr visit(const LT *op, ExprInfo *bounds);
    Expr visit(const LE *op, ExprInfo *bounds);
    Expr visit(const GT *op, ExprInfo *bounds);
    Expr visit(const GE *op, ExprInfo *bounds);
    Expr visit(const And *op, ExprInfo *bounds);
    Expr visit(const Or *op, ExprInfo *bounds);
    Expr visit(const Not *op, ExprInfo *bounds);
    Expr visit(const Select *op, ExprInfo *bounds);
    Expr visit(const Ramp *op, ExprInfo *bounds);
    Stmt visit(const IfThenElse *op);
    Expr visit(const Load *op, ExprInfo *bounds);
    Expr visit(const Call *op, ExprInfo *bounds);
    Expr visit(const Shuffle *op, ExprInfo *bounds);
    Expr visit(const Let *op, ExprInfo *bounds);
    Stmt visit(const LetStmt *op);
    Stmt visit(const AssertStmt *op);
    Stmt visit(const For *op);
    Stmt visit(const Provide *op);
    Stmt visit(const Store *op);
    Stmt visit(const Allocate *op);
    Stmt visit(const Evaluate *op);
    Stmt visit(const ProducerConsumer *op);
    Stmt visit(const Block *op);
    Stmt visit(const Realize *op);
    Stmt visit(const Prefetch *op);
    Stmt visit(const Free *op);
    Stmt visit(const Acquire *op);
    Stmt visit(const Fork *op);

    std::map<std::string, bool> default_rule_flags;
    std::map<std::string, bool> experimental_rule_flags;

    bool get_rule_flag(std::string rulename, bool experimental) {
        default_rule_flags["add100"] = true;
default_rule_flags["add101"] = true;
default_rule_flags["add102"] = true;
default_rule_flags["add103"] = true;
default_rule_flags["add104"] = true;
default_rule_flags["add105"] = true;
default_rule_flags["add106"] = true;
default_rule_flags["add107"] = true;
default_rule_flags["add108"] = true;
default_rule_flags["add110"] = true;
default_rule_flags["add111"] = true;
default_rule_flags["add112"] = true;
default_rule_flags["add113"] = true;
default_rule_flags["add114"] = true;
default_rule_flags["add115"] = true;
default_rule_flags["add116"] = true;
default_rule_flags["add117"] = true;
default_rule_flags["add118"] = true;
default_rule_flags["add119"] = true;
default_rule_flags["add121"] = true;
default_rule_flags["add122"] = true;
default_rule_flags["add123"] = true;
default_rule_flags["add31"] = true;
default_rule_flags["add36"] = true;
default_rule_flags["add37"] = true;
default_rule_flags["add42"] = true;
default_rule_flags["add43"] = true;
default_rule_flags["add44"] = true;
default_rule_flags["add45"] = true;
default_rule_flags["add46"] = true;
default_rule_flags["add47"] = true;
default_rule_flags["add48"] = true;
default_rule_flags["add51"] = true;
default_rule_flags["add52"] = true;
default_rule_flags["add53"] = true;
default_rule_flags["add54"] = true;
default_rule_flags["add55"] = true;
default_rule_flags["add56"] = true;
default_rule_flags["add57"] = true;
default_rule_flags["add58"] = true;
default_rule_flags["add60"] = true;
default_rule_flags["add61"] = true;
default_rule_flags["add62"] = true;
default_rule_flags["add63"] = true;
default_rule_flags["add64"] = true;
default_rule_flags["add65"] = true;
default_rule_flags["add66"] = true;
default_rule_flags["add67"] = true;
default_rule_flags["add68"] = true;
default_rule_flags["add69"] = true;
default_rule_flags["add70"] = true;
default_rule_flags["add71"] = true;
default_rule_flags["add72"] = true;
default_rule_flags["add73"] = true;
default_rule_flags["add74"] = true;
default_rule_flags["add75"] = true;
default_rule_flags["add76"] = true;
default_rule_flags["add77"] = true;
default_rule_flags["add79"] = true;
default_rule_flags["add80"] = true;
default_rule_flags["add81"] = true;
default_rule_flags["add82"] = true;
default_rule_flags["add83"] = true;
default_rule_flags["add84"] = true;
default_rule_flags["add85"] = true;
default_rule_flags["add86"] = true;
default_rule_flags["add87"] = true;
default_rule_flags["add88"] = true;
default_rule_flags["add89"] = true;
default_rule_flags["add90"] = true;
default_rule_flags["add91"] = true;
default_rule_flags["add92"] = true;
default_rule_flags["add93"] = true;
default_rule_flags["add94"] = true;
default_rule_flags["add95"] = true;
default_rule_flags["add96"] = true;
default_rule_flags["add97"] = true;
default_rule_flags["add98"] = true;
default_rule_flags["add99"] = true;
default_rule_flags["and100"] = true;
default_rule_flags["and101"] = true;
default_rule_flags["and102"] = true;
default_rule_flags["and104"] = true;
default_rule_flags["and105"] = true;
default_rule_flags["and106"] = true;
default_rule_flags["and107"] = true;
default_rule_flags["and109"] = true;
default_rule_flags["and110"] = true;
default_rule_flags["and111"] = true;
default_rule_flags["and112"] = true;
default_rule_flags["and114"] = true;
default_rule_flags["and115"] = true;
default_rule_flags["and117"] = true;
default_rule_flags["and118"] = true;
default_rule_flags["and119"] = true;
default_rule_flags["and120"] = true;
default_rule_flags["and121"] = true;
default_rule_flags["and45"] = true;
default_rule_flags["and46"] = true;
default_rule_flags["and47"] = true;
default_rule_flags["and48"] = true;
default_rule_flags["and49"] = true;
default_rule_flags["and50"] = true;
default_rule_flags["and51"] = true;
default_rule_flags["and52"] = true;
default_rule_flags["and53"] = true;
default_rule_flags["and54"] = true;
default_rule_flags["and55"] = true;
default_rule_flags["and56"] = true;
default_rule_flags["and57"] = true;
default_rule_flags["and58"] = true;
default_rule_flags["and59"] = true;
default_rule_flags["and60"] = true;
default_rule_flags["and66"] = true;
default_rule_flags["and67"] = true;
default_rule_flags["and68"] = true;
default_rule_flags["and69"] = true;
default_rule_flags["and70"] = true;
default_rule_flags["and71"] = true;
default_rule_flags["and72"] = true;
default_rule_flags["and73"] = true;
default_rule_flags["and74"] = true;
default_rule_flags["and78"] = true;
default_rule_flags["and80"] = true;
default_rule_flags["and81"] = true;
default_rule_flags["and82"] = true;
default_rule_flags["and83"] = true;
default_rule_flags["and84"] = true;
default_rule_flags["and85"] = true;
default_rule_flags["and87"] = true;
default_rule_flags["and89"] = true;
default_rule_flags["and90"] = true;
default_rule_flags["and91"] = true;
default_rule_flags["and92"] = true;
default_rule_flags["and94"] = true;
default_rule_flags["and95"] = true;
default_rule_flags["and96"] = true;
default_rule_flags["and97"] = true;
default_rule_flags["and99"] = true;
default_rule_flags["div103"] = true;
default_rule_flags["div104"] = true;
default_rule_flags["div107"] = true;
default_rule_flags["div108"] = true;
default_rule_flags["div109"] = true;
default_rule_flags["div111"] = true;
default_rule_flags["div113"] = true;
default_rule_flags["div114"] = true;
default_rule_flags["div115"] = true;
default_rule_flags["div116"] = true;
default_rule_flags["div118"] = true;
default_rule_flags["div119"] = true;
default_rule_flags["div120"] = true;
default_rule_flags["div121"] = true;
default_rule_flags["div122"] = true;
default_rule_flags["div123"] = true;
default_rule_flags["div124"] = true;
default_rule_flags["div125"] = true;
default_rule_flags["div127"] = true;
default_rule_flags["div128"] = true;
default_rule_flags["div129"] = true;
default_rule_flags["div130"] = true;
default_rule_flags["div132"] = true;
default_rule_flags["div133"] = true;
default_rule_flags["div134"] = true;
default_rule_flags["div135"] = true;
default_rule_flags["div138"] = true;
default_rule_flags["div139"] = true;
default_rule_flags["div140"] = true;
default_rule_flags["div141"] = true;
default_rule_flags["div142"] = true;
default_rule_flags["div143"] = true;
default_rule_flags["div144"] = true;
default_rule_flags["div145"] = true;
default_rule_flags["div147"] = true;
default_rule_flags["div148"] = true;
default_rule_flags["div149"] = true;
default_rule_flags["div150"] = true;
default_rule_flags["div152"] = true;
default_rule_flags["div153"] = true;
default_rule_flags["div154"] = true;
default_rule_flags["div155"] = true;
default_rule_flags["div156"] = true;
default_rule_flags["div157"] = true;
default_rule_flags["div158"] = true;
default_rule_flags["div159"] = true;
default_rule_flags["div160"] = true;
default_rule_flags["div161"] = true;
default_rule_flags["div162"] = true;
default_rule_flags["div163"] = true;
default_rule_flags["div164"] = true;
default_rule_flags["div165"] = true;
default_rule_flags["div168"] = true;
default_rule_flags["div171"] = true;
default_rule_flags["div173"] = true;
default_rule_flags["div174"] = true;
default_rule_flags["div177"] = true;
default_rule_flags["div180"] = true;
default_rule_flags["div182"] = true;
default_rule_flags["div93"] = true;
default_rule_flags["div95"] = true;
default_rule_flags["div96"] = true;
default_rule_flags["div97"] = true;
default_rule_flags["div98"] = true;
default_rule_flags["eq100"] = true;
default_rule_flags["eq74"] = true;
default_rule_flags["eq75"] = true;
default_rule_flags["eq76"] = true;
default_rule_flags["eq77"] = true;
default_rule_flags["eq78"] = true;
default_rule_flags["eq79"] = true;
default_rule_flags["eq80"] = true;
default_rule_flags["eq81"] = true;
default_rule_flags["eq82"] = true;
default_rule_flags["eq83"] = true;
default_rule_flags["eq84"] = true;
default_rule_flags["eq85"] = true;
default_rule_flags["eq86"] = true;
default_rule_flags["eq87"] = true;
default_rule_flags["eq88"] = true;
default_rule_flags["eq89"] = true;
default_rule_flags["eq90"] = true;
default_rule_flags["eq91"] = true;
default_rule_flags["eq92"] = true;
default_rule_flags["eq93"] = true;
default_rule_flags["eq98"] = true;
default_rule_flags["eq99"] = true;
default_rule_flags["lt100"] = true;
default_rule_flags["lt101"] = true;
default_rule_flags["lt102"] = true;
default_rule_flags["lt105"] = true;
default_rule_flags["lt106"] = true;
default_rule_flags["lt107"] = true;
default_rule_flags["lt108"] = true;
default_rule_flags["lt109"] = true;
default_rule_flags["lt110"] = true;
default_rule_flags["lt111"] = true;
default_rule_flags["lt112"] = true;
default_rule_flags["lt115"] = true;
default_rule_flags["lt116"] = true;
default_rule_flags["lt117"] = true;
default_rule_flags["lt118"] = true;
default_rule_flags["lt119"] = true;
default_rule_flags["lt120"] = true;
default_rule_flags["lt121"] = true;
default_rule_flags["lt122"] = true;
default_rule_flags["lt123"] = true;
default_rule_flags["lt124"] = true;
default_rule_flags["lt125"] = true;
default_rule_flags["lt126"] = true;
default_rule_flags["lt127"] = true;
default_rule_flags["lt128"] = true;
default_rule_flags["lt129"] = true;
default_rule_flags["lt130"] = true;
default_rule_flags["lt133"] = true;
default_rule_flags["lt134"] = true;
default_rule_flags["lt136"] = true;
default_rule_flags["lt138"] = true;
default_rule_flags["lt141"] = true;
default_rule_flags["lt142"] = true;
default_rule_flags["lt148"] = true;
default_rule_flags["lt149"] = true;
default_rule_flags["lt150"] = true;
default_rule_flags["lt151"] = true;
default_rule_flags["lt153"] = true;
default_rule_flags["lt154"] = true;
default_rule_flags["lt155"] = true;
default_rule_flags["lt156"] = true;
default_rule_flags["lt159"] = true;
default_rule_flags["lt160"] = true;
default_rule_flags["lt161"] = true;
default_rule_flags["lt162"] = true;
default_rule_flags["lt164"] = true;
default_rule_flags["lt165"] = true;
default_rule_flags["lt166"] = true;
default_rule_flags["lt167"] = true;
default_rule_flags["lt170"] = true;
default_rule_flags["lt171"] = true;
default_rule_flags["lt172"] = true;
default_rule_flags["lt173"] = true;
default_rule_flags["lt175"] = true;
default_rule_flags["lt176"] = true;
default_rule_flags["lt177"] = true;
default_rule_flags["lt178"] = true;
default_rule_flags["lt181"] = true;
default_rule_flags["lt182"] = true;
default_rule_flags["lt183"] = true;
default_rule_flags["lt184"] = true;
default_rule_flags["lt187"] = true;
default_rule_flags["lt188"] = true;
default_rule_flags["lt189"] = true;
default_rule_flags["lt190"] = true;
default_rule_flags["lt195"] = true;
default_rule_flags["lt196"] = true;
default_rule_flags["lt197"] = true;
default_rule_flags["lt198"] = true;
default_rule_flags["lt200"] = true;
default_rule_flags["lt201"] = true;
default_rule_flags["lt202"] = true;
default_rule_flags["lt203"] = true;
default_rule_flags["lt205"] = true;
default_rule_flags["lt206"] = true;
default_rule_flags["lt207"] = true;
default_rule_flags["lt208"] = true;
default_rule_flags["lt210"] = true;
default_rule_flags["lt211"] = true;
default_rule_flags["lt212"] = true;
default_rule_flags["lt213"] = true;
default_rule_flags["lt216"] = true;
default_rule_flags["lt219"] = true;
default_rule_flags["lt220"] = true;
default_rule_flags["lt222"] = true;
default_rule_flags["lt223"] = true;
default_rule_flags["lt233"] = true;
default_rule_flags["lt234"] = true;
default_rule_flags["lt235"] = true;
default_rule_flags["lt236"] = true;
default_rule_flags["lt237"] = true;
default_rule_flags["lt238"] = true;
default_rule_flags["lt239"] = true;
default_rule_flags["lt240"] = true;
default_rule_flags["lt243"] = true;
default_rule_flags["lt244"] = true;
default_rule_flags["lt245"] = true;
default_rule_flags["lt246"] = true;
default_rule_flags["lt249"] = true;
default_rule_flags["lt250"] = true;
default_rule_flags["lt251"] = true;
default_rule_flags["lt252"] = true;
default_rule_flags["lt255"] = true;
default_rule_flags["lt256"] = true;
default_rule_flags["lt257"] = true;
default_rule_flags["lt258"] = true;
default_rule_flags["lt259"] = true;
default_rule_flags["lt260"] = true;
default_rule_flags["lt261"] = true;
default_rule_flags["lt262"] = true;
default_rule_flags["lt265"] = true;
default_rule_flags["lt266"] = true;
default_rule_flags["lt269"] = true;
default_rule_flags["lt270"] = true;
default_rule_flags["lt271"] = true;
default_rule_flags["lt272"] = true;
default_rule_flags["lt275"] = true;
default_rule_flags["lt276"] = true;
default_rule_flags["lt277"] = true;
default_rule_flags["lt278"] = true;
default_rule_flags["lt281"] = true;
default_rule_flags["lt282"] = true;
default_rule_flags["lt285"] = true;
default_rule_flags["lt286"] = true;
default_rule_flags["lt288"] = true;
default_rule_flags["lt289"] = true;
default_rule_flags["lt291"] = true;
default_rule_flags["lt292"] = true;
default_rule_flags["lt295"] = true;
default_rule_flags["lt296"] = true;
default_rule_flags["lt299"] = true;
default_rule_flags["lt300"] = true;
default_rule_flags["lt301"] = true;
default_rule_flags["lt302"] = true;
default_rule_flags["lt303"] = true;
default_rule_flags["lt304"] = true;
default_rule_flags["lt306"] = true;
default_rule_flags["lt307"] = true;
default_rule_flags["lt308"] = true;
default_rule_flags["lt309"] = true;
default_rule_flags["lt310"] = true;
default_rule_flags["lt311"] = true;
default_rule_flags["lt313"] = true;
default_rule_flags["lt314"] = true;
default_rule_flags["lt315"] = true;
default_rule_flags["lt316"] = true;
default_rule_flags["lt317"] = true;
default_rule_flags["lt318"] = true;
default_rule_flags["lt319"] = true;
default_rule_flags["lt320"] = true;
default_rule_flags["lt321"] = true;
default_rule_flags["lt323"] = true;
default_rule_flags["lt324"] = true;
default_rule_flags["lt325"] = true;
default_rule_flags["lt329"] = true;
default_rule_flags["lt330"] = true;
default_rule_flags["lt331"] = true;
default_rule_flags["lt332"] = true;
default_rule_flags["lt333"] = true;
default_rule_flags["lt334"] = true;
default_rule_flags["lt335"] = true;
default_rule_flags["lt336"] = true;
default_rule_flags["lt337"] = true;
default_rule_flags["lt338"] = true;
default_rule_flags["lt339"] = true;
default_rule_flags["lt34"] = true;
default_rule_flags["lt340"] = true;
default_rule_flags["lt349"] = true;
default_rule_flags["lt35"] = true;
default_rule_flags["lt355"] = true;
default_rule_flags["lt36"] = true;
default_rule_flags["lt37"] = true;
default_rule_flags["lt39"] = true;
default_rule_flags["lt40"] = true;
default_rule_flags["lt41"] = true;
default_rule_flags["lt42"] = true;
default_rule_flags["lt55"] = true;
default_rule_flags["lt57"] = true;
default_rule_flags["lt59"] = true;
default_rule_flags["lt60"] = true;
default_rule_flags["lt63"] = true;
default_rule_flags["lt65"] = true;
default_rule_flags["lt66"] = true;
default_rule_flags["lt67"] = true;
default_rule_flags["lt68"] = true;
default_rule_flags["lt69"] = true;
default_rule_flags["lt70"] = true;
default_rule_flags["lt71"] = true;
default_rule_flags["lt72"] = true;
default_rule_flags["lt73"] = true;
default_rule_flags["lt74"] = true;
default_rule_flags["lt75"] = true;
default_rule_flags["lt76"] = true;
default_rule_flags["lt77"] = true;
default_rule_flags["lt78"] = true;
default_rule_flags["lt81"] = true;
default_rule_flags["lt82"] = true;
default_rule_flags["lt85"] = true;
default_rule_flags["lt86"] = true;
default_rule_flags["lt89"] = true;
default_rule_flags["lt90"] = true;
default_rule_flags["lt91"] = true;
default_rule_flags["lt92"] = true;
default_rule_flags["lt95"] = true;
default_rule_flags["lt96"] = true;
default_rule_flags["lt97"] = true;
default_rule_flags["lt98"] = true;
default_rule_flags["lt99"] = true;
default_rule_flags["max100"] = true;
default_rule_flags["max101"] = true;
default_rule_flags["max102"] = true;
default_rule_flags["max103"] = true;
default_rule_flags["max104"] = true;
default_rule_flags["max105"] = true;
default_rule_flags["max106"] = true;
default_rule_flags["max108"] = true;
default_rule_flags["max109"] = true;
default_rule_flags["max110"] = true;
default_rule_flags["max111"] = true;
default_rule_flags["max112"] = true;
default_rule_flags["max113"] = true;
default_rule_flags["max114"] = true;
default_rule_flags["max115"] = true;
default_rule_flags["max118"] = true;
default_rule_flags["max119"] = true;
default_rule_flags["max120"] = true;
default_rule_flags["max121"] = true;
default_rule_flags["max123"] = true;
default_rule_flags["max124"] = true;
default_rule_flags["max125"] = true;
default_rule_flags["max126"] = true;
default_rule_flags["max128"] = true;
default_rule_flags["max130"] = true;
default_rule_flags["max131"] = true;
default_rule_flags["max133"] = true;
default_rule_flags["max134"] = true;
default_rule_flags["max135"] = true;
default_rule_flags["max136"] = true;
default_rule_flags["max137"] = true;
default_rule_flags["max138"] = true;
default_rule_flags["max139"] = true;
default_rule_flags["max140"] = true;
default_rule_flags["max142"] = true;
default_rule_flags["max143"] = true;
default_rule_flags["max144"] = true;
default_rule_flags["max145"] = true;
default_rule_flags["max147"] = true;
default_rule_flags["max148"] = true;
default_rule_flags["max149"] = true;
default_rule_flags["max150"] = true;
default_rule_flags["max152"] = true;
default_rule_flags["max153"] = true;
default_rule_flags["max154"] = true;
default_rule_flags["max155"] = true;
default_rule_flags["max157"] = true;
default_rule_flags["max158"] = true;
default_rule_flags["max159"] = true;
default_rule_flags["max160"] = true;
default_rule_flags["max161"] = true;
default_rule_flags["max162"] = true;
default_rule_flags["max163"] = true;
default_rule_flags["max164"] = true;
default_rule_flags["max165"] = true;
default_rule_flags["max166"] = true;
default_rule_flags["max167"] = true;
default_rule_flags["max168"] = true;
default_rule_flags["max169"] = true;
default_rule_flags["max170"] = true;
default_rule_flags["max173"] = true;
default_rule_flags["max174"] = true;
default_rule_flags["max175"] = true;
default_rule_flags["max176"] = true;
default_rule_flags["max177"] = true;
default_rule_flags["max178"] = true;
default_rule_flags["max179"] = true;
default_rule_flags["max180"] = true;
default_rule_flags["max182"] = true;
default_rule_flags["max183"] = true;
default_rule_flags["max185"] = true;
default_rule_flags["max186"] = true;
default_rule_flags["max187"] = true;
default_rule_flags["max188"] = true;
default_rule_flags["max189"] = true;
default_rule_flags["max190"] = true;
default_rule_flags["max192"] = true;
default_rule_flags["max193"] = true;
default_rule_flags["max200"] = true;
default_rule_flags["max201"] = true;
default_rule_flags["max203"] = true;
default_rule_flags["max205"] = true;
default_rule_flags["max46"] = true;
default_rule_flags["max47"] = true;
default_rule_flags["max54"] = true;
default_rule_flags["max99"] = true;
default_rule_flags["min100"] = true;
default_rule_flags["min101"] = true;
default_rule_flags["min102"] = true;
default_rule_flags["min103"] = true;
default_rule_flags["min104"] = true;
default_rule_flags["min105"] = true;
default_rule_flags["min106"] = true;
default_rule_flags["min108"] = true;
default_rule_flags["min109"] = true;
default_rule_flags["min110"] = true;
default_rule_flags["min111"] = true;
default_rule_flags["min112"] = true;
default_rule_flags["min113"] = true;
default_rule_flags["min114"] = true;
default_rule_flags["min115"] = true;
default_rule_flags["min118"] = true;
default_rule_flags["min120"] = true;
default_rule_flags["min121"] = true;
default_rule_flags["min122"] = true;
default_rule_flags["min123"] = true;
default_rule_flags["min125"] = true;
default_rule_flags["min126"] = true;
default_rule_flags["min127"] = true;
default_rule_flags["min128"] = true;
default_rule_flags["min130"] = true;
default_rule_flags["min132"] = true;
default_rule_flags["min133"] = true;
default_rule_flags["min135"] = true;
default_rule_flags["min136"] = true;
default_rule_flags["min137"] = true;
default_rule_flags["min138"] = true;
default_rule_flags["min139"] = true;
default_rule_flags["min140"] = true;
default_rule_flags["min141"] = true;
default_rule_flags["min142"] = true;
default_rule_flags["min144"] = true;
default_rule_flags["min145"] = true;
default_rule_flags["min146"] = true;
default_rule_flags["min147"] = true;
default_rule_flags["min149"] = true;
default_rule_flags["min150"] = true;
default_rule_flags["min151"] = true;
default_rule_flags["min152"] = true;
default_rule_flags["min154"] = true;
default_rule_flags["min155"] = true;
default_rule_flags["min156"] = true;
default_rule_flags["min157"] = true;
default_rule_flags["min159"] = true;
default_rule_flags["min160"] = true;
default_rule_flags["min161"] = true;
default_rule_flags["min162"] = true;
default_rule_flags["min163"] = true;
default_rule_flags["min164"] = true;
default_rule_flags["min165"] = true;
default_rule_flags["min166"] = true;
default_rule_flags["min167"] = true;
default_rule_flags["min168"] = true;
default_rule_flags["min169"] = true;
default_rule_flags["min170"] = true;
default_rule_flags["min172"] = true;
default_rule_flags["min173"] = true;
default_rule_flags["min175"] = true;
default_rule_flags["min176"] = true;
default_rule_flags["min177"] = true;
default_rule_flags["min178"] = true;
default_rule_flags["min179"] = true;
default_rule_flags["min180"] = true;
default_rule_flags["min181"] = true;
default_rule_flags["min182"] = true;
default_rule_flags["min184"] = true;
default_rule_flags["min185"] = true;
default_rule_flags["min187"] = true;
default_rule_flags["min188"] = true;
default_rule_flags["min189"] = true;
default_rule_flags["min190"] = true;
default_rule_flags["min191"] = true;
default_rule_flags["min192"] = true;
default_rule_flags["min194"] = true;
default_rule_flags["min195"] = true;
default_rule_flags["min202"] = true;
default_rule_flags["min203"] = true;
default_rule_flags["min205"] = true;
default_rule_flags["min207"] = true;
default_rule_flags["min46"] = true;
default_rule_flags["min47"] = true;
default_rule_flags["min54"] = true;
default_rule_flags["min99"] = true;

        experimental_rule_flags["add42"] = true;
        experimental_rule_flags["add47"] = false;
        if (experimental) {
            return experimental_rule_flags[rulename];
        } else {
            return default_rule_flags[rulename];
        }
    }
};

}
}

#endif
