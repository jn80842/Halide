# How to verify simplification rewrite rules

## Requirements

Install Z3 (https://github.com/Z3Prover/z3) and put the executable on your PATH.

## Running the task

When the `HALIDE_VERIFY_SIMPLIFY_RULES` flag is set in src/IRMatch.h, every time a rewrite method is invoked, a file is written out containing an SMT2 script. The rewrite rules are called in the various src/Simplify&ast;.cpp files. The arguments to the rewrite method are left hand side (original) expression, right hand side (substitute) expression, and an optional precondition. To verify that this substitution is valid, we assert that given that the precondition holds, there is no assignment to the variables in the expressions such that the LHS and RHS are not equal. If Z3 can find such an assignment, the formula is satisfiable and the rewrite is not valid. If it cannot and the formula is unsatisfiable, we know the substitution preserves the semantics of the original expression. Because nonlinear integer arithmetic is undecidable, Z3 will sometimes return a status of unknown, in which case we cannot say if the substitution is valid or not.

To verify the rewrite rules, run `make correctness_verify`. In the `main` method of test/correctness/verify.cpp, we check a suite of rewrites designed to exercise every rewrite rule. For every type of expression operation, the simplifier tries to match the first argument of the `check` call to the LHS of a series of rewrite rules, stopping once a match has been found. In verify.cpp, we call `check` on expressions of every operation type that cannot simplify, thus ensuring that the simplifier will attempt all the rewrite rules it can. Some of the rewrite rules have additional guards, such as checking that the expression type is integer before attempting the rewrite. We believe that the current set of expressions exercise all rules that are currently able to be verified, but if additional rules are added, care should be taken to ensure they will also be verified with this job.

Once the make task has run, a file for each rule will be created in bin/build/tmp. (Some rules will have generated files multiple times, as it's tricky to invoke every rewrite rule once and only once.) Running the script test/z3/verify_rules.sh will call Z3 on each of these files. The script sets a timeout of 60 seconds and a limit on the memory Z3 will use to 1000 MB; adjust the -T and -memory flags on z3 in the script as needed. The verify_rules.sh script can be called with the options -f, -p, -u flags to only emit the results from verifications that fail, pass, or have status unknown respectively. Failing tests will print values for which the LHS and RHS evaluate to different results.

## Assumptions

We currently assume all numbers are infinite precision integers. Halide booleans (uint1) are modeled by the Bool type in SMT2.

We assume that all left hand side expressions do not divide by zero; that is, any divisor or modulus is not equal to zero. Right hand side expressions can contain divisor/modulus terms from the LHS, but cannot introduce new divisor/modulus terms, since we cannot assume that they are not zero. Thus, a LHS expression that does not divide by zero will never be rewritten to a RHS that divides by zero. However, LHS expression that does divide by zero can be rewritten to an expression that does or does not divide by zero, so it is possible that unsimplified code that fails at runtime will not fail after simplification.

## Resources

A useful Z3 tutorial: https://rise4fun.com/z3/tutorial

Documentation for SMT2: http://smtlib.cs.uiowa.edu/index.shtml