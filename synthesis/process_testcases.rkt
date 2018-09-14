#lang rosette

(require racket/engine)

(require "lang.rkt")
(require "sketch.rkt")
(require "synthesize.rkt")
(require "parsers/halide-dsl.rkt")
(require "parsers/mask-constants.rkt")
(require "parsers/smt2.rkt")

(current-bitwidth #f)

;(define true-output-file (open-output-file "/Users/jnewcomb/testcases/verify/simplifier_testcases_proven_true" #:exists 'append))
;(define not-true-output-file (open-output-file "/Users/jnewcomb/testcases/verify/simplifier_testcases_not_proven_true" #:exists 'append))
;(define timeout-file (open-output-file "/Users/jnewcomb/testcases/verify/simplifier_testcases_timeout2" #:exists 'append))

#;(call-with-input-file "/Users/jnewcomb/testcases/verify/simplifier_testcases_timeout"
  (λ (f)
    (for/fold ([counter 0])
              ([line (in-lines f)])
              (begin
                (display (format "~a: " counter))
                (displayln line)
                (with-handlers ([exn:fail? (λ (exn) (begin (displayln "z3 timeout")
                                                           (write-string (string-append line "\n") timeout-file)
                                                           'fail))])
                  (if (verify-testcase line)
                    (write-string (string-append line "\n") true-output-file)
                    (write-string (string-append line "\n") not-true-output-file)))
                (when (equal? (modulo counter 100) 0)
                  (begin
                    (flush-output true-output-file)
                    (flush-output not-true-output-file)
                    (flush-output timeout-file)))
                (add1 counter)))))

;(close-output-port true-output-file)
;(close-output-port not-true-output-file)

(define str "((min((v3*2), ((v4*2) + 1)) + (((v1 + v2)/4)*2)) <= ((((v1 + v2)/4) + v3)*2))")

(define f (λ (v1 v2 v3 v4)
            (<= (hld-add (hld-min (hld-mul v3 2) (hld-add (hld-mul v4 2) 1))
                         (hld-mul (hld-div (hld-add v1 v2) 4) 2))
                (hld-mul (hld-add (hld-div (hld-add v1 v2) 4) v3) 2))))

(define-symbolic* v0 integer?)
(define-symbolic* v1 integer?)
(define-symbolic* v2 integer?)
(define-symbolic* v3 integer?)
(define-symbolic* v4 integer?)

(define (testcase->smt2 s)
  (let* ([input-str (string-trim s)]
         [variables (set->list (get-variables input-str))]
         [phi (get-smt2-formula input-str)])
    (string-join (append
                  (list (format ";; ~a" input-str))
                  (for/list ([i (range (length variables))])
                    (format "(declare-const ~a Int)" (symbol->string (list-ref variables i))))
                  (list "(define-fun max ((x Int) (y Int)) Int (ite (> x y) x y))"
                        "(define-fun min ((x Int) (y Int)) Int (ite (> x y) y x))"
                        (format "(assert (not ~a))" phi)
                        "(check-sat)"
                        "(get-model)")) "\n")))

(call-with-input-file "/Users/jnewcomb/testcases/unsimplified.txt"
  (λ (f)
    (for/fold ([counter 0])
              ([line (in-lines f)])
      (begin
        (displayln line)
        (displayln (testcase->smt2 line))
        (call-with-output-file (format "/Users/jnewcomb/testcases/formulas/~a.txt" counter)
          (λ (out) (display (testcase->smt2 line) out)))
        (add1 counter)))))