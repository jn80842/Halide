#lang racket

(provide (all-defined-out))


;; convenience methods for calling out to shell

(define (close-process-ports p)
  (begin
    (close-input-port (list-ref p 0))
    (close-output-port (list-ref p 1))
    (close-input-port (list-ref p 3))))

(define (stdout-port->string p)
  (port->string (list-ref p 0)))

(define (stderr-port->string p)
  (port->string (list-ref p 3)))

;;

#;(define (verify-expr-is-true e)
  (let* ([p (process (format "echo '~a' | /usr/local/bin/z3 -smt2 -in" (testcase->smt2 e)))]
         [expr-true? (string-contains? (stdout-port->string p) "unsat")])
    (close-process-ports p)
    expr-true?))

(define (build-smt2-query int-vars bool-vars formula)
  (string-join (append
                 ; (list (format ";; ~a" input-str))
                  (for/list ([var int-vars])
                    (format "(declare-const ~a Int)" var))
                  (for/list ([bvar bool-vars])
                    (format "(declare-const ~a Bool)" bvar))
                  (list "(define-fun max ((x Int) (y Int)) Int (ite (> x y) x y))"
                        "(define-fun min ((x Int) (y Int)) Int (ite (> x y) y x))"
                        formula
                        "(check-sat)"
                        "(get-model)")) " "))

(define (get-verify-equiv-formula int-vars bool-vars s1 s2)
  (build-smt2-query int-vars bool-vars (format "(assert (not (= ~a ~a)))" s1 s2)))

(define (get-verify-true-formula int-vars bool-vars s1)
  (build-smt2-query int-vars bool-vars (format "(assert (not ~a))" s1)))

(define (get-verify-false-formula int-vars bool-vars s1)
  (build-smt2-query int-vars bool-vars (format "(assert ~a)" s1)))

(define (call-z3 formula)
  (let* ([p (process (format "echo '~a' | /usr/local/bin/z3 -smt2 -in -T:60 -memory:1000" formula))]
         [status (string-contains? (stdout-port->string p) "unsat")])
    (close-process-ports p)
    status))