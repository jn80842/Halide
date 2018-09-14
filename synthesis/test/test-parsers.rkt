#lang rosette

(require rackunit)
(require "../lang.rkt")
(require "../sketch.rkt")
(require "../synthesize.rkt")
(require "../ordering.rkt")
(require "../parsers/parser.rkt")
(require "../parsers/halide-dsl.rkt")
(require "../parsers/ordering.rkt")

(define p1 "(v0 + (v1 - v0))")
(define h3 3)
(define h10 10)
(define order1 (ordering 2 '(1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0)))

(define (build-variable-lookup var-set)
  (map (λ (s) (cons s (get-sym-int))) (set->list var-set)))

(check-equal? (evaluate-parser (parser-to-hld-dsl #f (build-var-lookup "v" (list h3 h10)) (make-hash '())) p1) h10)

(define testcase "((min((v3*2), ((v4*2) + 1)) + (((v1 + v2)/4)*2)) <= ((((v1 + v2)/4) + v3)*2))")

(check-equal? (evaluate-parser (parser-to-hld-dsl #f (make-hash (list (cons 'v1 10) (cons 'v2 20))) (make-hash '())) "(v1*v2)") 200)
(check-false (evaluate-parser (parser-to-hld-dsl #f (make-hash (list (cons 'v1 10) (cons 'v2 20))) (make-hash '())) "(v1>=v2)"))

;(check-true (verify-testcase testcase))

;(check-equal? (find-ordering p1) order1)


