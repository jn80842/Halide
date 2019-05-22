#lang rosette

(require "../lang.rkt")
(require "../sketch.rkt")
(require "../print-sketch.rkt")
(require "../ordering.rkt")
(require "../synthesize.rkt")
(require "../parsers/parser.rkt")
(require "../parsers/halide-dsl.rkt")

(current-bitwidth #f)

(define expr "(((max((v0/2), -2) - max(((v0 + 3)/2), 0)) + 2) <= 1)")

(define-symbolic* v0 integer?)
(define-symbolic* c0 integer?)
(define-symbolic* c1 integer?)
(define-symbolic* c2 integer?)
(define-symbolic* c3 integer?)
(define-symbolic* c4 integer?)

(define RHS-sketch (get-symbolic-sketch 9 1 5))

#;(let* ([evaled-LHS (evaluate-parser (parser-to-hld-dsl #f (make-hash (list (cons 'v0 v0))) (make-hash '())) expr)]
       [evaled-RHS (apply (get-sketch-function RHS-sketch) (list v0 2 -2 3 0 1))]
       [binding (time (synthesize #:forall (list v0)
                                  #:guarantee (assert (equal? evaled-LHS evaled-RHS))))])
  (if (unsat? binding)
      (displayln "unsat")
      (print-live-regs-sketch (evaluate RHS-sketch binding))))

(clear-asserts!)

#;(let* ([evaled-LHS (evaluate-parser (parser-to-hld-dsl #t (make-hash (list (cons 'v0 v0))) (make-hash (list (cons '2 c0)
                                                                                                            (cons '-2 c1)
                                                                                                            (cons '3 c2)
                                                                                                            (cons '0 c3)
                                                                                                            (cons '1 c4)))) expr)]
       [evaled-RHS (apply (get-sketch-function RHS-sketch) (list v0 c0 c1 c2 c3 c4))]
       [binding (time (synthesize #:forall (list v0 c0 c1 c2 c3 c4)
                                  #:guarantee (assert (and (equal? 0 (get-variable-count-for-program RHS-sketch))
                                                           (equal? evaled-LHS evaled-RHS)))))])
  (if (unsat? binding)
      (displayln "unsat")
      (print-live-regs-sketch (evaluate RHS-sketch binding))))

;; factor out divisions
(define expr1 "(((max((v0), -2*2) - max(((v0 + 3)), 0*2)) + 2*2) <= 1*2)")

;; fewer instructions in sketch
(define RHS-sketch1 (get-symbolic-sketch 5 1 5))

(let* ([evaled-LHS (evaluate-parser (parser-to-hld-dsl #t (make-hash (list (cons 'v0 v0))) (make-hash (list (cons '2 c0)
                                                                                                            (cons '-2 c1)
                                                                                                            (cons '3 c2)
                                                                                                            (cons '0 c3)
                                                                                                            (cons '1 c4)))) expr1)]
       [evaled-RHS (apply (get-sketch-function RHS-sketch1) (list v0 c0 c1 c2 c3 c4))]
       [binding (time (synthesize #:forall (list v0 c0 c1 c2 c3 c4)
                                  #:guarantee (assert (and (equal? 0 (get-variable-count-for-program RHS-sketch))
                                                           (equal? evaled-LHS evaled-RHS)))))])
  (if (unsat? binding)
      (displayln "unsat")
      (print-live-regs-sketch (evaluate RHS-sketch binding))))

