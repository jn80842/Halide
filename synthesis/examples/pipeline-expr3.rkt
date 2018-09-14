#lang rosette

(require "../lang.rkt")
(require "../sketch.rkt")
(require "../print-sketch.rkt")
(require "../ordering.rkt")
(require "../synthesize.rkt")
(require "../parsers/parser.rkt")
(require "../parsers/halide-dsl.rkt")

(current-bitwidth #f)

(define expr "(((v0 + 1)/32) >= ((((v0 + 1)/32) + (((v0/32) - ((v0 + 1)/32)) + 1)) - 1))")

;; R0 : v0
;; R1 : 1
;; R2 : 32
;; R3 : 0 (dummy)
;; R4 : R0 + R1
;; R5 : R4 / R2
;; R6 : R0 / R2
;; R7 : R6 - R5
;; R8 : R5 + R7
;; R9 : R8 + R1
;; R10 : R9 - R1
;; R11 : R10 < R5
;; R12 : not R11

(define-symbolic* v0 integer?)
(define-symbolic* c0 integer?)
(define-symbolic* c1 integer?)

(define RHS-sketch (get-symbolic-sketch 5 1 2))

(let* ([evaled-LHS (evaluate-parser (parser-to-hld-dsl #t (make-hash (list (cons 'v0 v0))) (make-hash (list (cons '32 c0)
                                                                                                            (cons '1 c1)))) expr)]
       [evaled-RHS (apply (get-sketch-function RHS-sketch) (list v0 c0 c1))]
       [binding (time (synthesize #:forall (list v0 c0 c1)
                                  #:guarantee (assert (and (equal? 0 (get-variable-count-for-program RHS-sketch))
                                                           (equal? evaled-LHS evaled-RHS)))))])
  (if (unsat? binding)
      (displayln "unsat")
      (print-live-regs-sketch (evaluate RHS-sketch binding))))