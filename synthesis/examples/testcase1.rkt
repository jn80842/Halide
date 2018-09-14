#lang rosette

(require "../lang.rkt")
(require "../sketch.rkt")
(require "../synthesize.rkt")

(current-bitwidth #f)

;; test case: reduce (0 - x) / 2 <= (1 - x) / 2
;; ! ( (1 - x) / 2 > (0 - x) / 2 )

;; R0 : x
;; R1 : 0
;; R2 : 1
;; R3 : 2
;; R4 : R1 - R0
;; R5 : R4 / R3
;; R6 : R2 - R0
;; R7 : R6 / R3
;; R8 : R7 < R5
;; R9 : ! R8

(define LHS (sketch (list (insn 1 1 0 0)
                          (insn 4 4 3 0)
                          (insn 1 2 0 0)
                          (insn 4 6 3 0)
                          (insn 9 7 5 0)
                          (insn 12 8 0 0))
                    9
                    1
                    3))

(define RHS-sketch (get-symbolic-sketch 6 1 3))

(define x (get-sym-int))
(define c-zero 0)
(define zero (get-sym-int))
(define c-one 1)
(define one (get-sym-int))
(define c-two 2)
(define two (get-sym-int))

;(synth-rewrite RHS-sketch LHS x zero one two)

#;(let ([evaled-LHS ((get-sketch-function LHS) x zero one two)]
      [evaled-concrete-conditions ((get-sketch-function RHS-sketch) x (hld-int #f #f 0) (hld-int #f #f 1) (hld-int #f #f 2))]
      [evaled-conditions ((get-sketch-function RHS-sketch) x zero one two)])
  (synthesize #:forall (symbolics (list x zero one two))
              #:guarantee (assert (and ((get-sketch-function LHS) x zero one two)
                                     ((get-sketch-function RHS-sketch) x zero one two)))))
