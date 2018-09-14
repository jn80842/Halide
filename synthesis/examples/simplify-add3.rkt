#lang rosette

(require "../lang.rkt")
(require "../sketch.rkt")
(require "../synthesize.rkt")

(current-bitwidth #f)

;; (rewrite((x - y) + (y - z), x - z)

;; R0 : x
;; R1 : y
;; R2 : z
;; R3 : 0 (dummy)
;; R4 : R0 - R1
;; R5 : R1 - R2
;; R6 : R4 + R5

(define LHS2 (sketch (list (insn sub-idx 0 1 3)
                          (insn sub-idx 1 2 3)
                          (insn add-idx 4 5 3))
                    6
                    3
                    0))

(define x (get-sym-int))
(define y (get-sym-int))
(define z (get-sym-int))

(define RHS-sketch2 (get-symbolic-sketch 3 3 0))

(displayln "No ordering")
(define synth1b-sketch (synth-rewrite RHS-sketch2 LHS2 x y z))
(displayln "Ordering on variable count")
(define synth2b-sketch (synth-rewrite-var-counts RHS-sketch2 LHS2 x y z))
(displayln "Ordering on variable count and naive operator counts")
(define synth3b-sketch (synth-rewrite-var-and-op-counts RHS-sketch2 LHS2 x y z))