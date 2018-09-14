#lang rosette

(require "../lang.rkt")
(require "../sketch.rkt")
(require "../synthesize.rkt")

(current-bitwidth #f)

;; min(x, y - z) + z

;; R0 : x
;; R1 : y
;; R2 : z
;; R3 : 0 (dummy)
;; R4 : R1 - R2
;; R5 : min R0 R4
;; R6 : R5 + R2

(define LHS (sketch (list (insn sub-idx 1 2 3)
                          (insn min-idx 0 4 3)
                          (insn add-idx 5 2 3))
                    6 3 0))

(define RHS-sketch (get-symbolic-sketch 3 3 0))

(define x (get-sym-int))
(define y (get-sym-int))
(define z (get-sym-int))

(synth-rewrite RHS-sketch LHS x y z)