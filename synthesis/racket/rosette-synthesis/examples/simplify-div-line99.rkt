#lang rosette

(require "../lang.rkt")
(require "../sketch.rkt")
(require "../synthesize.rkt")

(current-bitwidth #f)

;; rewrite((x + y)/x, y/x + 1)

;; R0 : x
;; R1 : y
;; R2 : 1
;; R3 : 0 (dummy)
;; R4 : R0 + R1
;; R5 : R4 / R0

(define LHS (sketch (list (insn add-idx 0 1 0)
                          (insn div-idx 4 0 0))
                    5 2 1))

(define RHS-sketch (get-symbolic-sketch 2 2 1))

(define-symbolic* x integer?)
(define-symbolic* y integer?)

(synth-rewrite RHS-sketch LHS x y 1)
