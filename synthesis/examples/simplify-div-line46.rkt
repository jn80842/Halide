#lang rosette

(require "../lang.rkt")
(require "../sketch.rkt")
(require "../synthesize.rkt")

(current-bitwidth #f)

;; rewrite(0 / x, 0)

;; R0 : x
;; R1 : 0
;; R2 : R1 / R0

(define LHS (sketch (list (insn div-idx 1 0 0))
                    2 1 0))

(define RHS-sketch (get-symbolic-sketch 1 1 0))

(define-symbolic* x integer?)

(synth-rewrite RHS-sketch LHS x)