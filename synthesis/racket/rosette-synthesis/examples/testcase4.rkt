#lang rosette

(require "../lang.rkt")
(require "../sketch.rkt")
(require "../synthesize.rkt")

(current-bitwidth #f)

;; -1 < v0 || v0 < -1

;; R0 : v0
;; R1 : -1
;; R2 : R1 < R0
;; R3 : R0 < R1
;; R4 : R2 || R3

(define LHS (sketch (list (insn lt-idx 1 0 0)
                          (insn lt-idx 0 1 0)
                          (insn or-idx 3 4 0))
                    5
                    1
                    1))

(define RHS-sketch (get-symbolic-sketch 3 1 1))

(define x (get-sym-int))
(define c1 (get-sym-int))
(define negative-one -1)

(verify-bool-expr LHS x negative-one)

(synth-rewrite RHS-sketch LHS x c1)