#lang rosette

(require "../lang.rkt")
(require "../sketch.rkt")
(require "../synthesize.rkt")

(current-bitwidth #f)

;;  (((0 - ((v0 + 7) % 136))/136) == -1)

;; R0 : v0
;; R1 : 0
;; R2 : 7
;; R3 : 136
;; R4 : -1
;; R5 : R0 + R2
;; R6 : R5 % R3
;; R7 : R1 - R6
;; R8 : R7 / R3
;; R9 : R8 == R4

(define LHS (sketch (list (insn add-idx 0 2 0)
                          (insn mod-idx 5 3 0)
                          (insn sub-idx 1 6 0)
                          (insn div-idx 7 3 0)
                          (insn eq-idx 8 4 0))
                    9
                    1
                    4))

(define RHS-sketch (get-symbolic-sketch 5 1 4))

(define x (get-sym-int))
(define zero 0)
(define one 7)
(define two 136)
(define three -1)
(define c0 (get-sym-int))
(define c1 (get-sym-int))
(define c2 (get-sym-int))
(define c3 (get-sym-int))

(verify-bool-expr LHS x zero one two three)

(synth-rewrite RHS-sketch LHS x zero one two three)