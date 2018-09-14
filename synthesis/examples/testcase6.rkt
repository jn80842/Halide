#lang rosette

(require "../lang.rkt")
(require "../sketch.rkt")
(require "../synthesize.rkt")

(current-bitwidth #f)

;; -1 < x || (x + y) < y

;; R0 : x
;; R1 : y
;; R2 : -1
;; R3 : 0 (dummy)
;; R4 : R2 < R0
;; R5 : R0 + R1
;; R6 : R5 < R1
;; R7 : R4 || R6

(define LHS (sketch (list (insn lt-idx 2 0 2)
                          (insn add-idx 0 1 2)
                          (insn lt-idx 5 1 2)
                          (insn or-idx 4 6 2))
                    7
                    2
                    1))

(define RHS-sketch (get-symbolic-sketch 4 2 1))

(define x (get-sym-int))
(define y (get-sym-int))
(define -one -1)
(define c0 (get-sym-int))

(verify-bool-expr LHS x y -one)

(verify-bool-expr LHS x y c0)

(synth-rewrite RHS-sketch LHS x y -one)