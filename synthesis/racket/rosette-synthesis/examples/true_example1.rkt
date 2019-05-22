#lang rosette

;; slow

(require "../lang.rkt")
(require "../sketch.rkt")
(require "../synthesize.rkt")

(current-bitwidth #f)

;; ((((0 - ((v0 - v1) % 2))/2) + (((v0 - v1) + -7)/2)) <= (((v0 - v1) + -7)/2))

;; R0 : v0
;; R1 : v1
;; R2 : c0 (0)
;; R3 : c1 (2)
;; R4 : c2 (7)
;; R5 : 0 (dummy)
;; R6 : R0 - R1
;; R7 : R6 % R4
;; R8 : R2 - R7
;; R9 : R8 / R3
;; R10 : - R4
;; R11 : R6 + R10
;; R12 : R11 / R3
;; R13 : R9 + R12
;; R14 : R13 < R12
;; R15 : ! R14

(define LHS (sketch (list (insn sub-idx 0 1 2)
                          (insn mod-idx 6 4 2)
                          (insn sub-idx 2 7 2)
                          (insn div-idx 8 3 2)
                          (insn negate-idx 4 2 2)
                          (insn add-idx 6 10 2)
                          (insn div-idx 11 3 2)
                          (insn add-idx 9 12 2)
                          (insn lt-idx 13 12 2)
                          (insn not-idx 14 2 2))
                    14
                    2
                    3))

(define RHS-sketch (get-symbolic-sketch 10 2 3))

(define x (get-sym-int))
(define y (get-sym-int))
(define zero 0)
(define two 2)
(define seven 7)

(synth-rewrite RHS-sketch LHS x y zero two seven)