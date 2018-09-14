#lang rosette

(require "../lang.rkt")
(require "../sketch.rkt")
(require "../synthesize.rkt")

(current-bitwidth #f)

;; !((0 < v0) && (min((v1 + 12), v2) < (min((v1 + 20), v2) + -144)))
;; (0 < v0) && (min((v1 + 12), v2) < (min((v1 + 20), v2) + -144))
;; (0 < v0)
;; (min((v1 + 12), v2) < (min((v1 + 20), v2) + -144))
;; (min((v1 + 12), v2)
;; (min((v1 + 20), v2) + -144)

;; R0 : v0
;; R1 : v1
;; R2 : v2
;; R3 : 0
;; R4 : 12
;; R5 : 20
;; R6 : -144
;; R7 : R3 < R0
;; R8 : R1 + R4
;; R9 : R1 + R5
;; R10: min R8 R2
;; R11: min R9 R2
;; R12: R11 + R6
;; R13: R10 < R12
;; R14: R13 && R7
;; R15: not R14

(define LHS (sketch (list (insn lt-idx 3 0 0)
                          (insn add-idx 1 4 0)
                          (insn add-idx 1 5 0)
                          (insn min-idx 8 2 0)
                          (insn min-idx 9 2 0)
                          (insn add-idx 11 6 0)
                          (insn lt-idx 10 12 0)
                          (insn and-idx 13 7 0)
                          (insn not-idx 14 0 0))
                    15
                    3
                    4))

(define RHS-sketch (get-symbolic-sketch 9 3 4))

(define v0 (get-sym-int))
(define v1 (get-sym-int))
(define v2 (get-sym-int))
(define zero 0)
(define twelve 12)
(define twenty 20)
(define negative144 -144)
(define c0 (get-sym-int))
(define c1 (get-sym-int))
(define c2 (get-sym-int))
(define c3 (get-sym-int))

;(verify-bool-expr LHS v0 v1 v2 zero twelve twenty negative144)

;(verify-bool-expr LHS v0 v1 v2 c0 c1 c2 c3)

;(synth-rewrite RHS-sketch LHS v0 v1 v2 zero twelve twenty c3)

;; (min((v1 + 12), v2) < (min((v1 + 20), v2) + -144))

;; R0 : v1
;; R1 : v2
;; R2 : 12
;; R3 : 20
;; R4 : -144
;; R5 : R0 + R2
;; R6 : min R5 R1
;; R7 : R0 + R3
;; R8 : min R7 R1
;; R9 : R8 + R4
;; R10 : R6 < R9

(define LHS-subtree (sketch (list (insn add-idx 0 2 0)
                                  (insn min-idx 5 1 0)
                                  (insn add-idx 0 3 0)
                                  (insn min-idx 7 1 0)
                                  (insn add-idx 8 4 0)
                                  (insn lt-idx 6 9 0))
                            10
                            2
                            3))

(define RHS-subtree (get-symbolic-sketch 6 2 3))

(synth-rewrite RHS-subtree LHS-subtree v1 v2 c1 c2 c3)