#lang rosette

(require "../lang.rkt")
(require "../sketch.rkt")
(require "../synthesize.rkt")

(current-bitwidth #f)

;; slow

;; ((-1 < v0) || (v0 < -10))

;; R0 : v0
;; R1 : -1
;; R2 : -10
;; R3 : (dummy reg)
;; R4 : R1 < R0
;; R5 : R0 < R2
;; R6 : R4 || R5

(define (target-function v0 c0 c1)
  (hld-or (hld-lt c0 v0 #f) (hld-lt v0 c1 #f) #f))

(define LHS (sketch (list (insn lt-idx 1 0 1)
                          (insn lt-idx 0 2 1)
                          (insn or-idx 4 5 1))
                    6
                    1
                    2))

(define RHS-sketch (get-symbolic-sketch 3 1 2))

(define x (get-sym-int))
(define -one -1)
(define -ten -10)
(define zero 0)
(define c0 (get-sym-int))
(define c1 (get-sym-int))

(displayln "For LHS (-1 < v0) || (v0 < -10)")
;(verify-bool-expr LHS x -one -ten)
(displayln "For LHS ! ( (-1 < v0) || (v0 < -10) )")
;(verify-bool-expr-false LHS x -one -ten)

(displayln "For LHS (c0 < v0) || (v0 < c1)")
;(verify-bool-expr LHS x c0 c1)
(displayln "For LHS ! (co < v0) || (v0 < c1)")
;(verify-bool-expr-false LHS x c0 c1)

(synth-rewrite RHS-sketch LHS x c0 c1)