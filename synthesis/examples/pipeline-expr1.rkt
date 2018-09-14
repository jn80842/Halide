#lang rosette

(require "../lang.rkt")
(require "../sketch.rkt")
(require "../ordering.rkt")
(require "../synthesize.rkt")
(require "../parsers/parser.rkt")
(require "../parsers/halide-dsl.rkt")

(current-bitwidth #f)

(define expr "(((max(((v1 - v2)/13), -3) - max((((v1 - v2) + 27)/13), 0)) + 3) <= 1)")

;; R0 : v1
;; R1 : v2
;; R2 : 13
;; R3 : -3
;; R4 : 27
;; R5 : 0
;; R6 : 3
;; R7 : 1
;; R8 : 0 (dummy)
;; R9 : R0 - R1
;; R10 : R9 / R2
;; R11 : max R10 R3
;; R12 : R9 + R4
;; R13 : R12 / R2
;; R14 : max R13 R5
;; R15 : R11 - R14
;; R16 : R15 + R6
;; R17 : R7 > R16
;; R18 : not R17

(define LHS (sketch (list (insn sub-idx 0 1 8)
                          (insn div-idx 9 2 8)
                          (insn max-idx 10 3 8)
                          (insn add-idx 9 4 8)
                          (insn div-idx 12 2 8)
                          (insn max-idx 13 5 8)
                          (insn sub-idx 11 14 8)
                          (insn add-idx 15 6 8)
                          (insn lt-idx 7 16 8)
                          (insn not-idx 17 8 8)
                          )
                    18 2 6))

(define-symbolic* v1 integer?)
(define-symbolic* v2 integer?)

(define RHS-sketch (get-symbolic-sketch 10 2 6))

(define evaled-LHS (evaluate-parser (parser-to-hld-dsl #f (make-hash (list (cons 'v1 v1) (cons 'v2 v2))) (make-hash '())) expr))
(define evaled-RHS (apply (get-sketch-function RHS-sketch) (list v1 v2 13 -3 27 0 3 1)))
(define binding (time (synthesize #:forall (list v1 v2)
                                  #:guarantee (assert (and (and (>= 2 (get-variable-count-for-program RHS-sketch))
                                                                (equal? evaled-LHS evaled-RHS)))))))


