#lang rosette

(require "../lang.rkt")
(require "../sketch.rkt")
(require "../synthesize.rkt")

(current-bitwidth #f)

;; v0 || ! v0 || ! v0 || v0

;; R0 : v0
;; R1 : ! R0
;; R2 : R0 || R1
;; R3 : R2 || R0
;; R4 : R3 || R1
;; R5 : R4 || R0

(define LHS (sketch (list (insn not-idx 0 0 0)
                          (insn or-idx 0 1 0)
                          (insn or-idx 2 0 0)
                          (insn or-idx 3 1 0)
                          (insn or-idx 4 0 0))
                    5
                    1
                    0))

(define RHS-sketch (get-symbolic-sketch 5 1 0))

(define-symbolic* x boolean?)

(synth-rewrite RHS-sketch LHS x)

;; R0 : v0
;; R1 : R0 == R0

(define synthed-RHS (sketch (list (insn eq-bool-idx 0 0 0)) 1 1 0))

(synth-rewrite-to-ordering RHS-sketch LHS synthed-RHS x)

;; R0 : v0
;; R1 : ! R0
;; R2 : select R0 R0 R1

(define synthed-RHS2 (sketch (list (insn not-idx 0 0 0)
                                   (insn select-bool-idx 0 0 1))
                             2 1 0))

(synth-rewrite-to-ordering RHS-sketch LHS synthed-RHS2 x)

;; R0 : v0
;; R1 : select R0 R0 R0
;; R2 : R0 == R1

(define synthed-RHS3 (sketch (list (insn select-bool-idx 0 0 0)
                                   (insn eq-bool-idx 0 1 0))
                             2 1 0))

(synth-rewrite-to-ordering RHS-sketch LHS synthed-RHS3 x)