#lang rosette

(require "../lang.rkt")
(require "../sketch.rkt")
(require "../synthesize.rkt")

(current-bitwidth #f)

;; rewrite(x + (y - x), y)

;; R0: x
;; R1: y
;; R2: 0 (dummy)
;; R3: R1 - R0
;; R4: R0 + R3

(define LHS (sketch (list (insn sub-idx 1 0 2)
                          (insn add-idx 0 3 2))
                    4
                    2
                    0))

(define-symbolic* x integer?)
(define-symbolic* y integer?)

(define RHS-sketch (get-symbolic-sketch 2 2 0))

(displayln "Synthesize without specified ordering")
(define synth1-sketch (synth-rewrite RHS-sketch LHS x y))
(displayln "Synthesize with ordering on variable count")
(define synth2-sketch (synth-rewrite-var-counts RHS-sketch LHS x y))
(displayln "Synthesize with ordering on variable count and naive operator counts")
(define synth3-sketch (synth-rewrite-var-and-op-counts RHS-sketch LHS x y))