#lang rosette

(require "../lang.rkt")
(require "../sketch.rkt")
(require "../synthesize.rkt")

(current-bitwidth #f)

;; rewrite((select(x, y, z) + w) + select(x, u, v), select(x, y + u, z + v) + w)

;; R0 :x (bool)
;; R1 : y
;; R2 : z
;; R3 : w
;; R4 : u
;; R5 : v
;; R6 : 0 (dummy)
;; R7 : select R0 R1 R2
;; R8 : R7 + R3
;; R9 : select R0 R4 R5
;; R10 : R8 + R9

(define select-LHS (sketch (list (insn select-idx 0 1 2)
                                 (insn add-idx 7 3 0)
                                 (insn select-idx 0 4 5)
                                 (insn add-idx 8 9 0))
                           10
                           6
                           0))

(define select-RHS (get-symbolic-sketch 4 6 0))

(define x (get-sym-bool))
(define y (get-sym-int))
(define z (get-sym-int))
(define w (get-sym-int))
(define u (get-sym-int))
(define v (get-sym-int))

;(define synth1-sketch (synth-rewrite select-RHS select-LHS x y z w u v))
(synth-rewrite-var-and-op-counts select-RHS select-LHS x y z w u v)

;; synthesized in 813s (13.5min)

;;(define (sketch-function _0 _1 _2 _3 _4 _5)
;;  (define R0 _0)
;;  (define R1 _1)
;;  (define R2 _2)
;;  (define R3 _3)
;;  (define R4 _4)
;;  (define R5 _5)
;;  (define R7 (hld-add R1 R4))
;;  (define R8 (hld-add R2 R5))
;;  (define R9 (hld-select-int R0 R7 R8))
;;  (define R10 (hld-add R3 R9))
;;  R10)
;;(sketch (list (insn 1 1 4 0) (insn 1 2 5 3) (insn 15 0 7 8) (insn 1 3 9 0)) 10 6 0)