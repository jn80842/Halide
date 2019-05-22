#lang rosette

(require "../fixed-lang.rkt")
(require "../fixed-sketch.rkt")

(current-bitwidth #f)

;; x + y - x
(define example-sk
  (fixed-sketch 2 (list add-idx noop-idx sub-idx) (list 0 1 0 3 )))

(define RHS-sketch (get-symbolic-sketch 2))

(define x (get-sym-hld-int))
(define y (get-sym-hld-int))
(define z (get-sym-hld-int))
(define zero (hld-int #f #f 0))
(define negative-one (hld-int #f #f -1))
(define c0 (get-sym-hld-int))

(define a (get-sym-hld-int))
(define b (get-sym-hld-int))
(define c (get-sym-hld-int))
(define d (get-sym-hld-int))

(let ([evaled-LHS (apply (get-sketch-function example-sk) (list x y z zero))]
      [evaled-RHS (apply (get-sketch-function RHS-sketch) (list x y z zero))])
  (time (synthesize #:forall (symbolics (list x y z))
                    #:guarantee (assert (and (< (get-var-count RHS-sketch) (get-var-count example-sk))
                                             (histo-greater-than (get-op-count example-sk) (get-op-count RHS-sketch))
                                             (equal? evaled-LHS evaled-RHS))))))

;; -1 < x || x < -1
(define example-sk2
  (fixed-sketch 2 (list lt-idx lt-idx or-idx) (list 3 0 0 3)))

(let ([evaled-LHS (apply (get-sketch-function example-sk2) (list x y z negative-one))]
      [evaled-RHS (apply (get-sketch-function RHS-sketch) (list x y z negative-one))])
  (time (synthesize #:forall (symbolics (list x y z))
                    #:guarantee (assert (and (< (get-var-count RHS-sketch) (get-var-count example-sk2))
                                             (histo-greater-than (get-op-count example-sk2) (get-op-count RHS-sketch))
                                             (equal? evaled-LHS evaled-RHS))))))