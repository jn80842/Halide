#lang rosette

(require "../fixed-lang.rkt")
(require "../fixed-sketch.rkt")

(current-bitwidth #f)

(define sk2
  (fixed-sketch 3 (list noop-idx sub-idx noop-idx noop-idx min-idx noop-idx add-idx)
                (list 0 3 1 2 2 3 3 3)))

(define RHS-sketch (get-symbolic-sketch 3))

(define inputs (for/list ([i (range 8)]) (get-sym-hld-int)))

(let ([evaled-LHS (apply (get-sketch-function sk2) inputs)]
      [evaled-RHS (apply (get-sketch-function RHS-sketch) inputs)])
  (time (synthesize #:forall (symbolics inputs)
                    #:guarantee (assert (and (> (get-var-count sk2) (get-var-count RHS-sketch))
                                             (histo-greater-than (get-op-count sk2) (get-op-count RHS-sketch))
                                             (equal? evaled-LHS evaled-RHS))))))