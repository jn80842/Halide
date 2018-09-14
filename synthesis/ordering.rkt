#lang rosette

(require "lang.rkt")
(require "sketch.rkt")

(provide (all-defined-out))

(struct ordering ([nc-count #:mutable] histo-count) #:transparent)

(define (get-variable-count-for-program sk)
  (letrec ([f (λ (calculated-counts i)
                (cond [(equal? (length (sketch-insn-list sk)) i) calculated-counts]
                      [else (let ([next-reg-count (get-insn-var-count (list-ref (sketch-insn-list sk) i) calculated-counts)])
                              (f (append calculated-counts (list next-reg-count)) (add1 i)))]))])
    (list-ref (f (append (make-list (sketch-nc-input-count sk) 1) (make-list (add1 (sketch-const-input-count sk)) 0)) 0) (sketch-retval-idx sk))))

;; let the solver choose cheap instructions
(define (get-insn-var-count i var-counts)
  (+ (list-ref var-counts (insn-arg1-idx i)) (list-ref var-counts (insn-arg2-idx i)) (list-ref var-counts (insn-arg3-idx i))))

(define (get-operator-count-for-program sk)
  (let ([ops (map (λ (i) (insn-op-idx i)) (sketch-insn-list sk))])
    (map (λ (op) (apply + (map (λ (i) (if (equal? i op) 1 0)) ops))) (range (length operator-list)))))

(define (sketch-histo-greater-than sk1 sk2)
  (histo-greater-than (get-operator-count-for-program sk1) (get-operator-count-for-program sk2)))

(define (histo-greater-than h1 h2)
  (findf (λ (x) (not (equal? x 'tie)))
         (reverse (map (λ (count1 count2)
                         (if (equal? count1 count2)
                             'tie
                             (> count1 count2))) h1 h2))))

(define minimum-ordered-sketch (sketch '() 0 1 0))