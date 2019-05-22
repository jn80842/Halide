#lang rosette

(require "lang.rkt")

(provide (all-defined-out))

(define (get-sym-int)
  (define-symbolic* x integer?)
  x)

(define (get-sym-bool)
  (define-symbolic* b boolean?)
  b)

;; a halide expression sketch is a list of instructions and a return value
;; each instruction has an operator index and indices of the operator's arguments
;; the return value is the index of the register whose value should be returned

(struct insn (op-idx arg1-idx arg2-idx arg3-idx) #:transparent)

(define (call-insn i registers)
  ((get-operator-function-by-idx (insn-op-idx i)) (list-ref registers (insn-arg1-idx i)) (list-ref registers (insn-arg2-idx i)) (list-ref registers (insn-arg3-idx i))))

(define (call-with-divisors-insn i registers divisors)
  (let ([op-idx (insn-op-idx i)])
    (if (or (equal? op-idx div-idx) (equal? op-idx mod-idx))
        ((get-operator-function-by-idx op-idx) (list-ref registers (insn-arg1-idx i)) (list-ref divisors (insn-arg2-idx i)) (list-ref registers (insn-arg3-idx i)))
        ((get-operator-function-by-idx op-idx) (list-ref registers (insn-arg1-idx i)) (list-ref registers (insn-arg2-idx i)) (list-ref registers (insn-arg3-idx i))))))

(define (get-sym-insn)
  (define-symbolic* op integer?)
  (define-symbolic* arg1 integer?)
  (define-symbolic* arg2 integer?)
  (define-symbolic* arg3 integer?)
  (insn op arg1 arg2 arg3))

(define (has-divisor? insn)
  (or (equal? (insn-op-idx insn) div-idx)
      (equal? (insn-op-idx insn) mod-idx)))

(struct sketch (insn-list retval-idx nc-input-count const-input-count) #:transparent)

;; all sketches contain 1 dummy register to be put in unused slots
(define (get-sketch-input-count sk)
  (+ (sketch-nc-input-count sk) (sketch-const-input-count sk) 1))

(define (get-sketch-register-count sk)
  (+ (length (sketch-insn-list sk)) (get-sketch-input-count sk)))

(define (get-symbolic-sketch insn-count nc-input-count const-input-count)
  (define-symbolic* retval integer?)
  (sketch (for/list ([i (range insn-count)]) (get-sym-insn)) retval nc-input-count const-input-count))

(define (find-referenced-registers i)
  (let ([arity (get-operator-arity-by-idx (insn-op-idx i))])
    (case arity
      [(1) (list (insn-arg1-idx i))]
      [(2) (list (insn-arg1-idx i) (insn-arg2-idx i))]
      [(3) (list (insn-arg1-idx i) (insn-arg2-idx i) (insn-arg3-idx i))])))

(define (find-live-registers sk)
  (let ([input-count (get-sketch-input-count sk)])
    (letrec ([f (λ (unprocessed-idx live-regs)
                  (cond [(empty? unprocessed-idx) live-regs]
                        [(< (first unprocessed-idx) input-count) (f (cdr unprocessed-idx) (append (list (first unprocessed-idx)) live-regs))]
                        [else (f (append (cdr unprocessed-idx) (find-referenced-registers (list-ref (sketch-insn-list sk) (- (first unprocessed-idx) input-count))))
                                 (cons (first unprocessed-idx) live-regs))]))])
      (f (list (sketch-retval-idx sk)) '()))))

;; would it help if we unrolled this into a for foldl?
;; potentially not since there's only 2 branches in the recursive function
(define (get-sketch-function sk)
  (letrec ([f (λ (calculated-regs i)
                (cond [(equal? (length (sketch-insn-list sk)) i) calculated-regs]
                      [else (let ([next-reg (call-insn (list-ref (sketch-insn-list sk) i) calculated-regs)])
                              (f (append calculated-regs (list next-reg)) (add1 i)))]))])
    (λ inputs (list-ref (f (append inputs (list 0)) 0) (sketch-retval-idx sk)))))

(define (evaluate-RHS RHS-sk LHS-divisors inputs)
  (letrec ([f (λ (calculated-regs i)
                (cond [(equal? (length (sketch-insn-list RHS-sk)) i) calculated-regs]
                      [else (let ([next-reg (call-with-divisors-insn (list-ref (sketch-insn-list RHS-sk) i) calculated-regs LHS-divisors)])
                              (f (append calculated-regs (list next-reg)) (add1 i)))]))])
    (list-ref (f (append inputs (list 0)) 0) (sketch-retval-idx RHS-sk))))

(define (get-divisors sk . inputs)
  (let ([divisor-insn-indexes (filter (λ (n) (has-divisor? (list-ref (sketch-insn-list sk) n)))
                                      (range (length (sketch-insn-list sk))))])
    (for/list ([n divisor-insn-indexes])
      (evaluate-divisor sk n inputs))))

(define (evaluate-divisor sk insn-idx inputs)
  (let ([divisor-idx (insn-arg2-idx (list-ref (sketch-insn-list sk) insn-idx))])
    (apply (get-sketch-function (sketch (sketch-insn-list sk) divisor-idx (sketch-nc-input-count sk) (sketch-const-input-count sk))) inputs)))


