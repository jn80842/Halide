#lang rosette

(require "constants-lang.rkt")

(current-bitwidth #f)

(define (get-sym-int)
  (begin
    (define-symbolic* x integer?)
    x))

(struct insn (op-idx arg1-idx arg2-idx) #:transparent)

(struct insn2 (comm-flag op-idx inputs-idx) #:transparent)

(define (get-sym-insn2)
  (define-symbolic* comm boolean?)
  (define-symbolic* op integer?)
  (define-symbolic* inputs integer?)
  (insn2 comm op inputs))

(define (get-comm-inputs inputs)
  (apply append (map (λ (n) (map (λ (x) (cons x (list-ref inputs n)))
                                 (list-tail inputs n)))
                     (range (length inputs)))))

(define (get-ordered-inputs inputs)
  (apply append (map (λ (x) (map (λ (n) (cons x n)) inputs)) inputs)))

(define (get-sketch-function2 sk)
  (λ args (list-ref (for/fold ([inputs args])
                              ([i (sketch-insn-list sk)])
                      (let ([comm-inputs (get-comm-inputs inputs)]
                            [ordered-inputs (get-ordered-inputs inputs)])
                        (append inputs (list (call-insn2 i comm-inputs ordered-inputs))))) (sub1 (+ (length args) (length (sketch-insn-list sk)))))))
    

(define (call-insn2 i inputs-list ordered-inputs-list)
  (if (insn2-comm-flag i)
      (let ([inputs (list-ref inputs-list (insn2-inputs-idx i))])
        ((get-comm-operator-function-by-idx (insn2-op-idx i)) (car inputs) (cdr inputs)))
      (let ([inputs (list-ref ordered-inputs-list (insn2-inputs-idx i))])
        ((get-ordered-operator-function-by-idx (insn2-op-idx i)) (car inputs) (cdr inputs)))))

(define (call-insn i registers)
  ((get-operator-function-by-idx (insn-op-idx i)) (list-ref registers (insn-arg1-idx i)) (list-ref registers (insn-arg2-idx i))))

(define (get-sym-insn)
  (define-symbolic* op integer?)
  (define-symbolic* arg1 integer?)
  (define-symbolic* arg2 integer?)
  (insn op arg1 arg2))

(struct sketch (insn-list nc-input-count const-input-count) #:transparent)

(define (get-symbolic-sketch insn-count nc-input-count const-input-count)
  (sketch (for/list ([i (range insn-count)]) (get-sym-insn)) nc-input-count const-input-count))

(define (get-symbolic-sketch2 insn-count nc-input-count const-input-count)
  (sketch (for/list ([i (range insn-count)]) (get-sym-insn2)) nc-input-count const-input-count))

(define (get-sketch-function sk)
  (letrec ([f (λ (calculated-regs i)
                (cond [(equal? (length (sketch-insn-list sk)) i) calculated-regs]
                      [else (let ([next-reg (call-insn (list-ref (sketch-insn-list sk) i) calculated-regs)])
                              (f (append calculated-regs (list next-reg)) (add1 i)))]))])
    (λ inputs (list-ref (f (append inputs (list 0)) 0) (+ (length inputs) (length (sketch-insn-list sk)))))))

(define (synthesize-predicate expr sk nc-inputs const-inputs)
  (let* ([sym-consts (map (λ (i) (get-sym-int)) const-inputs)]
         [evaled-sketch (apply (get-sketch-function sk) sym-consts)]
         [evaled-const-sketch (apply (get-sketch-function sk) const-inputs)]
         [evaled-expr (apply expr (append nc-inputs sym-consts))]
         [binding (time (synthesize #:forall (append nc-inputs sym-consts)
                                    #:guarantee (assert (and (or (not evaled-sketch) evaled-expr)
                                                             evaled-const-sketch))))])
    (if (unsat? binding)
        (displayln "no solution")
        (displayln binding))))

(define (synthesize-predicate2 expr sk nc-inputs const-inputs)
  (let* ([sym-consts (map (λ (i) (get-sym-int)) const-inputs)]
         [evaled-sketch (apply (get-sketch-function2 sk) sym-consts)]
         [evaled-const-sketch (apply (get-sketch-function2 sk) const-inputs)]
         [evaled-expr (apply expr (append nc-inputs sym-consts))]
         [binding (time (synthesize #:forall (append nc-inputs sym-consts)
                                    #:guarantee (assert (and (or (not evaled-sketch) evaled-expr)
                                                             evaled-const-sketch))))])
    (if (unsat? binding)
        (displayln "no solution")
        (displayln binding))))

;; ((((min(v3, 0) + ((v1*63) + v2))*2) + -1) <= (((v1*63) + v2)*2))
;;(((a - x)/b) >= ((((a - x)/b) + (((c - x)/b) - ((a - x)/b))) - d))

(define (testcase-expr x y z)
  (<= (+ (+ (min z 0) (* (+ (* x 63) y) 2)) -1)
      (* (+ (* x 63) y) 2)))

(define (testcase-c-expr x y z a b c d)
  (<= (+ (* (+ (min z a) (+ (* x b) y)) c) (- d))
      (* (+ (* x b) y) c)))

(define-symbolic* x integer?)
(define-symbolic* y integer?)
(define-symbolic* z integer?)
(define-symbolic* a integer?)
(define-symbolic* b integer?)
(define-symbolic* c integer?)
(define-symbolic* d integer?)

;;(define predicate-sk (get-symbolic-sketch 4 4 0))

#;(define minified-expr
  (sketch (list (insn min-idx 2 7)
                (insn mul-idx 5 8)
                (insn le-idx 9 6))
          10 3 4))

#;(define predicate-answer
  (sketch (list (insn gt-idx 5 7)
                (insn mul-idx 3 5)
                (insn ge-idx 6 9)
                (insn and-idx 8 10))
          11 3 4))