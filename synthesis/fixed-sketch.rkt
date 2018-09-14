#lang rosette

(require "fixed-lang.rkt")

(current-bitwidth #f)

;; R0 - R3 : choose from index into inputs
;; R4 : $op 0 1
;; R5 : $op 2 3
;; R6 : $op 4 5
;; return value of R6

(provide fixed-sketch get-sym-hld-int get-symbolic-sketch get-sketch-function get-var-count get-op-count histo-greater-than)

(define (symbolic-op op x y)
  (if (equal? op add-idx)
      (hld-add x y)
      (if (equal? op sub-idx)
          (hld-sub x y)
          (if (equal? op mod-idx)
              (hld-mod x y)
              (if (equal? op div-idx)
                  (hld-div x y)
                  (if (equal? op min-idx)
                      (hld-min x y)
                      (if (equal? op max-idx)
                          (hld-max x y)
                          (if (equal? op eq-idx)
                              (hld-eq x y)
                              (if (equal? op lt-idx)
                                  (hld-lt x y)
                                  (if (equal? op and-idx)
                                      (hld-and x y)
                                      (if (equal? op or-idx)
                                          (hld-or x y)
                                          (if (equal? op not-idx)
                                              (hld-not x y)
                                              (if (equal? op select-idx)
                                                  (hld-select x y)
                                                  (if (equal? op union-idx)
                                                      (hld-union x y)
                                                      (hld-no-op x y)))))))))))))))

(define (symbolic-op2 op hld-x hld-y)
  (let ([x (hld-int-val hld-x)]
        [y (hld-int-val hld-y)])
    (hld-int (|| (and (equal? op mod-idx) (eq? 0 y))
                 (and (equal? op div-idx) (eq? 0 y)))
             #f
             (if (equal? op add-idx)
                 (+ x y)
                 (if (equal? op sub-idx)
                     (- x y)
                     (if (equal? op mod-idx)
                         (modulo x y)
                         (if (equal? op div-idx)
                             (quotient x y)
                             (if (equal? op min-idx)
                                 (min x y)
                                 (if (equal? op max-idx)
                                     (max x y)
                                     (if (equal? op eq-idx)
                                         (equal? x y)
                                         (if (equal? op lt-idx)
                                             (< x y)
                                             (if (equal? op and-idx)
                                                 (and x y)
                                                 (if (equal? op or-idx)
                                                     (or x y)
                                                     (if (equal? op not-idx)
                                                         (not x)
                                                         x))))))))))))))

(define (get-sym-hld-int)
  (define-symbolic* int integer?)
  (hld-int #f #f int))

(struct fixed-sketch (depth operators input-indexes) #:transparent)

(define (get-sketch-function sk)
  (letrec ([f (λ (calculated-regs op-i input-i)
                (if (equal? op-i (sub1 (expt 2 (fixed-sketch-depth sk))))
                    calculated-regs
                    (f (append calculated-regs (list ((get-operator-function-by-idx (list-ref (fixed-sketch-operators sk) op-i))
                                                      (list-ref calculated-regs input-i) (list-ref calculated-regs (add1 input-i)))))
                               (add1 op-i) (+ input-i 2))))])
   (λ inputs (let ([input-regs (for/list ([i (range (expt 2 (fixed-sketch-depth sk)))]) (list-ref inputs (list-ref (fixed-sketch-input-indexes sk) i)))])
               (list-ref (f input-regs 0 0) (sub1 (+ (expt 2 (fixed-sketch-depth sk)) (sub1 (expt 2 (fixed-sketch-depth sk))))))))))

(define (get-sketch-function2 sk)
  (λ (x y z w)
    ((get-operator-function-by-idx (list-ref (fixed-sketch-operators sk) 2)) ((get-operator-function-by-idx (list-ref (fixed-sketch-operators sk) 0)) x y)
                                                                             ((get-operator-function-by-idx (list-ref (fixed-sketch-operators sk) 1)) z w))))

(define (get-symbolic-input)
  (define-symbolic* i integer?)
  i)

(define (get-symbolic-operator)
  (define-symbolic* op integer?)
  op)

(define (get-symbolic-sketch d)
  (fixed-sketch d
                (for/list ([i (range (sub1 (expt 2 d)))]) (get-symbolic-operator))
                (for/list ([i (range (expt 2 d))]) (get-symbolic-input))))

(define (get-var-count sk)
  (let ([lt-3 (λ (i) (< i 3))])
    (+ (if (lt-3 (list-ref (fixed-sketch-input-indexes sk) 0)) 1 0)
       (if (lt-3 (list-ref (fixed-sketch-input-indexes sk) 1)) 1 0)
       (if (lt-3 (list-ref (fixed-sketch-input-indexes sk) 2)) 1 0)
       (if (lt-3 (list-ref (fixed-sketch-input-indexes sk) 3)) 1 0))))

(define (sum-operator-use op sk)
  (+ (if (equal? op (list-ref (fixed-sketch-operators sk) 0)) 1 0)
     (if (equal? op (list-ref (fixed-sketch-operators sk) 1)) 1 0)
     (if (equal? op (list-ref (fixed-sketch-operators sk) 2)) 1 0)))

(define (get-op-count sk)
  (map (λ (op) (sum-operator-use op sk)) (range (length operator-list))))

(define (histo-greater-than h1 h2)
  (findf (λ (x) (not (equal? x 'tie)))
         (reverse (map (λ (count1 count2)
                         (if (equal? count1 count2)
                             'tie
                             (> count1 count2))) h1 h2))))


