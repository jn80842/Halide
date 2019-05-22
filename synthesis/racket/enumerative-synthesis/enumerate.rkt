#lang racket

(require "../smt2/smt2-gt.rkt")

(provide int-next-round bool-next-round get-int-expr-function get-bool-expr-function)

;; build up SMT2 expressions

(define (make-arity1 f inputs)
  (for/list ([e inputs])
    (f e)))

(define (make-arity2 f inputs1 inputs2)
  (flatten (for/list ([e1 inputs1])
             (for/list ([e2 inputs2])
               (f e1 e2)))))

(define (make-comm-arity2 f inputs)
  (flatten (for/list ([i (range (length inputs))])
             (for/list ([j (range (add1 i))])
               (f (list-ref inputs i) (list-ref inputs j))))))

(define (make-arity3 f inputs1 inputs2 inputs3)
  (flatten (for/list ([e1 inputs1])
             (for/list ([e2 inputs2])
               (for/list ([e3 inputs3])
                 (f e1 e2 e3))))))

;; int expressions

;; arity 1

(define (make-neg e)
  (format "(- ~a)" e))

;; arity 2

(define (make-min e1 e2)
  (format "(min ~a ~a)" e1 e2))

(define (make-max e1 e2)
  (format "(max ~a ~a)" e1 e2))

(define (make-add e1 e2)
  (format "(+ ~a ~a)" e1 e2))

(define (make-sub e1 e2)
  (format "(- ~a ~a)" e1 e2))

(define (make-mod e1 e2)
  (format "(mod ~a ~a)" e1 e2))

(define (make-mul e1 e2)
  (format "(* ~a ~a)" e1 e2))

(define (make-div e1 e2)
  (format "(div ~a ~a)" e1 e2))

;; arity 3

(define (make-select e1 e2 e3)
  (format "(ite ~a ~a ~a)" e1 e2 e3))

;; bool expressions

;; arity 1

(define (make-not e)
  (format "(not ~a)" e))

;; arity 2

(define (make-eq e1 e2)
  (format "(= ~a ~a)" e1 e2))

(define (make-lt e1 e2)
  (format "(< ~a ~a)" e1 e2))

(define (make-and e1 e2)
  (format "(and ~a ~a)" e1 e2))

(define (make-or e1 e2)
  (format "(or ~a ~a)" e1 e2))

(define (get-int-count int-count bool-count)
  (+ (* (apply + (range 1 (add1 int-count))) 4) ;; max, min, add, mul
     (* (expt int-count 2) 3) ;; sub, mod, div
     int-count ;; neg
     (* bool-count (expt int-count 2))))

(define (get-bool-count int-count bool-count)
  (+ (* (apply + (range 1 (add1 bool-count))) 2) ;; and, or
     (apply + (range 1 (add1 int-count))) ;; eq
     (expt int-count 2) ;; lt
     bool-count ;; not
     (expt bool-count 3)))

(define (int-next-round int-inputs bool-inputs)
  (append (make-comm-arity2 make-max int-inputs)
          (make-comm-arity2 make-min int-inputs)
          (make-comm-arity2 make-add int-inputs)
          (make-arity1 make-neg int-inputs)
          (make-arity2 make-sub int-inputs int-inputs)
          (make-arity2 make-mod int-inputs int-inputs)
          (make-comm-arity2 make-mul int-inputs)
          (make-arity2 make-div int-inputs int-inputs)
   (if (> (length bool-inputs) 0) (make-arity3 make-select bool-inputs int-inputs int-inputs) '())
   ))

(define (get-int-expr-function expr)
  (let ([node-types (get-less-than-term-symbols expr)])
    (λ (int-inputs bool-inputs)
      (append (if (member 'minmax node-types)
                  (append (make-comm-arity2 make-max int-inputs)
                          (make-comm-arity2 make-min int-inputs))
                  '())
              (if (member 'add node-types) (make-comm-arity2 make-add int-inputs) '())
              (if (member 'sub node-types) (append (make-arity1 make-neg int-inputs) (make-arity2 make-sub int-inputs int-inputs)) '())
              (if (member 'mod node-types) (make-arity2 make-mod int-inputs int-inputs) '())
              (if (member 'mul node-types) (make-comm-arity2 make-mul int-inputs) '())
              (if (member 'div node-types) (make-arity2 make-div int-inputs int-inputs) '())
              (if (and (member 'select node-types) (> (length bool-inputs) 0))
                  (make-arity3 make-select bool-inputs int-inputs int-inputs) '())))))

(define (get-bool-expr-function expr)
  (let ([node-types (get-less-than-term-symbols expr)])
    (λ (int-inputs bool-inputs)
      (append (if (member 'EQ node-types) (make-comm-arity2 make-eq bool-inputs) '())
              (if (member 'LT node-types) (make-arity2 make-lt int-inputs int-inputs) '())
              (if (member 'and node-types) (make-comm-arity2 make-and bool-inputs) '())
              (if (member 'or node-types) (make-comm-arity2 make-or bool-inputs) '())
              (if (member 'not node-types) (make-arity1 make-not bool-inputs) '())
              (if (member 'select node-types) (make-arity3 bool-inputs bool-inputs bool-inputs) '())))))

(define integer-expr-templates
  (make-hash (list (cons 'arity2-comm (list "(max ~a ~a)" "(min ~a ~a)" "(+ ~a ~a)" "(* ~a ~a)"))
                   (cons 'arity1 (list "(- ~a)"))
                   (cons 'arity2 (list "(- ~a ~a)" "(mod ~a ~a)" "(div ~a ~a)"))
                   (cons 'arity3 (list "(ite ~a ~a ~a)")))))

(define boolean-expr-templates
  (make-hash (list (cons 'arity2-comm (list "(= ~a ~a)" "(and ~a ~a)" "(or ~a ~a)"))
                   (cons 'arity1 (list "(not ~a)"))
                   (cons 'arity3 (list "(ite ~a ~a ~a)")))))

(define (bool-next-round int-inputs bool-inputs)
  (flatten (append
            (if (> (length int-inputs) 0)
                (append (make-comm-arity2 make-eq int-inputs)
                        (make-arity2 make-lt int-inputs int-inputs))
                '())
            (if (> (length bool-inputs) 0)
                (append (make-comm-arity2 make-and bool-inputs)
                        (make-comm-arity2 make-or bool-inputs)
                        (make-arity1 make-not bool-inputs)
                        (make-arity3 make-select bool-inputs bool-inputs bool-inputs))
                '())
            )))

