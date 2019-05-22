#lang rosette

;; Expr -> IntExpr | BoolExpr;
;; 
;; IntExpr -> IntExpr + IntExpr
;;         | IntExpr - IntExpr
;;         | IntExpr * IntExpr
;;         | IntExpr / IntExpr
;;         | IntExpr % IntExpr
;;         | max(IntExpr, IntExpr)
;;         | min(IntExpr, IntExpr)
;;         | Int;
;; 
;; BoolExpr -> ! BoolExpr
;;         | BoolExpr && BoolExpr
;;         | BoolExpr || BoolExpr
;;         | IntExpr < IntExpr
;;         | IntExpr - Intexpr == 0
;;         | BoolExpr == BoolExpr
;;         | Bool;

(provide (all-defined-out))

(define (div-in-Z-val x y)
  (if (= (modulo x y) 0) 0 1))

(define (euclidean-div x y)
  (cond [(and (negative? x) (negative? y)) (+ (- (quotient (abs x) y)) (div-in-Z-val x y))]
        [(negative? x) (- (- (quotient (abs x) y)) (div-in-Z-val x y)) ]
        [(negative? y) (quotient x y)]
        [else (quotient x y)]))

(define (hld-op op i1 i2)
  (op i1 i2))

(define (hld-add i1 i2)
  (hld-op + i1 i2))

(define (hld-sub i1 i2)
  (hld-op - i1 i2))

(define (hld-mul i1 i2)
  (hld-op * i1 i2))

(define (hld-max i1 i2)
  (hld-op max i1 i2))

(define (hld-min i1 i2)
  (hld-op min i1 i2))

(define (hld-div i1 i2)
  (hld-op euclidean-div i1 i2))

(define (hld-not b [i2 0])
  (if (boolean? b)
      (not b)
      'failed-typecheck))

(define (hld-and b1 b2)
  (if (and (boolean? b1) (boolean? b2))
      (and b1 b2)
      'failed-typecheck))

(define (hld-or b1 b2)
  (if (and (boolean? b1) (boolean? b2))
      (or b1 b2)
      'failed-typecheck))

(define (hld-lt i1 i2)
  (hld-op < i1 i2))

(define (hld-gt i1 i2)
  (hld-op > i1 i2))

(define (hld-le i1 i2)
  (hld-op <= i1 i2))

(define (hld-ge i1 i2)
  (hld-op >= i1 i2))

(define (hld-eq i1 i2)
  (hld-op equal? i1 i2))

(define (hld-negate i1 [i2 0])
  (- i1))

(struct operator (function arity name) #:transparent)

(define add-operator (operator hld-add 2 "+"))
(define sub-operator (operator hld-sub 2 "-"))
(define mul-operator (operator hld-mul 2 "*"))
(define neg-operator (operator hld-negate 1 "-"))
(define max-operator (operator hld-max 2 "max"))
(define min-operator (operator hld-min 2 "min"))
(define not-operator (operator hld-not 1 "not"))
(define and-operator (operator hld-and 2 "and"))
(define or-operator (operator hld-or 2 "or"))
(define lt-operator (operator hld-lt 2 "<"))
(define gt-operator (operator hld-gt 2 ">"))
(define le-operator (operator hld-le 2 "<="))
(define ge-operator (operator hld-ge 2 ">="))
(define eq-operator (operator hld-eq 2 "equal?"))
(define div-operator (operator hld-div 2 "div"))

(define operator-list
  (list add-operator
        sub-operator
        mul-operator
        neg-operator
        max-operator
        min-operator
        not-operator
        and-operator
        or-operator
        lt-operator
        gt-operator
        le-operator
        ge-operator
        eq-operator
     ;;   div-operator
        ))

(define comm-operator-list
  (list add-operator
        mul-operator
        max-operator
        min-operator
        and-operator
        or-operator
        eq-operator))

;; not sure what to do with neg or not
(define ordered-operator-list
  (list sub-operator
        neg-operator
        not-operator
        lt-operator
        gt-operator
        le-operator
        ge-operator))

(define add-idx 0)
(define sub-idx 1)
(define mul-idx 2)
(define neg-idx 3)
(define max-idx 4)
(define min-idx 5)
(define not-idx 6)
(define and-idx 7)
(define or-idx 8)
(define lt-idx 9)
(define gt-idx 10)
(define le-idx 11)
(define ge-idx 12)
(define eq-idx 13)
(define div-idx 14)

(define (get-operator-by-idx idx)
  (list-ref operator-list idx))
(define (get-operator-arity-by-idx idx)
  (operator-arity (get-operator-by-idx idx)))
(define (get-operator-name-by-idx idx)
  (operator-name (get-operator-by-idx idx)))
(define (get-operator-function-by-idx idx)
  (operator-function (get-operator-by-idx idx)))
(define (get-comm-operator-function-by-idx idx)
  (operator-function (list-ref comm-operator-list idx)))
(define (get-ordered-operator-function-by-idx idx)
  (operator-function (list-ref ordered-operator-list idx)))