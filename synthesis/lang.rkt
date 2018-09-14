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
;;         | select(BoolExpr, IntExpr, IntExpr)
;;         | ramp(IntExpr, IntExpr)
;;         | broadcast(IntExpr)
;;         | WildInt
;;         | Int;
;; 
;; BoolExpr -> ! BoolExpr
;;         | BoolExpr && BoolExpr
;;         | BoolExpr || BoolExpr
;;         | IntExpr < IntExpr
;;         | IntExpr - Intexpr == 0
;;         | BoolExpr == BoolExpr
;;         | select(BoolExpr, BoolExpr, BoolExpr)
;;         | broadcast(BoolExpr)
;;         | WildBool
;;         | Bool;

;; non-rewrite rule rewrites:
;; a <= b --> ! b > a
;; a > b  --> b > a
;; a >= b --> ! a < b
;; a != b --> ! a == b
;; a == b --> a - b == 0
;; - a    --> 0 - a

(provide (all-defined-out))

(define (div-in-Z-val x y)
  (if (= (modulo x y) 0) 0 1))

(define (euclidean-div x y)
  (cond [(and (negative? x) (negative? y)) (+ (- (quotient (abs x) y)) (div-in-Z-val x y))]
        [(negative? x) (- (- (quotient (abs x) y)) (div-in-Z-val x y)) ]
        [(negative? y) (quotient x y)]
        [else (quotient x y)]))

;; involves casting from ints to reals and back so may not be faster than definition above
#;(define (euclidean-div x y)
  (if (< 0 y)
      (floor (/ x y))
      (ceiling (/ x y))))

(define (euclidean-mod x y)
  (cond [(and (negative? x) (negative? y)) (- (- (modulo (abs x) (abs y))) (* y (div-in-Z-val x y)))]
        [(negative? x) (+ (- (modulo (abs x) y)) (* y (div-in-Z-val x y)))]
        [(negative? y) (modulo x (abs y))]
        [else (modulo x y)]))

(define (hld-op op i1 i2)
  (op i1 i2))

(define (hld-add i1 i2 [i3 0])
  (hld-op + i1 i2))

(define (hld-sub i1 i2 [i3 0])
  (hld-op - i1 i2))

(define (hld-mul i1 i2 [i3 0])
  (hld-op * i1 i2))

(define (hld-div i1 i2 [i3 0])
  (hld-op euclidean-div i1 i2))

(define (hld-mod i1 i2 [i3 0])
  (hld-op euclidean-mod i1 i2))

(define (hld-max i1 i2 [i3 0])
  (hld-op max i1 i2))

(define (hld-min i1 i2 [i3 0])
  (hld-op min i1 i2))

;; untyped select that assumes b1 is boolean
;; in Racket everything that isn't #f is true; could conflict with C truthy values
(define (hld-select b1 i1 i2)
  (if b1 i1 i2))

(define (hld-select-int b1 i1 i2)
  (if (and (boolean? b1) (integer? i1) (integer? i2))
      (if b1 i1 i2)
      'failed-typecheck))

(define (hld-select-bool b1 b2 b3)
  (if (and (boolean? b1) (boolean? b2) (boolean? b3))
      (if b1 b2 b3)
      'failed-typecheck))

;; ramp and broadcast

(define (hld-not b [i2 0] [i3 0])
  (if (boolean? b)
      (not b)
      'failed-typecheck))

(define (hld-and b1 b2 [i3 0])
  (if (and (boolean? b1) (boolean? b2))
      (and b1 b2)
      'failed-typecheck))

(define (hld-or b1 b2 [i3 0])
  (if (and (boolean? b1) (boolean? b2))
      (or b1 b2)
      'failed-typecheck))

(define (hld-lt i1 i2 [i3 0])
  (hld-op < i1 i2))

(define (hld-eq i1 i2 [i3 0])
  (hld-op equal? i1 i2))

(define (hld-eq-int i1 i2 [i3 0])
  (hld-op equal? i1 i2))

(define (hld-eq-bool b1 b2 [i3 0])
  (if (and (boolean? b1) (boolean? b2))
      (or (and b1 b2) (nor b1 b2))
      'failed-typecheck))

(define (hld-negate i1 [i2 0] [i3 0])
  (- i1))

;; fold semantically does nothing, but is important for ordering
(define (hld-fold i1)
  i1)

;; hand up the left hand side
(define (hld-no-op i1 i2 i3)
  i1)

(struct operator (function arity name) #:transparent)

(define add-operator (operator hld-add 2 "hld-add"))
(define sub-operator (operator hld-sub 2 "hld-sub"))
(define mod-operator (operator hld-mod 2 "hld-mod"))
(define mul-operator (operator hld-mul 2 "hld-mul"))
(define div-operator (operator hld-div 2 "hld-div"))
(define min-operator (operator hld-min 2 "hld-min"))
(define max-operator (operator hld-max 2 "hld-max"))
(define eq-operator (operator hld-eq 2 "hld-eq"))
(define eq-int-operator (operator hld-eq-int 2 "hld-eq-int"))
(define eq-bool-operator (operator hld-eq-bool 2 "hld-eq-bool"))
(define lt-operator (operator hld-lt 2 "hld-lt"))
(define and-operator (operator hld-and 2 "hld-and"))
(define or-operator (operator hld-or 2 "hld-or"))
(define not-operator (operator hld-not 1 "hld-not"))
(define select-operator (operator hld-select 3 "hld-select"))
(define select-int-operator (operator hld-select-int 3 "hld-select-int"))
(define select-bool-operator (operator hld-select-bool 3 "hld-select-bool"))
(define negate-operator (operator hld-negate 1 "hld-negate"))
(define noop-operator (operator hld-no-op 2 "hld-noop"))

;; operators are in ascending strength order
;; chose an arbitrary ordering for the overloaded operators
(define operator-list
  (list noop-operator ;; 0
        add-operator ;; 1
        sub-operator ;; 2
        negate-operator ;; 3
        mod-operator ;; 4
        mul-operator ;; 5
        div-operator ;; 6
        min-operator ;; 7
        max-operator ;; 8
        eq-operator ;; 9
        lt-operator ;; 10
        and-operator ;; 11
        or-operator ;; 12
        not-operator ;; 13
        select-operator ;; 14
        ))

(define noop-idx 0)
(define add-idx 1)
(define sub-idx 2)
(define negate-idx 3)
(define mod-idx 4)
(define mul-idx 5)
(define div-idx 6)
(define min-idx 7)
(define max-idx 8)
(define eq-idx 9)
;(define eq-int-idx 9)
;(define eq-bool-idx 10)
(define lt-idx 10)
(define and-idx 11)
(define or-idx 12)
(define not-idx 13)
(define select-idx 14)
;(define select-int-idx 15)
;(define select-bool-idx 16)

(define (get-operator-by-idx idx)
  (list-ref operator-list idx))
(define (get-operator-arity-by-idx idx)
  (operator-arity (get-operator-by-idx idx)))
(define (get-operator-name-by-idx idx)
  (operator-name (get-operator-by-idx idx)))
(define (get-operator-function-by-idx idx)
  (operator-function (get-operator-by-idx idx)))