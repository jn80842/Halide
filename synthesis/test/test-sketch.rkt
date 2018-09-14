#lang rosette

(require rackunit)

(require "../lang.rkt")
(require "../sketch.rkt")

(define x (get-sym-int))
(define y (get-sym-int))
(define zero 0)
(define -one -1)
(define -ten -10)

(define sk1 (sketch (list (insn add-idx 0 1 2))
                    3 2 0))

(check-equal? (get-sketch-input-count sk1) 3)
(check-equal? (get-sketch-register-count sk1) 4)
(check-true (unsat? (verify (assert (equal? ((get-sketch-function sk1) x y) (hld-add x y #f))))))

(define sk2 (sketch (list (insn lt-idx 1 0 1)
                          (insn lt-idx 0 2 1)
                          (insn or-idx 4 5 1))
                    6
                    1
                    2))

(check-equal? (get-sketch-input-count sk2) 4)
(check-equal? (get-sketch-register-count sk2) 7)
(check-true (unsat? (verify (assert (equal? ((get-sketch-function sk2) x -one -ten) (hld-or (hld-lt -one x #f) (hld-lt x -ten #f) #f))))))

(define sk3 (sketch (list (insn sub-idx 0 1 2))
                    6 2 3))

(check-true (unsat? (verify (assert (equal? ((get-sketch-function sk3) x y zero -one -ten) (hld-sub x y #f))))))

(define small-div-sk (sketch (list (insn div-idx 0 1 0)) 3 2 0))

(check-equal? (get-divisors small-div-sk 3 6) '(6))

(define div-sk2 (sketch (list (insn div-idx 0 1 0)
                              (insn add-idx 0 3 0)
                              (insn mod-idx 0 4 0)) 5 2 0))

(check-equal? (get-divisors div-sk2 6 3) '(3 8))
