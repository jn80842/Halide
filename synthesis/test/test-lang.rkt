#lang rosette

(require rackunit)

(require "../lang.rkt")

(check-equal? (euclidean-div 6 3) 2)
(check-equal? (euclidean-div -6 3) -2)
(check-equal? (euclidean-div 6 -3) -2)
(check-equal? (euclidean-div -6 -3) 2)

(check-equal? (euclidean-div 3 2) 1)
(check-equal? (euclidean-div -3 2) -2)
(check-equal? (euclidean-div 3 -2) -1)
(check-equal? (euclidean-div -3 -2) 2)

(check-equal? (euclidean-mod 3 2) 1)
(check-equal? (euclidean-mod -3 2) 1)
(check-equal? (euclidean-mod 3 -2) 1)
(check-equal? (euclidean-mod -3 -2) 1)

(check-equal? (euclidean-mod 25 3) 1)
(check-equal? (euclidean-mod -25 3) 2)
(check-equal? (euclidean-mod 25 -3) 1)
(check-equal? (euclidean-mod -25 -3) 2)

(define three 3)
(define two 2)
(define one 1)
(define zero 0)
(define negative-one -1)
(define negative-two -2)
(define dummy 0)


(check-equal? (hld-add one negative-one dummy) zero)

(check-equal? (hld-sub one negative-one dummy) two)

(check-equal? (hld-mod three two dummy) one)

(check-equal? (hld-div three two dummy) one)

(check-equal? (hld-min negative-two zero dummy) negative-two)

(check-equal? (hld-max negative-two zero dummy) zero)

(check-true (hld-eq-int negative-one negative-one dummy))
(check-false (hld-eq-int negative-one negative-two dummy))

(check-true (hld-eq-bool #t #t dummy))
(check-true (hld-eq-bool #f #f dummy))
(check-false (hld-eq-bool #t #f dummy))
(check-false (hld-eq-bool #f #t dummy))

(check-true (hld-lt negative-two negative-one dummy))
(check-false (hld-lt negative-two negative-two dummy))
(check-false (hld-lt zero negative-two dummy))

(check-true (hld-and #t #t dummy))
(check-false (hld-and #t #f dummy))
(check-equal? (hld-and one #t dummy) 'failed-typecheck)

(check-true (hld-or #t #f dummy))
(check-false (hld-or #f #f dummy))
(check-equal? (hld-or one #f dummy) 'failed-typecheck)

(check-true (hld-not #f dummy dummy))
(check-false (hld-not #t dummy dummy))
(check-equal? (hld-not one dummy dummy) 'failed-typecheck)

(check-equal? (hld-select-int #t one two) one)
(check-equal? (hld-select-int #f one two) two)
(check-equal? (hld-select-int one one two) 'failed-typecheck)
(check-equal? (hld-select-int #t #f two) 'failed-typecheck)

(check-true (hld-select-bool #t #t #f))
(check-false (hld-select-bool #f #t #f))
(check-equal? (hld-select-bool one #t #f) 'failed-typecheck)
(check-equal? (hld-select-bool #t one two) 'failed-typecheck)