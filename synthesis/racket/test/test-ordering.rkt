#lang racket

(require rackunit)

(require "../lang.rkt")
(require "../sketch.rkt")
(require "../ordering.rkt")

(define sk2 (sketch (list (insn lt-idx 1 0 1)
                          (insn lt-idx 0 2 1)
                          (insn or-idx 4 5 1))
                    6
                    1
                    2))

(check-equal? (get-variable-count-for-program sk2) 2)

(define add-sk (sketch (list (insn add-idx 0 1 2))
                       3 2 0))
(define sub-sk (sketch (list (insn sub-idx 0 1 2))
                       3 2 0))

;; R0 : x
;; R1 : c0
;; R2 : c1
;; R3 : 0 (dummy)
;; R4 : R0 + R1
;; R5 : R4 / R2
(define x+c0/c1 (sketch (list (insn add-idx 0 1 3)
                              (insn div-idx 4 2 3))
                        5
                        1
                        2))

;; R0 : x
;; R1 : c0
;; R2 : c1
;; R3 : 0 (dummy)
;; R4 : R0 + R1
;; R5 : R4 * R2
(define x+c0*c1 (sketch (list (insn add-idx 0 1 3)
                              (insn mul-idx 4 2 3))
                        5 1 2))

;; R0 : x
;; R1 : c0
;; R2 : 0 (dummy)
;; R3 : R0 + C0
;; R4 : R3 * R3
(define x+c0*x+c0 (sketch (list (insn add-idx 0 1 2)
                                (insn mul-idx 3 3 2))
                          4
                          1
                          1))

;; R0 : x
;; R1 : 0 (dummy)
;; R2 : R0 + R1 ;;;;;; return this register
;; R3 : R0 - R1

(define dead-reg-sk (sketch (list (insn add-idx 0 1 1)
                                  (insn sub-idx 0 1 1))
                            2 1 0))

(check-equal? (get-variable-count-for-program add-sk) 2)
(check-equal? (get-variable-count-for-program sub-sk) 2)
(check-equal? (get-variable-count-for-program x+c0/c1) 1)
(check-equal? (get-variable-count-for-program x+c0*c1) 1)
(check-equal? (get-variable-count-for-program x+c0*x+c0) 2)
(check-equal? (get-variable-count-for-program dead-reg-sk) 1)

(check-equal? (get-operator-count-for-program add-sk) '(1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
(check-equal? (get-operator-count-for-program sub-sk) '(0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
(check-equal? (get-operator-count-for-program x+c0/c1) '(1 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0))
(check-equal? (get-operator-count-for-program x+c0*c1) '(1 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0))
(check-equal? (get-operator-count-for-program x+c0*x+c0) '(2 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0)) ;; note add only gets counted once
(check-equal? (get-operator-count-for-program dead-reg-sk) '(1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) ;; note that unused insn is also counted

(check-true (sketch-histo-greater-than sub-sk add-sk))
(check-true (sketch-histo-greater-than x+c0/c1 x+c0*c1))
(check-true (sketch-histo-greater-than x+c0*x+c0 x+c0*c1)) ;; again, note add is only counted once

