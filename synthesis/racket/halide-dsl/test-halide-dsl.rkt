#lang racket

(require rackunit)
(require "halide-to-smt2.rkt")

(check-equal? (halide->smt2 "(((min(((v1 - v2) / 4), -3) * 4) + v2) <= v2)") "(<= (+ (* (min (div (- v1 v2) 4) -3) 4) v2) v2)")
