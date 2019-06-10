#lang racket

(require rackunit)

(require "smt2-to-halide.rkt")

(check-equal? (smt2->halide "(<= (+ (* (min (div (- v1 v2) 4) -3) 4) v2) v2)") "(((min(((v1 - v2) / 4), -3) * 4) + v2) <= v2)")