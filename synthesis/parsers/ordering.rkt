#lang racket

(require parser-tools/yacc
         parser-tools/lex
         (prefix-in : parser-tools/lex-sre))

(require "parser.rkt")
(require "../lang.rkt")
(require "../ordering.rkt")

(provide find-ordering)

(define parser-to-ordering
  (parser
   (start start)
   (end newline EOF)
   (tokens value-tokens op-tokens)
   (error (λ (a b c) (void)))
   (precs (right EQ)
          (left < > GE LE)
          (left OR AND)
          (left - +)
          (left * / %)
          (left NEG)
          (left !))

   (grammar

    (start [() #f]
           [(error start) $2]
           [(exp) $1])

    (exp [(NUM) '()]
         [(VAR) $1]
         [(MAX OP exp COMMA exp CP) (list max-idx $3 $5)]
         [(MIN OP exp COMMA exp CP) (list min-idx $3 $5)]
         [(! OP exp CP) (list not-idx $3)]
         [(SELECT OP exp COMMA exp COMMA exp CP) (list select-idx $3 $5 $7)]
         [(exp AND exp) (list and-idx $1 $3)]
         [(exp OR exp) (list or-idx $1 $3)]
         [(exp + exp) (list add-idx $1 $3)]
         [(exp - exp) (list sub-idx $1 $3)]
         [(exp * exp) (list mul-idx $1 $3)]
         [(exp / exp) (list div-idx $1 $3)]
         [(exp % exp) (list mod-idx $1 $3)]
         [(exp < exp) (list lt-idx $1 $3)]
         [(exp > exp) (list lt-idx $1 $3)] ;; x > y --> y < x
         [(exp EQ exp) (list eq-idx $1 $3)]
         [(exp GE exp) (list lt-idx not-idx $1 $3)] ;; x >= y --> ! x < y
         [(exp LE exp) (list lt-idx not-idx $1 $3)] ;; x <= y --> ! y < x
         [(- exp) (list negate-idx $2)]
         [(OP exp CP) $2]))))

#;(define (find-ordering s)
  (let ([order (get-new-ordering)]
        [var-hash (make-hash '())])
    (for-each (λ (elt) (if (symbol? elt)
                           (hash-set! var-hash elt 0)
                           (increment-ordering-operator order elt)))
              (flatten (evaluate-parser parser-to-ordering s)))
    (set-ordering-nc-count! order (hash-count var-hash))
    order))

(define (find-ordering s)
  (let ([var-hash (make-hash '())]
        [op-hash (make-hash (map (λ (i) (cons i 0)) (range (length operator-list))))])
    (for-each (λ (elt) (if (symbol? elt)
                           (hash-set! var-hash elt 0)
                           (hash-set! op-hash elt (add1 (hash-ref op-hash elt)))))
              (flatten (evaluate-parser parser-to-ordering s)))
    (ordering (hash-count var-hash) (map (λ (i) (hash-ref op-hash i)) (range (length operator-list))))))