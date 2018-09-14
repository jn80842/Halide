#lang rosette

(require parser-tools/yacc)

(require "parser.rkt")
(require "../lang.rkt")
(require "../sketch.rkt")

(provide build-var-lookup parser-to-hld-dsl)

(define (parser-to-hld-dsl use-wild-constants? var-hash const-hash)
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

    (exp [(NUM) (if use-wild-constants? (hash-ref const-hash $1) $1)]
         [(VAR) (hash-ref var-hash $1)]
         [(MAX OP exp COMMA exp CP) (hld-max $3 $5)]
         [(MIN OP exp COMMA exp CP) (hld-min $3 $5)]
         [(! OP exp CP) (hld-not $3)]
         [(SELECT OP exp COMMA exp COMMA exp CP) (hld-select $3 $5 $7)]
         [(exp AND exp) (hld-and $1 $3)]
         [(exp OR exp) (hld-or $1 $3)]
         [(exp + exp) (hld-add $1 $3)]
         [(exp - exp) (hld-sub $1 $3)]
         [(exp * exp) (hld-mul $1 $3)]
         [(exp / exp) (hld-div $1 $3)]
         [(exp % exp) (hld-mod $1 $3)]
         [(exp < exp) (hld-lt $1 $3)]
         [(exp > exp) (hld-lt $3 $1)] ;; x > y --> y < x
         [(exp EQ exp) (hld-eq $1 $3)]
         [(exp GE exp) (hld-not (hld-lt $1 $3))] ;; x >= y --> ! x < y
         [(exp LE exp) (hld-not (hld-lt $3 $1))] ;; x <= y --> ! y < x
         [(- exp) (hld-negate $2)]
         [(OP exp CP) $2]))))

(define (build-var-lookup prefix values)
  (make-hash (map cons (for/list ([i (range (length values))])
                         (string->symbol (string-append prefix (number->string i))))
                  values)))





    