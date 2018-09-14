#lang racket

(require parser-tools/yacc
         parser-tools/lex
         (prefix-in : parser-tools/lex-sre))

(require "parser.rkt")

(provide get-insn-node-count)

(define parser-for-insn-node-count
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

    (exp [(NUM) 0]
         [(VAR) 0]
         [(MAX OP exp COMMA exp CP) (+ 1 $3 $5)]
         [(MIN OP exp COMMA exp CP) (+ 1 $3 $5)]
         [(! OP exp CP) (+ 1 $3)]
         [(SELECT OP exp COMMA exp COMMA exp CP) (+ 1 $3 $5 $7)]
         [(exp AND exp) (+ 1 $1 $3)]
         [(exp OR exp) (+ 1 $1 $3)]
         [(exp + exp) (+ 1 $1 $3)]
         [(exp - exp) (+ 1 $1 $3)]
         [(exp * exp) (+ 1 $1 $3)]
         [(exp / exp) (+ 1 $1 $3)]
         [(exp % exp) (+ 1 $1 $3)]
         [(exp < exp) (+ 1 $1 $3)]
         [(exp > exp) (+ 1 $1 $3)]
         [(exp EQ exp) (+ 1 $1 $3)]
         [(exp GE exp) (+ 1 $1 $3)]
         [(exp LE exp) (+ 1 $1 $3)]
         [(- exp) (+ 1 $2)]
         [(OP exp CP) $2]))))

(define (get-insn-node-count s)
  (evaluate-parser parser-for-insn-node-count s))