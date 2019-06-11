#lang racket

(require parser-tools/yacc)

(require "lexer.rkt")

(provide get-halide-constants get-halide-variables)

(define (get-halide-constants expr-str)
  (let* ([constset (mutable-set)]
         [p (parser
             (start start)
             (end newline EOF)
             (tokens value-tokens op-tokens)
             (error (lambda (a b c) (void)))

             (precs (right EQ)
                    (left < > GE LE)
                    (left OR AND)
                    (left - +)
                    (left * / %)
                    (left NEG)
                    (left !))

             (grammar

              (start [() #f]
                     ;; If there is an error, ignore everything before the error
                     ;; and try to start over right after the error
                     [(error start) $2]
                     [(exp) $1])

              (exp [(NUM) (set-add! constset $1)]
                   [(VAR) (void)]
                   [(TRUE) (void)]
                   [(FALSE) (void)]
                   [(UINT1) (void)]
                   [(UINT0) (void)]
                   [(exp EQ exp) (void $1 $3)]
                   [(MAX OP exp COMMA exp CP) (void $3 $5)]
                   [(MIN OP exp COMMA exp CP) (void $3 $5)]
                   [(! OP exp CP) (void $3)]
                   [(SELECT OP exp COMMA exp COMMA exp CP) (void $3 $5 $7)]
                   [(exp AND exp) (void $1 $3)]
                   [(exp OR exp) (void $1 $3)]
                   [(exp + exp) (void $1 $3)]
                   [(exp - exp) (void $1 $3)]
                   [(exp * exp) (void $1 $3)]
                   [(exp / exp) (void $1 $3)]
                   [(exp < exp) (void $1 $3)]
                   [(exp > exp) (void $1 $3)]
                   [(exp % exp) (void $1 $3)]
                   [(exp GE exp) (void $1 $3)]
                   [(exp LE exp) (void $1 $3)]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [_ (evaluate-halide-parser p expr-str)])
    constset))

(define (get-halide-variables expr-str)
  (let* ([varset (mutable-set)]
         [p (parser
             (start start)
             (end newline EOF)
             (tokens value-tokens op-tokens)
             (error (lambda (a b c) (void)))
             
             (precs (right EQ)
                    (left < > GE LE)
                    (left OR AND)
                    (left - +)
                    (left * / %)
                    (left NEG)
                    (left !))
             
             (grammar
              
              (start [() #f]
                     ;; If there is an error, ignore everything before the error
                     ;; and try to start over right after the error
                     [(error start) $2]
                     [(exp) $1])
               
              (exp [(NUM) (number->string $1)]
                   [(VAR) (set-add! varset (symbol->string $1))]
                   [(TRUE) (void)]
                   [(FALSE) (void)]
                   [(UINT1) (void)]
                   [(UINT0) (void)]
                   [(exp EQ exp) (void $1 $3)]
                   [(MAX OP exp COMMA exp CP) (void $3 $5)]
                   [(MIN OP exp COMMA exp CP) (void $3 $5)]
                   [(! OP exp CP) (void $3)]
                   [(SELECT OP exp COMMA exp COMMA exp CP) (void $3 $5 $7)]
                   [(exp AND exp) (void $1 $3)]
                   [(exp OR exp) (void $1 $3)]
                   [(exp + exp) (void $1 $3)]
                   [(exp - exp) (void $1 $3)]
                   [(exp * exp) (void $1 $3)]
                   [(exp / exp) (void $1 $3)]
                   [(exp < exp) (void $1 $3)]
                   [(exp > exp) (void $1 $3)]
                   [(exp % exp) (void $1 $3)]
                   [(exp GE exp) (void $1 $3)]
                   [(exp LE exp) (void $1 $3)]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [_ (evaluate-halide-parser p expr-str)])
    varset))