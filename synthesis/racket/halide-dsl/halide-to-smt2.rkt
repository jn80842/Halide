#lang racket

(require parser-tools/yacc)

(require "lexer.rkt")

(provide halide->smt2)

(define halide->smt2-parser
  (parser

   (start start)
   (end newline EOF)
   (tokens value-tokens op-tokens)
   (error (lambda (a b c) (void)))

   (precs (left OR AND)
          (right EQ)
          (left < > GE LE)
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
    
    (exp [(NUM) $1]
         [(VAR) $1]
         [(TRUE) "true"]
         [(FALSE) "false"]
         [(UINT1) "true"]
         [(UINT0) "false"]
         [(exp EQ exp) (format "(= ~a ~a)" $1 $3)]
         [(MAX OP exp COMMA exp CP) (format "(max ~a ~a)" $3 $5)]
         [(MIN OP exp COMMA exp CP) (format "(min ~a ~a)" $3 $5)]
         [(SELECT OP exp COMMA exp COMMA exp CP) (format "(ite ~a ~a ~a)" $3 $5 $7)]
         [(exp AND exp) (format "(and ~a ~a)" $1 $3)]
         [(exp OR exp) (format "(or ~a ~a)" $1 $3)]
         [(exp + exp) (format "(+ ~a ~a)"$1 $3)]
         [(exp - exp) (format "(- ~a ~a)" $1 $3)]
         [(exp * exp) (format "(* ~a ~a)" $1 $3)]
         [(exp / exp) (format "(div ~a ~a)" $1 $3)]
         [(exp < exp) (format "(< ~a ~a)" $1 $3)]
         [(exp > exp) (format "(> ~a ~a)" $1 $3)]
         [(exp % exp) (format "(mod ~a ~a)" $1 $3)]
         [(exp GE exp) (format "(>= ~a ~a)" $1 $3)]
         [(exp LE exp) (format "(<= ~a ~a)" $1 $3)]
         [(! OP exp CP) (format "(not ~a)" $3)]
         [(OP exp CP) $2]
         [(LII exp) $2]))))

(define (halide->smt2 s)
  (evaluate-halide-parser halide->smt2-parser s))
