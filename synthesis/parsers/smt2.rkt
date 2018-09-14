#lang rosette

(require parser-tools/yacc)

(require "parser.rkt")
(require "../lang.rkt")
(require "../sketch.rkt")

(provide get-smt2-formula)

(define parser-to-smt2
  (parser

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
    
    (exp [(NUM) $1]
         [(VAR) $1]
         [(TRUE) "true"]
         [(FALSE) "false"]
         [(exp EQ exp) (format "(= ~a ~a)" $1 $3)]
         [(MAX OP exp COMMA exp CP) (format "(max ~a ~a)" $3 $5)]
         [(MIN OP exp COMMA exp CP) (format "(min ~a ~a)" $3 $5)]
         [(! OP exp CP) (format "(not ~a)" $3)]
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
         [(- exp) (prec NEG) (- $2)]
         [(OP exp CP) $2]))))

(define str "((min((v3*2), ((v4*2) + 1)) + (((v1 + v2)/4)*2)) <= ((((v1 + v2)/4) + v3)*2))")

(define (get-smt2-formula s)
  (evaluate-parser parser-to-smt2 s))
