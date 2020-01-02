#lang racket

(require parser-tools/yacc)

(require "lexer.rkt")

(provide smt2->halide)

(define (smt2->halide expr-str)
  (let* ([p (parser
             (start start)
             (end newline EOF)
             (tokens smt2-value-tokens smt2-op-tokens)
             (error (lambda (a b c) (void)))
             
             (precs (right EQ)
                    (left < > GE LE)
                    (left OR AND)
                    (left - +)
                    (left * DIV MOD)
                    (left NEG)
                    (left NOT))
             
             (grammar
              
              (start [() #f]
                     ;; If there is an error, ignore everything before the error
                     ;; and try to start over right after the error
                     [(error start) $2]
                     [(exp) $1])
               
              (exp [(NUM) $1]
                   [(VAR) (symbol->string $1)]
                   [(TRUE) "true"]
                   [(FALSE) "false"]
                   [(OP EQ exp exp CP) (format "(~a == ~a)" $3 $4)]
                   [(OP MAX exp exp CP) (format "max(~a, ~a)" $3 $4)]
                   [(OP MIN exp exp CP)  (format "min(~a, ~a)" $3 $4)]
                   [(OP NOT exp CP) (format "(! ~a)" $3)]
                   [(OP ITE exp exp exp CP) (format "select(~a, ~a, ~a)" $3 $4 $5)]
                   [(OP AND exp exp CP) (format "(~a && ~a)" $3 $4)]
                   [(OP OR exp exp CP) (format "(~a || ~a)" $3 $4)]
                   [(OP + exp exp CP) (format "(~a + ~a)" $3 $4)]
                   [(OP - exp exp CP) (format "(~a - ~a)" $3 $4)]
                   [(OP - exp CP) (format "(- ~a)" $3)]
                   [(OP * exp exp CP) (format "(~a * ~a)" $3 $4)]
                   [(OP DIV exp exp CP)  (format "(~a / ~a)" $3 $4)]
                   [(OP < exp exp CP) (format "(~a < ~a)" $3 $4)]
                   [(OP > exp exp CP) (format "(~a > ~a)" $3 $4)]
                   [(OP MOD exp exp CP) (format "(~a % ~a)" $3 $4)]
                   [(OP GE exp exp CP) (format "(~a >= ~a)" $3 $4)]
                   [(OP LE exp exp CP) (format "(~a <= ~a)" $3 $4)]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [expr-type (evaluate-smt2-parser p expr-str)])
    expr-type))
