#lang racket

(require parser-tools/yacc)

(require "lexer.rkt")

(provide get-smt2-renamed-constants-expr)

(define (get-smt2-renamed-constants-expr expr-str)
  (let* ([counter (vector 0)]
         [vars-hash (make-hash '())]
         [p (parser
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
               
              (exp [(NUM) (let ([num $1])
                            (if (hash-has-key? vars-hash num)
                                (hash-ref vars-hash num)
                                (let* ([current-count (vector-ref counter 0)]
                                       [new-varname (format "c~a" current-count)])
                                  (vector-set! counter 0 (add1 current-count))
                                  (hash-set! vars-hash num new-varname)
                                  new-varname)))]
                   [(VAR) (symbol->string $1)]
                   [(TRUE) "true"]
                   [(FALSE) "false"]
                   [(OP EQ exp exp CP) (format "(= ~a ~a)" $3 $4)]
                   [(OP MAX exp exp CP) (format "(max ~a ~a)" $3 $4)]
                   [(OP MIN exp exp CP) (format "(min ~a ~a)"$3 $4)]
                   [(OP NOT exp CP) (format "(not ~a )" $3)]
                   [(OP ITE exp exp exp CP) (format "(ite ~a ~a ~a)" $3 $4 $5)]
                   [(OP AND exp exp CP) (format "(and ~a ~a)" $3 $4)]
                   [(OP OR exp exp CP) (format "(or ~a ~a)" $3 $4)]
                   [(OP + exp exp CP) (format "(+ ~a ~a)" $3 $4)]
                   [(OP - exp exp CP) (format "(- ~a ~a)" $3 $4)]
                   [(OP * exp exp CP) (format "(* ~a ~a)" $3 $4)]
                   [(OP DIV exp exp CP) (format "(div ~a ~a)" $3 $4)]
                   [(OP < exp exp CP) (format "(< ~a ~a)" $3 $4)]
                   [(OP > exp exp CP) (format "(> ~a ~a)" $3 $4)]
                   [(OP MOD exp exp CP) (format "(mod ~a ~a)" $3 $4)]
                   [(OP GE exp exp CP) (format "(>= ~a ~a)" $3 $4)]
                   [(OP LE exp exp CP) (format "(<= ~a ~a)" $3 $4)]
                   [(- exp) (prec NEG) (format "(- ~a)" $2)]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [full-expr (evaluate-smt2-parser p expr-str)])
    full-expr))
