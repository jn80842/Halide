#lang rosette

(require parser-tools/yacc)

(require "parser.rkt")
(require "smt2.rkt")
(require "../lang.rkt")
(require "../sketch.rkt")

;(provide get-smt2-formula)

(define (get-subterms str)
  (let* ([subterm-set (list->mutable-set '())]
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
               
              (exp [(NUM) (let ([t $1])
                            (set-add! subterm-set (number->string t))
                            t)]
                   [(VAR) (let ([t $1])
                            (set-add! subterm-set (symbol->string t))
                            t)]
                   [(TRUE) (let ([t "true"])
                             (set-add! subterm-set t)
                             t)]
                   [(FALSE) (let ([t "false"])
                              (set-add! subterm-set t)
                              t)]
                   [(UINT1) (let ([t "true"])
                             (set-add! subterm-set t)
                             t)]
                   [(UINT0) (let ([t "false"])
                              (set-add! subterm-set t)
                              t)]
                   [(exp EQ exp) (let ([t (format "(= ~a ~a)" $1 $3)])
                                   (set-add! subterm-set t)
                                   t)]
                   [(MAX OP exp COMMA exp CP) (let ([t (format "(max ~a ~a)" $3 $5)])
                                                (set-add! subterm-set t)
                                                t)]
                   [(MIN OP exp COMMA exp CP) (let ([t (format "(min ~a ~a)" $3 $5)])
                                                (set-add! subterm-set t)
                                                t)]
                   [(! OP exp CP) (let ([t (format "(not ~a)" $3)])
                                    (set-add! subterm-set t)
                                    t)]
                   [(SELECT OP exp COMMA exp COMMA exp CP) (let ([t (format "(ite ~a ~a ~a)" $3 $5 $7)])
                                                             (set-add! subterm-set t)
                                                             t)]
                   [(exp AND exp) (let ([t (format "(and ~a ~a)" $1 $3)])
                                    (set-add! subterm-set t)
                                    t)]
                   [(exp OR exp) (let ([t (format "(or ~a ~a)" $1 $3)])
                                   (set-add! subterm-set t)
                                   t)]
                   [(exp + exp) (let ([t (format "(+ ~a ~a)"$1 $3)])
                                  (set-add! subterm-set t)
                                  t)]
                   [(exp - exp) (let ([t (format "(- ~a ~a)" $1 $3)])
                                  (set-add! subterm-set t)
                                  t)]
                   [(exp * exp) (let ([t (format "(* ~a ~a)" $1 $3)])
                                  (set-add! subterm-set t)
                                  t)]
                   [(exp / exp) (let ([t (format "(div ~a ~a)" $1 $3)])
                                  (set-add! subterm-set t)
                                  t)]
                   [(exp < exp) (let ([t (format "(< ~a ~a)" $1 $3)])
                                  (set-add! subterm-set t)
                                  t)]
                   [(exp > exp) (let ([t (format "(> ~a ~a)" $1 $3)])
                                  (set-add! subterm-set t)
                                  t)]
                   [(exp % exp) (let ([t (format "(mod ~a ~a)" $1 $3)])
                                  (set-add! subterm-set t)
                                  t)]
                   [(exp GE exp) (let ([t (format "(>= ~a ~a)" $1 $3)])
                                   (set-add! subterm-set t)
                                   t)]
                   [(exp LE exp) (let ([t (format "(<= ~a ~a)" $1 $3)])
                                   (set-add! subterm-set t)
                                   t)]
                   [(- exp) (prec NEG) (let ([t (format "(- ~a)" $2)])
                                         (set-add! subterm-set t)
                                         t)]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [full-expr (evaluate-parser p str)])
    (set->list subterm-set)))
  
  (define str "((min((v3*2), ((v4*2) + 1)) + (((v1 + v2)/4)*2)) == ((((v1 + v2)/4) + v3)*2))")
(define origstr "(<= (+ (min (* v3 2) (+ (* v4 2) 1)) (* (div (+ v1 v2) 4) 2)) (* (+ (div (+ v1 v2) 4) v3) 2))")
  
  #;(define (get-smt2-formula s)
      (evaluate-parser parser-to-smt2 s))

(define (get-substituted-exprs halide-str)
  (let ([smt-str (get-smt2-formula halide-str)]
        [subterms (get-subterms halide-str)])
    (for/list ([i (range (length subterms))])
      (string-replace smt-str (list-ref subterms i) (format "t~a" i)))))
