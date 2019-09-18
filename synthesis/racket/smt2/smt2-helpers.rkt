#lang racket

(require parser-tools/yacc)

(require "lexer.rkt")
(require "../rosette-synthesis/lang.rkt")

(provide (all-defined-out))
#;(provide get-smt2-type get-smt2-root-symbol get-smt2-node-count get-smt2-node-depth
         get-smt2-variables hash-smt2-terms-by-type sort-smt2-by-node-count get-smt2-replaced-consts-expr)

(define (get-smt2-type expr-str)
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

              (exp [(NUM) 'integer]
                   [(VAR) 'unknown]
                   [(TRUE) 'boolean]
                   [(FALSE) 'boolean]
                   [(OP EQ exp exp CP) 'boolean]
                   [(OP MAX exp exp CP) 'integer]
                   [(OP MIN exp exp CP)  'integer]
                   [(OP NOT exp CP) 'boolean]
                   [(OP ITE exp exp exp CP) $4]
                   [(OP AND exp exp CP) 'boolean]
                   [(OP OR exp exp CP) 'boolean]
                   [(OP + exp exp CP) 'integer]
                   [(OP - exp exp CP) 'integer]
                   [(OP * exp exp CP) 'integer]
                   [(OP DIV exp exp CP)  'integer]
                   [(OP < exp exp CP) 'boolean]
                   [(OP > exp exp CP) 'boolean]
                   [(OP MOD exp exp CP) 'integer]
                   [(OP GE exp exp CP) 'boolean]
                   [(OP LE exp exp CP) 'boolean]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [expr-type (evaluate-smt2-parser p expr-str)])
    expr-type))

(define (hash-smt2-terms-by-type terms)
  (make-hash (map (λ (xs) (cons (get-smt2-type (first xs)) xs))
                  (group-by get-smt2-type terms))))

(define (get-smt2-root-symbol expr-str)
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
               
              (exp [(NUM) 'imm]
                   [(VAR) 'var]
                   [(TRUE) 'imm]
                   [(FALSE) 'imm]
                   [(OP EQ exp exp CP) 'EQ]
                   [(OP MAX exp exp CP) 'minmax]
                   [(OP MIN exp exp CP)  'minmax]
                   [(OP NOT exp CP) 'not]
                   [(OP ITE exp exp exp CP) 'select]
                   [(OP AND exp exp CP) 'and]
                   [(OP OR exp exp CP) 'or]
                   [(OP + exp exp CP) 'add]
                   [(OP - exp exp CP) 'sub]
                   [(OP * exp exp CP) 'mul]
                   [(OP DIV exp exp CP)  'div]
                   [(OP < exp exp CP) 'LT]
                   [(OP > exp exp CP) 'GT]
                   [(OP MOD exp exp CP) 'mod]
                   [(OP GE exp exp CP) 'GE]
                   [(OP LE exp exp CP) 'LE]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [root (evaluate-smt2-parser p expr-str)])
    root))

(define (get-smt2-node-count expr-str)
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
               
              (exp [(NUM) 0]
                   [(VAR) 0]
                   [(TRUE) 0]
                   [(FALSE) 0]
                   [(OP EQ exp exp CP) (add1 (+ $3 $4))]
                   [(OP MAX exp exp CP) (add1 (+ $3 $4))]
                   [(OP MIN exp exp CP)  (add1 (+ $3 $4))]
                   [(OP NOT exp CP) (add1 $3)]
                   [(OP ITE exp exp exp CP) (add1 (+ $3 $4 $5))]
                   [(OP AND exp exp CP) (add1 (+ $3 $4))]
                   [(OP OR exp exp CP) (add1 (+ $3 $4))]
                   [(OP + exp exp CP) (add1 (+ $3 $4))]
                   [(OP - exp exp CP) (add1 (+ $3 $4))]
                   [(OP * exp exp CP) (add1 (+ $3 $4))]
                   [(OP DIV exp exp CP)  (add1 (+ $3 $4))]
                   [(OP < exp exp CP) (add1 (+ $3 $4))]
                   [(OP > exp exp CP) (add1 (+ $3 $4))]
                   [(OP MOD exp exp CP) (add1 (+ $3 $4))]
                   [(OP GE exp exp CP) (add1 (+ $3 $4))]
                   [(OP LE exp exp CP) (add1 (+ $3 $4))]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [node-count (evaluate-smt2-parser p expr-str)])
    node-count))

(define (sort-smt2-by-node-count terms)
  (sort terms (λ (t1 t2) (< (get-smt2-node-count t1) (get-smt2-node-count t2)))))

(define (get-smt2-node-depth expr-str)
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
               
              (exp [(NUM) 1]
                   [(VAR) 1]
                   [(TRUE) 1]
                   [(FALSE) 1]
                   [(OP EQ exp exp CP) (add1 (max $3 $4))]
                   [(OP MAX exp exp CP) (add1 (max $3 $4))]
                   [(OP MIN exp exp CP) (add1 (max $3 $4))]
                   [(OP NOT exp CP) (add1 $3)]
                   [(OP ITE exp exp exp CP) (add1 (max $3 $4 $5))]
                   [(OP AND exp exp CP) (add1 (max $3 $4))]
                   [(OP OR exp exp CP) (add1 (max $3 $4))]
                   [(OP + exp exp CP) (add1 (max $3 $4))]
                   [(OP - exp exp CP) (add1 (max $3 $4))]
                   [(OP * exp exp CP) (add1 (max $3 $4))]
                   [(OP DIV exp exp CP) (add1 (max $3 $4))]
                   [(OP < exp exp CP) (add1 (max $3 $4))]
                   [(OP > exp exp CP) (add1 (max $3 $4))]
                   [(OP MOD exp exp CP) (add1 (max $3 $4))]
                   [(OP GE exp exp CP) (add1 (max $3 $4))]
                   [(OP LE exp exp CP) (add1 (max $3 $4))]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [node-depth (evaluate-smt2-parser p expr-str)])
    node-depth))

(define (get-smt2-variables expr-str)
  (let* ([varset (mutable-set)]
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
               
              (exp [(NUM) (void)]
                   [(VAR) (set-add! varset (symbol->string $1))]
                   [(TRUE) (void)]
                   [(FALSE) (void)]
                   [(OP EQ exp exp CP) (void $3 $4)]
                   [(OP NEQ exp exp CP) (void $3 $4)]
                   [(OP MAX exp exp CP) (void $3 $4)]
                   [(OP MIN exp exp CP) (void $3 $4)]
                   [(OP NOT exp CP) (void $3)]
                   [(OP ITE exp exp exp CP) (void $3 $4 $5)]
                   [(OP AND exp exp CP) (void $3 $4)]
                   [(OP OR exp exp CP) (void $3 $4)]
                   [(OP + exp exp CP) (void $3 $4)]
                   [(OP - exp exp CP) (void $3 $4)]
                   [(OP - exp CP) (void $3)]
                   [(OP * exp exp CP) (void $3 $4)]
                   [(OP DIV exp exp CP) (void $3 $4)]
                   [(OP < exp exp CP) (void $3 $4)]
                   [(OP > exp exp CP) (void $3 $4)]
                   [(OP MOD exp exp CP) (void $3 $4)]
                   [(OP GE exp exp CP) (void $3 $4)]
                   [(OP LE exp exp CP) (void $3 $4)]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [_ (evaluate-smt2-parser p expr-str)])
    (set->list varset)))

(define (get-smt2-replaced-consts-expr expr-str subst)
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

              (exp [(NUM) (let ([c $1])
                            (if (hash-has-key? subst c)
                                (hash-ref subst c)
                                c))]
                   [(VAR) (symbol->string $1)]
                   [(TRUE) "true"]
                   [(FALSE) "false"]
                   [(OP EQ exp exp CP) (format "(= ~a ~a)" $3 $4)]
                   [(OP NEQ exp exp CP) (format "(!= ~a ~a)" $3 $4)]
                   [(OP MAX exp exp CP) (format "(max ~a ~a)" $3 $4)]
                   [(OP MIN exp exp CP) (format "(min ~a ~a)" $3 $4)]
                   [(OP NOT exp CP) (format "(not ~a)" $3)]
                   [(OP ITE exp exp exp CP) (format "(ite ~a ~a ~a)" $3 $4 $5)]
                   [(OP AND exp exp CP) (format "(and ~a ~a)" $3 $4)]
                   [(OP OR exp exp CP) (format "(or ~a ~a)" $3 $4)]
                   [(OP + exp exp CP) (format "(+ ~a ~a)" $3 $4)]
                   [(OP - exp exp CP) (format "(- ~a ~a)" $3 $4)]
                   [(OP - exp CP) (format "(- ~a)" $3)]
                   [(OP * exp exp CP) (format "(* ~a ~a)" $3 $4)]
                   [(OP DIV exp exp CP) (format "(div ~a ~a)" $3 $4)]
                   [(OP < exp exp CP) (format "(< ~a ~a)" $3 $4)]
                   [(OP > exp exp CP) (format "(> ~a ~a)" $3 $4)]
                   [(OP MOD exp exp CP) (format "(mod ~a ~a)" $3 $4)]
                   [(OP GE exp exp CP) (format "(>= ~a ~a)" $3 $4)]
                   [(OP LE exp exp CP) (format "(<= ~a ~a)" $3 $4)]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [e (evaluate-smt2-parser p expr-str)])
    e))

(define (get-smt2-replaced-vars-expr expr-str subst)
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

              (exp [(NUM)  $1]
                   [(VAR) (let ([v (symbol->string $1)])
                            (if (hash-has-key? subst v)
                                (hash-ref subst v)
                                v))]
                   [(TRUE) "true"]
                   [(FALSE) "false"]
                   [(OP EQ exp exp CP) (format "(= ~a ~a)" $3 $4)]
                   [(OP NEQ exp exp CP) (format "(!= ~a ~a)" $3 $4)]
                   [(OP MAX exp exp CP) (format "(max ~a ~a)" $3 $4)]
                   [(OP MIN exp exp CP) (format "(min ~a ~a)" $3 $4)]
                   [(OP NOT exp CP) (format "(not ~a)" $3)]
                   [(OP ITE exp exp exp CP) (format "(ite ~a ~a ~a)" $3 $4 $5)]
                   [(OP AND exp exp CP) (format "(and ~a ~a)" $3 $4)]
                   [(OP OR exp exp CP) (format "(or ~a ~a)" $3 $4)]
                   [(OP + exp exp CP) (format "(+ ~a ~a)" $3 $4)]
                   [(OP - exp exp CP) (format "(- ~a ~a)" $3 $4)]
                   [(OP - exp CP) (format "(- ~a)" $3)]
                   [(OP * exp exp CP) (format "(* ~a ~a)" $3 $4)]
                   [(OP DIV exp exp CP) (format "(div ~a ~a)" $3 $4)]
                   [(OP < exp exp CP) (format "(< ~a ~a)" $3 $4)]
                   [(OP > exp exp CP) (format "(> ~a ~a)" $3 $4)]
                   [(OP MOD exp exp CP) (format "(mod ~a ~a)" $3 $4)]
                   [(OP GE exp exp CP) (format "(>= ~a ~a)" $3 $4)]
                   [(OP LE exp exp CP) (format "(<= ~a ~a)" $3 $4)]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [e (evaluate-smt2-parser p expr-str)])
    e))

(define (consistent-var-names-smt2-expr expr-str)
  (let* ([counter (vector 0)]
         [vars-hash (make-hash '())]
         [p (parser
             (start start)
             (end newline EOF)
             (tokens smt2-value-tokens smt2-op-tokens)
             (error (lambda (a b c) (void)))

             (precs (left OR AND)
                    (right EQ)
                    (left < > GE LE)
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
                   [(VAR) (let ([var $1])
                            (if (hash-has-key? vars-hash var)
                                (hash-ref vars-hash var)
                                (let* ([current-count (vector-ref counter 0)]
                                       [new-varname (format "c~a" current-count)])
                                  (vector-set! counter 0 (add1 current-count))
                                  (hash-set! vars-hash var new-varname)
                                  new-varname)))]
                   [(TRUE) "true"]
                   [(FALSE) "false"]
                   [(OP EQ exp exp CP) (format "(= ~a ~a)" $3 $4)]
                   [(OP NEQ exp exp CP) (format "(!= ~a ~a)" $3 $4)]
                   [(OP MAX exp exp CP) (format "(max ~a ~a)" $3 $4)]
                   [(OP MIN exp exp CP) (format "(min ~a ~a)" $3 $4)]
                   [(OP NOT exp CP) (format "(not ~a)" $3)]
                   [(OP ITE exp exp exp CP) (format "(ite ~a ~a ~a)" $3 $4 $5)]
                   [(OP AND exp exp CP) (format "(and ~a ~a)" $3 $4)]
                   [(OP OR exp exp CP) (format "(or ~a ~a)" $3 $4)]
                   [(OP + exp exp CP) (format "(+ ~a ~a)" $3 $4)]
                   [(OP - exp exp CP) (format "(- ~a ~a)" $3 $4)]
                   [(OP - exp CP) (format "(- ~a)" $3)]
                   [(OP * exp exp CP) (format "(* ~a ~a)" $3 $4)]
                   [(OP DIV exp exp CP) (format "(div ~a ~a)" $3 $4)]
                   [(OP < exp exp CP) (format "(< ~a ~a)" $3 $4)]
                   [(OP > exp exp CP) (format "(> ~a ~a)" $3 $4)]
                   [(OP MOD exp exp CP) (format "(mod ~a ~a)" $3 $4)]
                   [(OP GE exp exp CP) (format "(>= ~a ~a)" $3 $4)]
                   [(OP LE exp exp CP) (format "(<= ~a ~a)" $3 $4)]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [e (evaluate-smt2-parser p expr-str)])
    e))

(define (get-const-var-hash expr-str)
  (let* ([counter (vector 0)]
         [num-hash (make-hash '())]
         [p (parser
             (start start)
             (end newline EOF)
             (tokens smt2-value-tokens smt2-op-tokens)
             (error (lambda (a b c) (void)))

             (precs (left OR AND)
                    (right EQ)
                    (left < > GE LE)
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
                            (if (hash-has-key? num-hash num)
                                num
                                (let* ([current-count (vector-ref counter 0)]
                                       [new-varname (format "c~a" current-count)])
                                  (vector-set! counter 0 (add1 current-count))
                                  (hash-set! num-hash num new-varname)
                                  num)))]
                   [(VAR) (symbol->string $1)]
                   [(TRUE) "true"]
                   [(FALSE) "false"]
                   [(OP EQ exp exp CP) (format "(= ~a ~a)" $3 $4)]
                   [(OP NEQ exp exp CP) (format "(!= ~a ~a)" $3 $4)]
                   [(OP MAX exp exp CP) (format "(max ~a ~a)" $3 $4)]
                   [(OP MIN exp exp CP) (format "(min ~a ~a)" $3 $4)]
                   [(OP NOT exp CP) (format "(not ~a)" $3)]
                   [(OP ITE exp exp exp CP) (format "(ite ~a ~a ~a)" $3 $4 $5)]
                   [(OP AND exp exp CP) (format "(and ~a ~a)" $3 $4)]
                   [(OP OR exp exp CP) (format "(or ~a ~a)" $3 $4)]
                   [(OP + exp exp CP) (format "(+ ~a ~a)" $3 $4)]
                   [(OP - exp exp CP) (format "(- ~a ~a)" $3 $4)]
                   [(OP - exp CP) (format "(- ~a)" $3)]
                   [(OP * exp exp CP) (format "(* ~a ~a)" $3 $4)]
                   [(OP DIV exp exp CP) (format "(div ~a ~a)" $3 $4)]
                   [(OP < exp exp CP) (format "(< ~a ~a)" $3 $4)]
                   [(OP > exp exp CP) (format "(> ~a ~a)" $3 $4)]
                   [(OP MOD exp exp CP) (format "(mod ~a ~a)" $3 $4)]
                   [(OP GE exp exp CP) (format "(>= ~a ~a)" $3 $4)]
                   [(OP LE exp exp CP) (format "(<= ~a ~a)" $3 $4)]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [e (evaluate-smt2-parser p expr-str)])
    num-hash))

(define (evaluate-smt2-expr expr-str)
  (let ([p (parser
            (start start)
            (end newline EOF)
            (tokens smt2-value-tokens smt2-op-tokens)
            (error (lambda (a b c) (void)))

             (precs (left OR AND)
                    (right EQ)
                    (left < > GE LE)
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
                   [(VAR) $1]
                   [(TRUE) #t]
                   [(FALSE) #f]
                   [(OP EQ exp exp CP) (eq? $3 $4)]
                   [(OP NEQ exp exp CP) (not (eq? $3 $4))]
                   [(OP MAX exp exp CP) (max $3 $4)]
                   [(OP MIN exp exp CP) (min $3 $4)]
                   [(OP NOT exp CP) (not $3)]
                   [(OP ITE exp exp exp CP) (if $3 $4 $5)]
                   [(OP AND exp exp CP) (and $3 $4)]
                   [(OP OR exp exp CP) (or $3 $4)]
                   [(OP + exp exp CP) (+ $3 $4)]
                   [(OP - exp exp CP) (- $3 $4)]
                   [(OP - exp CP) (- $3)]
                   [(OP * exp exp CP) (* $3 $4)]
                   [(OP DIV exp exp CP) (euclidean-div $3 $4)]
                   [(OP < exp exp CP) (< $3 $4)]
                   [(OP > exp exp CP) (> $3 $4)]
                   [(OP MOD exp exp CP) (euclidean-mod $3 $4)]
                   [(OP GE exp exp CP) (>= $3 $4)]
                   [(OP LE exp exp CP) (<= $3 $4)]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))])
    (evaluate-smt2-parser p expr-str)))