#lang racket

(require parser-tools/yacc)
(require "parsers/parser.rkt")
(require "parsers/smt2-parser.rkt")

(provide smt2-expr-gt? get-type-smt2 get-smt2-node-depth build-smt2-node-histo node-type-list filter-by-gt)

(define node-type-list (list 'imm 'EQ 'NE 'LT 'LE 'GT 'GE 'and 'or 'not 'minmax 'add 'sub 'mod 'mul 'div 'select 'broadcast 'ramp))

(define node-type-ordering
  (make-hash (map (λ (n i) (cons n i)) node-type-list (range (length node-type-list)))))

(define (get-node-histo)
  (make-hash (map (λ (n) (cons n 0)) node-type-list)))

(define (increment-histo h symbol)
  (hash-set! h symbol (add1 (hash-ref h symbol))))

(define (node-type-gt? nt1 nt2)
  (> (hash-ref node-type-ordering nt1) (hash-ref node-type-ordering nt2)))

(define (node-histo-gt? h1 h2)
  (letrec ([f (λ (node-list) (cond [(empty? node-list) #f]
                                   [(eq? (hash-ref h1 (first node-list)) (hash-ref h2 (first node-list)))
                                    (f (cdr node-list))]
                                   [else (> (hash-ref h1 (first node-list)) (hash-ref h2 (first node-list)))]))])
    (f (reverse node-type-list))))

(define (build-node-histo expr-str)
  (let* ([node-hash (get-node-histo)]
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
               
              (exp [(NUM) (begin
                            (increment-histo node-hash 'imm)
                            $1)]
                   [(VAR) (symbol->string $1)]
                   [(TRUE) (begin
                             (increment-histo node-hash 'imm)
                             "true")]
                   [(FALSE) (begin
                              (increment-histo node-hash 'imm)
                              "false")]
                   [(UINT1) (begin
                             (increment-histo node-hash 'imm)
                             "true")]
                   [(UINT0) (begin
                              (increment-histo node-hash 'imm)
                              "false")]
                   [(exp EQ exp) (begin
                                   (increment-histo node-hash 'EQ)
                                   (format "(~a == ~a)" $1 $3))]
                   [(MAX OP exp COMMA exp CP) (begin
                                                (increment-histo node-hash 'minmax)
                                                (format "max(~a, ~a)" $3 $5))]
                   [(MIN OP exp COMMA exp CP) (begin
                                                (increment-histo node-hash 'minmax)
                                                (format "min(~a, ~a)" $3 $5))]
                   [(! OP exp CP) (begin
                                    (increment-histo node-hash 'not)
                                    (format "(! ~a )" $3))]
                   [(SELECT OP exp COMMA exp COMMA exp CP) (begin
                                                             (increment-histo node-hash 'select)
                                                             (format "select(~a, ~a, ~a)" $3 $5 $7))]
                   [(exp AND exp) (begin
                                    (increment-histo node-hash 'and)
                                    (format "(~a && ~a)" $1 $3))]
                   [(exp OR exp) (begin
                                   (increment-histo node-hash 'or)
                                   (format "(~a || ~a)" $1 $3))]
                   [(exp + exp) (begin
                                  (increment-histo node-hash 'add)
                                  (format "(~a + ~a)" $1 $3))]
                   [(exp - exp) (begin
                                  (increment-histo node-hash 'sub)
                                  (format "(~a - ~a)" $1 $3))]
                   [(exp * exp) (begin
                                  (increment-histo node-hash 'mul)
                                  (format "(~a * ~a)" $1 $3))]
                   [(exp / exp) (begin
                                  (increment-histo node-hash 'div)
                                  (format "(~a / ~a)" $1 $3))]
                   [(exp < exp) (begin
                                  (increment-histo node-hash 'LT)
                                  (format "(~a < ~a)" $1 $3))]
                   [(exp > exp) (begin
                                  (increment-histo node-hash 'GT)
                                  (format "(~a > ~a)" $1 $3))]
                   [(exp % exp) (begin
                                  (increment-histo node-hash 'mod)
                                  (format "(~a % ~a)" $1 $3))]
                   [(exp GE exp) (begin
                                   (increment-histo node-hash 'GE)
                                   (format "(~a >= ~a)" $1 $3))]
                   [(exp LE exp) (begin
                                   (increment-histo node-hash 'LE)
                                   (format "(~a <= ~a)" $1 $3))]
                   [(- exp) (prec NEG) (begin
                                         (increment-histo node-hash 'sub)
                                         (format "(- ~a)" $2))]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [full-expr (evaluate-parser p expr-str)])
    node-hash))

(define (build-smt2-node-histo expr-str)
  (let* ([node-hash (get-node-histo)]
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
               
              (exp [(NUM) (begin
                            (increment-histo node-hash 'imm)
                            $1)]
                   [(VAR) (symbol->string $1)]
                   [(TRUE) (begin
                             (increment-histo node-hash 'imm)
                             "true")]
                   [(FALSE) (begin
                              (increment-histo node-hash 'imm)
                              "false")]
                   [(OP EQ exp exp CP) (begin
                                   (increment-histo node-hash 'EQ)
                                   (format "(= ~a ~a)" $3 $4))]
                   [(OP MAX exp exp CP) (begin
                                                (increment-histo node-hash 'minmax)
                                                (format "(max ~a ~a)" $3 $4))]
                   [(OP MIN exp exp CP) (begin
                                                (increment-histo node-hash 'minmax)
                                                (format "(min ~a ~a)" $3 $4))]
                   [(OP NOT exp CP) (begin
                                    (increment-histo node-hash 'not)
                                    (format "(not ~a )" $3))]
                   [(OP ITE exp exp exp CP) (begin
                                              (increment-histo node-hash 'select)
                                              (format "(ite ~a ~a ~a)" $3 $4 $5))]
                   [(OP AND exp exp CP) (begin
                                          (increment-histo node-hash 'and)
                                          (format "(and ~a ~a)" $3 $4))]
                   [(OP OR exp exp CP) (begin
                                         (increment-histo node-hash 'or)
                                         (format "(or ~a ~a)" $3 $4))]
                   [(OP + exp exp CP) (begin
                                        (increment-histo node-hash 'add)
                                        (format "(+ ~a ~a)" $3 $4))]
                   [(OP - exp exp CP) (begin
                                        (increment-histo node-hash 'sub)
                                        (format "(- ~a ~a)" $3 $4))]
                   [(OP * exp exp CP) (begin
                                        (increment-histo node-hash 'mul)
                                        (format "(* ~a ~a)" $3 $4))]
                   [(OP DIV exp exp CP) (begin
                                          (increment-histo node-hash 'div)
                                          (format "(div ~a ~a)" $3 $4))]
                   [(OP < exp exp CP) (begin
                                        (increment-histo node-hash 'LT)
                                        (format "(< ~a ~a)" $3 $4))]
                   [(OP > exp exp CP) (begin
                                        (increment-histo node-hash 'GT)
                                        (format "(> ~a ~a)" $3 $4))]
                   [(OP MOD exp exp CP) (begin
                                          (increment-histo node-hash 'mod)
                                          (format "(mod ~a ~a)" $3 $4))]
                   [(OP GE exp exp CP) (begin
                                         (increment-histo node-hash 'GE)
                                         (format "(>= ~a ~a)" $3 $4))]
                   [(OP LE exp exp CP) (begin
                                         (increment-histo node-hash 'LE)
                                         (format "(<= ~a ~a)" $3 $4))]
                   [(OP - exp CP) (prec NEG) (begin
                                               (increment-histo node-hash 'sub)
                                               (format "(- ~a)" $3))]
                   [(- exp) (prec NEG) (begin
                                               (increment-histo node-hash 'sub)
                                               (format "(- ~a)" $2))]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [full-expr (evaluate-smt2-parser p expr-str)])
    node-hash))

#;(define (get-root-symbol-smt2 expr-str)
  (let* ([node-hash (get-node-histo)]
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
                   [(OP - exp CP) (prec NEG) 'sub]
                   [(- exp) (prec NEG) 'sub]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [root (evaluate-smt2-parser p expr-str)])
    root))

#;(define (get-type-smt2 expr-str)
  (let* ([node-hash (get-node-histo)]
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
               
              (exp [(NUM) 'integer]
                   [(VAR) 'unknown]
                   [(TRUE) 'boolean]
                   [(FALSE) 'boolean]
                   [(OP EQ exp exp CP) 'boolean]
                   [(OP MAX exp exp CP) 'integer]
                   [(OP MIN exp exp CP)  'integer]
                   [(OP NOT exp CP) 'boolean]
                   [(OP ITE exp exp exp CP) $3]
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
                   [(OP - exp CP) (prec NEG) 'integer]
                   [(- exp) (prec NEG) 'integer]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [expr-type (evaluate-smt2-parser p expr-str)])
    expr-type))

(define (root-sym-gt? e1 e2)
  (node-type-gt? (get-root-symbol-smt2 e1) (get-root-symbol-smt2 e2)))

(define (smt2-expr-gt? e1 e2)
  (let ([histo1 (build-smt2-node-histo e1)]
        [histo2 (build-smt2-node-histo e2)])
    (if (eq? histo1 histo2)
        (root-sym-gt? e1 e2)
        (node-histo-gt? histo1 histo2))))

#;(define (get-smt2-node-count expr-str)
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
                   [(OP - exp CP) (prec NEG) (add1 $3)]
                   [(- exp) (prec NEG) (add1 $2)]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [node-count (evaluate-smt2-parser p expr-str)])
    node-count))

#;(define (get-smt2-node-depth expr-str)
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
                   [(OP - exp CP) (prec NEG) (add1 $3)]
                   [(- exp) (prec NEG) (add1 $2)]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [node-depth (evaluate-smt2-parser p expr-str)])
    node-depth))

(define (filter-by-gt t terms)
  (filter (λ (e) (smt2-expr-gt? t e)) terms))