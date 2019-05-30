#lang racket

(require parser-tools/yacc)

(require "lexer.rkt")
(require "halide-helpers.rkt")

(provide get-all-substs-and-subterms)

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
               
              (exp [(NUM) (let ([t (format "i~a" (number->string $1))])
                            (set-add! subterm-set t)
                            t)]
                   ;; no need to rename variables so don't put in set
                   [(VAR) $1]
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
                   [(exp EQ exp) (let ([t (format "(~a == ~a)" $1 $3)])
                                   (set-add! subterm-set t)
                                   t)]
                   [(MAX OP exp COMMA exp CP) (let ([t (format "max(~a, ~a)" $3 $5)])
                                                (set-add! subterm-set t)
                                                t)]
                   [(MIN OP exp COMMA exp CP) (let ([t (format "min(~a, ~a)" $3 $5)])
                                                (set-add! subterm-set t)
                                                t)]
                   [(! OP exp CP) (let ([t (format "(! ~a)" $3)])
                                    (set-add! subterm-set t)
                                    t)]
                   [(SELECT OP exp COMMA exp COMMA exp CP) (let ([t (format "select(~a, ~a, ~a)" $3 $5 $7)])
                                                             (set-add! subterm-set t)
                                                             t)]
                   [(exp AND exp) (let ([t (format "(~a && ~a)" $1 $3)])
                                    (set-add! subterm-set t)
                                    t)]
                   [(exp OR exp) (let ([t (format "(~a || ~a)" $1 $3)])
                                   (set-add! subterm-set t)
                                   t)]
                   [(exp + exp) (let ([t (format "(~a + ~a)"$1 $3)])
                                  (set-add! subterm-set t)
                                  t)]
                   [(exp - exp) (let ([t (format "(~a - ~a)" $1 $3)])
                                  (set-add! subterm-set t)
                                  t)]
                   [(exp * exp) (let ([t (format "(~a * ~a)" $1 $3)])
                                  (set-add! subterm-set t)
                                  t)]
                   [(exp / exp) (let ([t (format "(~a / ~a)" $1 $3)])
                                  (set-add! subterm-set t)
                                  t)]
                   [(exp < exp) (let ([t (format "(~a < ~a)" $1 $3)])
                                  (set-add! subterm-set t)
                                  t)]
                   [(exp > exp) (let ([t (format "(~a > ~a)" $1 $3)])
                                  (set-add! subterm-set t)
                                  t)]
                   [(exp % exp) (let ([t (format "(~a % ~a)" $1 $3)])
                                  (set-add! subterm-set t)
                                  t)]
                   [(exp GE exp) (let ([t (format "(~a >= ~a)" $1 $3)])
                                   (set-add! subterm-set t)
                                   t)]
                   [(exp LE exp) (let ([t (format "(~a <= ~a)" $1 $3)])
                                   (set-add! subterm-set t)
                                   t)]
                   [(- exp) (prec NEG) (let ([t (format "(- ~a)" $2)])
                                         (set-add! subterm-set t)
                                         t)]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [full-expr (evaluate-halide-parser p str)])
    (set->list subterm-set)))

(define (escape-integer-parse expr-str)
  (let* ([p (parser
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
               
              (exp [(NUM) (format "i~a" (number->string $1))]
                   [(VAR) (symbol->string $1)]
                   [(TRUE) "true"]
                   [(FALSE) "false"]
                   [(UINT1) "true"]
                   [(UINT0) "false"]
                   [(exp EQ exp) (format "(~a == ~a)" $1 $3)]
                   [(MAX OP exp COMMA exp CP) (format "max(~a, ~a)" $3 $5)]
                   [(MIN OP exp COMMA exp CP) (format "min(~a, ~a)" $3 $5)]
                   [(! OP exp CP) (format "(! ~a )" $3)]
                   [(SELECT OP exp COMMA exp COMMA exp CP) (format "select(~a, ~a, ~a)" $3 $5 $7)]
                   [(exp AND exp) (format "(~a && ~a)" $1 $3)]
                   [(exp OR exp) (format "(~a || ~a)" $1 $3)]
                   [(exp + exp) (format "(~a + ~a)" $1 $3)]
                   [(exp - exp) (format "(~a - ~a)" $1 $3)]
                   [(exp * exp) (format "(~a * ~a)" $1 $3)]
                   [(exp / exp) (format "(~a / ~a)" $1 $3)]
                   [(exp < exp) (format "(~a < ~a)" $1 $3)]
                   [(exp > exp) (format "(~a > ~a)" $1 $3)]
                   [(exp % exp) (format "(~a % ~a)" $1 $3)]
                   [(exp GE exp) (format "(~a >= ~a)" $1 $3)]
                   [(exp LE exp) (format "(~a <= ~a)" $1 $3)]
                   [(- exp) (prec NEG) (format "(- ~a)" $2)]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [full-expr (evaluate-halide-parser p expr-str)])
    full-expr))

(define (rename-vars-parse expr-str)
  (let* ([counter (vector 0)]
         [vars-hash (make-hash '())]
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
                   [(VAR) (let ([varname $1])
                            (if (hash-has-key? vars-hash varname)
                              (hash-ref vars-hash varname)
                              (let* ([current-count (vector-ref counter 0)]
                                     [new-varname (format "v~a" current-count)])
                                (vector-set! counter 0 (add1 current-count))
                                (hash-set! vars-hash varname new-varname)
                                new-varname)))]
                   [(TRUE) "true"]
                   [(FALSE) "false"]
                   [(UINT1) "true"]
                   [(UINT0) "false"]
                   [(exp EQ exp) (format "(~a == ~a)" $1 $3)]
                   [(MAX OP exp COMMA exp CP) (format "max(~a, ~a)" $3 $5)]
                   [(MIN OP exp COMMA exp CP) (format "min(~a, ~a)" $3 $5)]
                   [(! OP exp CP) (format "(! ~a )" $3)]
                   [(SELECT OP exp COMMA exp COMMA exp CP) (format "select(~a, ~a, ~a)" $3 $5 $7)]
                   [(exp AND exp) (format "(~a && ~a)" $1 $3)]
                   [(exp OR exp) (format "(~a || ~a)" $1 $3)]
                   [(exp + exp) (format "(~a + ~a)" $1 $3)]
                   [(exp - exp) (format "(~a - ~a)" $1 $3)]
                   [(exp * exp) (format "(~a * ~a)" $1 $3)]
                   [(exp / exp) (format "(~a / ~a)" $1 $3)]
                   [(exp < exp) (format "(~a < ~a)" $1 $3)]
                   [(exp > exp) (format "(~a > ~a)" $1 $3)]
                   [(exp % exp) (format "(~a % ~a)" $1 $3)]
                   [(exp GE exp) (format "(~a >= ~a)" $1 $3)]
                   [(exp LE exp) (format "(~a <= ~a)" $1 $3)]
                   [(- exp) (prec NEG) (format "(- ~a)" $2)]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [full-expr (evaluate-halide-parser p expr-str)])
    full-expr))

  (define str "((min((v3*2), ((v4*2) + 1)) + (((v1 + v2)/4)*2)) == ((((v1 + v2)/4) + v3)*2))")
(define origstr "(<= (+ (min (* v3 2) (+ (* v4 2) 1)) (* (div (+ v1 v2) 4) 2)) (* (+ (div (+ v1 v2) 4) v3) 2))")
(define str2 "(select((0 < v0), min((v2*2), (v1 + 18)), (v2*2)) <= (v2*2))")

(define (unique-elts xs)
  (set->list (list->set xs)))

(define (get-substituted-exprs halide-str num)
  (let ([subterms (get-subterms halide-str)]
        [escaped-term (escape-integer-parse halide-str)])
    (for/list ([i (range (length subterms))])
      (string-replace escaped-term (list-ref subterms i) (format "t~a" num)))))

(define (apply-substitutions expr-str subterms subst-idxes)
  (letrec ([f (λ (str idxes) (cond [(empty? idxes) str]
                                   [(string-contains? str (list-ref subterms (first idxes)))
                                    (f (string-replace str (list-ref subterms (first idxes)) (format "t~a" (first idxes))) (cdr idxes))]
                                   [else (f str (cdr idxes))]))])
    (f expr-str subst-idxes)))

(define (get-all-substitutions halide-str)
  (let* ([subterms (get-subterms halide-str)]
         [escaped-term (escape-integer-parse halide-str)]
         [combos (combinations (range (length subterms)))])
    (unique-elts (map (λ (s) (rename-vars-parse (regexp-replace* #rx"i([0-9]+)" s "\\1")))
                      (unique-elts (for/list ([i (range (length combos))])
                                     (apply-substitutions escaped-term subterms (list-ref combos i))))))))

(define (get-all-substs-and-subterms halide-str)
  (filter (λ (e) (< (set-count (get-halide-variables e)) 7)) (unique-elts (flatten (append (get-all-substitutions halide-str) (map get-all-substitutions (get-subterms halide-str)))))))