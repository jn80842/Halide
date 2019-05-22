#lang rosette

(require parser-tools/yacc)

(require "parser.rkt")
(require "../lang.rkt")

(provide build-var-lookup parser-to-hld-dsl)

(define (parser-to-hld-dsl use-wild-constants? var-hash const-hash)
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

    (exp [(NUM) (if use-wild-constants? (hash-ref const-hash $1) $1)]
         [(VAR) (hash-ref var-hash $1)]
         [(MAX OP exp COMMA exp CP) (hld-max $3 $5)]
         [(MIN OP exp COMMA exp CP) (hld-min $3 $5)]
         [(! OP exp CP) (hld-not $3)]
         [(SELECT OP exp COMMA exp COMMA exp CP) (hld-select $3 $5 $7)]
         [(exp AND exp) (hld-and $1 $3)]
         [(exp OR exp) (hld-or $1 $3)]
         [(exp + exp) (hld-add $1 $3)]
         [(exp - exp) (hld-sub $1 $3)]
         [(exp * exp) (hld-mul $1 $3)]
         [(exp / exp) (hld-div $1 $3)]
         [(exp % exp) (hld-mod $1 $3)]
         [(exp < exp) (hld-lt $1 $3)]
         [(exp > exp) (hld-lt $3 $1)] ;; x > y --> y < x
         [(exp EQ exp) (hld-eq $1 $3)]
         [(exp GE exp) (hld-not (hld-lt $1 $3))] ;; x >= y --> ! x < y
         [(exp LE exp) (hld-not (hld-lt $3 $1))] ;; x <= y --> ! y < x
         [(- exp) (hld-negate $2)]
         [(OP exp CP) $2]))))

(define (build-var-lookup prefix values)
  (make-hash (map cons (for/list ([i (range (length values))])
                         (string->symbol (string-append prefix (number->string i))))
                  values)))

(provide (all-defined-out))

(define (get-halide-renamed-constants expr-str)
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
         [full-expr (evaluate-parser p expr-str)])
    full-expr))







    