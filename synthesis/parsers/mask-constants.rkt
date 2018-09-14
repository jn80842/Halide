#lang racket

(require parser-tools/yacc
         parser-tools/lex
         (prefix-in : parser-tools/lex-sre))

(require "parser.rkt")

(provide masked-constants get-variables get-variable-count get-constant-count)

(define wild-constants-hash (make-hash))
(define variable-set (mutable-set))

(define (get-wild-constant h const)
  (let ([count (length (hash-keys h))])
    (hash-ref h const (λ () (let ([const-var (string-append "c" (number->string count))])
                              (begin (hash-set! h const const-var)
                                     const-var))))))

(define (build-variable-set s v)
  (set-add! s v)
  v)

(define string-with-masked-constants
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

    (exp [(NUM) (get-wild-constant wild-constants-hash $1)]
         [(VAR) (build-variable-set variable-set $1)]
         [(TRUE) "true"]
         [(FALSE) "false"]
         [(MAX OP exp COMMA exp CP) (format "max(~a,~a)" $3 $5)]
         [(MIN OP exp COMMA exp CP) (format "min(~a,~a)" $3 $5)]
         [(! OP exp CP) (format "!(~a)" $3)]
         [(SELECT OP exp COMMA exp COMMA exp CP) (format "select(~a,~a,~a)" $3 $5 $7)]
         [(exp AND exp) (format "~a&&~a" $1 $3)]
         [(exp OR exp) (format "~a||~a" $1 $3)]
         [(exp + exp) (format "~a+~a" $1 $3)]
         [(exp - exp) (format "~a-~a" $1 $3)]
         [(exp * exp) (format "~a*~a" $1 $3)]
         [(exp / exp) (format "~a/~a" $1 $3)]
         [(exp % exp) (format "~a%~a" $1 $3)]
         [(exp < exp) (format "~a<~a" $1 $3)]
         [(exp > exp) (format "~a>~a" $1 $3)]
         [(exp EQ exp) (format "~a==~a" $1 $3)]
         [(exp GE exp) (format "~a>=~a" $1 $3)]
         [(exp LE exp) (format "~a<=~a" $1 $3)]
         [(- exp) (format "-~a" $2)]
         [(OP exp CP) (format "(~a)" $2)]))))

(define (masked-constants s)
  (let ([ip (open-input-string s)])
    (port-count-lines! ip)
    (string-with-masked-constants (λ () (halide-lexer ip)))))
   ; (string-append (string-with-masked-constants (λ () (halide-lexer ip))) " ~~~ " s "\n")))

(define (test-parsing in-file)
  (for-each (λ (s) (begin
                     (displayln s)
                     (masked-constants s)))
            (file->lines in-file)))

(define (get-variable-count s)
  (set-clear! variable-set)
  (masked-constants s)
  (set-count variable-set))

(define (get-variables s)
  (set-clear! variable-set)
  (masked-constants s)
  (set-copy variable-set))

(define (get-constant-count s)
  (hash-clear! wild-constants-hash)
  (masked-constants s)
  (hash-count wild-constants-hash))

#;(call-with-output-file "/Users/jnewcomb/testcases/08_02_2018/processed_part5.txt" #:exists 'append
  (λ (out)
    (for-each (λ (s) (begin
                       (hash-clear! wild-constants-hash)
                       (write-string (masked-constants s) out)))
              (file->lines "/Users/jnewcomb/testcases/08_02_2018/part5.txt"))))

