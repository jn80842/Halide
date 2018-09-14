#lang racket

;; Modified from an example in the Racket parser tools repo
;; https://github.com/racket/parser-tools

;; Import the parser and lexer generators.
(require parser-tools/yacc
         parser-tools/lex
         (prefix-in : parser-tools/lex-sre))

(provide halide-lexer evaluate-parser value-tokens op-tokens)

(define-tokens value-tokens (NUM VAR))
(define-empty-tokens op-tokens (newline OP CP COMMA + - * / % ^ < > ! EQ GE LE EOF NEG OR AND MAX MIN SELECT TRUE FALSE))

;; A hash table to store variable values in for the calculator
(define vars (make-hash))

(define-lex-abbrevs
 (lower-letter (:/ "a" "z"))

 (upper-letter (:/ #\A #\Z))

 ;; (:/ 0 9) would not work because the lexer does not understand numbers.  (:/ #\0 #\9) is ok too.
 (digit (:/ "0" "9")))

(define halide-lexer
  (lexer
   [(eof) 'EOF]
   ;; recursively call the lexer on the remaining input after a tab or space.  Returning the
   ;; result of that operation.  This effectively skips all whitespace.
   [(:or #\tab #\space) (halide-lexer input-port)]
   ;; (token-newline) returns 'newline
   [#\newline (token-newline)]
   ;; Since (token-=) returns '=, just return the symbol directly
   [(:or "+" "-" "*" "/" "<" ">" "!" "%") (string->symbol lexeme)]
   [">=" 'GE]
   ["<=" 'LE]
   ["==" 'EQ]
   ["(" 'OP]
   [")" 'CP]
   ["," 'COMMA]
   ["||" 'OR]
   ["&&" 'AND]
   ["max" 'MAX]
   ["min" 'MIN]
   ["select" 'SELECT]
   ["true" 'TRUE]
   ["false" 'FALSE]
   ;[(:+ (:or lower-letter upper-letter)) (token-VAR (string->symbol lexeme))]
   [(:: "v" (:+ digit)) (token-VAR (string->symbol lexeme))]
   [(:+ digit) (token-NUM (string->number lexeme))]
   [(:: (:+ digit) #\. (:* digit)) (token-NUM (string->number lexeme))]))


(define parser-to-racket
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
         [(VAR) (hash-ref vars $1 (lambda () 0))]
         [(TRUE) #t]
         [(FALSE) #f]
         [(exp EQ exp) (equal? $1 $3)]
         [(MAX OP exp COMMA exp CP) (max $3 $5)]
         [(MIN OP exp COMMA exp CP) (min $3 $5)]
         [(! OP exp CP) (not $3)]
         [(SELECT OP exp COMMA exp COMMA exp CP) (if $3 $5 $7)]
         [(exp AND exp) (and $1 $3)]
         [(exp OR exp) (or $1 $3)]
         [(exp + exp) (+ $1 $3)]
         [(exp - exp) (- $1 $3)]
         [(exp * exp) (* $1 $3)]
         [(exp / exp) (/ $1 $3)]
         [(exp < exp) (< $1 $3)]
         [(exp > exp) (> $1 $3)]
         [(exp % exp) (modulo $1 $3)]
         [(exp GE exp) (>= $1 $3)]
         [(exp LE exp) (<= $1 $3)]
         [(- exp) (prec NEG) (- $2)]
         [(OP exp CP) $2]))))

(define (evaluate-parser p s)
  (let ([ip (open-input-string s)])
    (port-count-lines! ip)
    (p (λ () (halide-lexer ip)))))