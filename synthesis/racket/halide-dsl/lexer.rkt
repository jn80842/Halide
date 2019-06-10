#lang racket

;; Modified from an example in the Racket parser tools repo
;; https://github.com/racket/parser-tools

;; Import the parser and lexer generators.
(require parser-tools/lex
         (prefix-in : parser-tools/lex-sre))

(provide value-tokens op-tokens halide-lexer evaluate-halide-parser)

(define-tokens value-tokens (NUM VAR))
(define-empty-tokens op-tokens (newline OP CP COMMA + - * / % ^ < > ! EQ GE LE EOF NEG OR AND MAX MIN SELECT TRUE FALSE LII UINT1 UINT0))

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
   ["VERIFYFAILURE" (halide-lexer input-port)] ;; throw away header
   ;; (token-newline) returns 'newline
   [#\newline (token-newline)]
   [(:: (:? "-") (:+ digit)) (token-NUM (string->number lexeme))]
   ;; Since (token-=) returns '=, just return the symbol directly
   [(:or "+" "-" "*" "/" "<" ">" "!" "%") (string->symbol lexeme)]
   ["(uint1)1" 'UINT1]
   ["(uint1)0" 'UINT0]
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
   ["likely_if_innermost" 'LII]
   ;[(:+ (:or lower-letter upper-letter)) (token-VAR (string->symbol lexeme))]
   [(:: (union "v" "i" "t" "c") (:+ digit)) (token-VAR (string->symbol lexeme))]

   [(:: (:+ digit) #\. (:* digit)) (token-NUM (string->number lexeme))]))

(define (evaluate-halide-parser p s)
  (let ([ip (open-input-string s)])
    (port-count-lines! ip)
    (p (λ () (halide-lexer ip)))))