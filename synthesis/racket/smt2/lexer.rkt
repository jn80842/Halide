#lang racket

;; Import the parser and lexer generators.
(require parser-tools/lex
         (prefix-in : parser-tools/lex-sre))

(provide smt2-value-tokens smt2-op-tokens smt2-lexer evaluate-smt2-parser)

(define-tokens smt2-value-tokens (NUM VAR))
(define-empty-tokens smt2-op-tokens (newline OP CP COMMA + - * DIV MOD ^ < > NOT EQ NEQ GE LE EOF NEG OR AND MAX MIN ITE TRUE FALSE LII))

(define-lex-abbrevs
 (lower-letter (:/ "a" "z"))

 (upper-letter (:/ #\A #\Z))

 ;; (:/ 0 9) would not work because the lexer does not understand numbers.  (:/ #\0 #\9) is ok too.
 (digit (:/ "0" "9")))

(define smt2-lexer
  (lexer
   [(eof) 'EOF]
   ;; recursively call the lexer on the remaining input after a tab or space.  Returning the
   ;; result of that operation.  This effectively skips all whitespace.
   [(:or #\tab #\space) (smt2-lexer input-port)]
   ["VERIFYFAILURE" (smt2-lexer input-port)] ;; throw away header
   ;; (token-newline) returns 'newline
   [#\newline (token-newline)]
   [(:: (:? "-") (:+ digit)) (token-NUM (string->number lexeme))]
   ;; Since (token-=) returns '=, just return the symbol directly
   [(:or "+" "-" "*" "<" ">") (string->symbol lexeme)]
   [">=" 'GE]
   ["<=" 'LE]
   ["=" 'EQ]
   ["!=" 'NEQ]
   ["(" 'OP]
   [")" 'CP]
   ["," 'COMMA]
   ["or" 'OR]
   ["and" 'AND]
   ["max" 'MAX]
   ["min" 'MIN]
   ["ite" 'ITE]
   ["true" 'TRUE]
   ["false" 'FALSE]
   ["mod" 'MOD]
   ["div" 'DIV]
   ["not" 'NOT]
   ["likely_if_innermost" 'LII]
   ;[(:+ (:or lower-letter upper-letter)) (token-VAR (string->symbol lexeme))]
   [(:: (union "v" "i" "t" "c") (:+ digit)) (token-VAR (string->symbol lexeme))]
   [(:: (:+ digit) #\. (:* digit)) (token-NUM (string->number lexeme))]))

(define (evaluate-smt2-parser p s)
  (let ([ip (open-input-string s)])
    (port-count-lines! ip)
    (p (λ () (smt2-lexer ip)))))