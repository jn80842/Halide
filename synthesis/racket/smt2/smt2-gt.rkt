#lang racket

(require parser-tools/yacc)

(require "lexer.rkt")
(require "smt2-helpers.rkt")

(provide smt2-expr-gt? get-less-than-term-symbols)

(define node-type-list (list 'imm 'EQ 'NE 'LT 'LE 'GT 'GE 'and 'or 'not 'minmax 'add 'sub 'mod 'mul 'div 'select 'broadcast 'ramp))

(define node-type-ordering
  (make-hash (map (λ (n i) (cons n i)) node-type-list (range (length node-type-list)))))

(define (get-node-histo)
  (make-hash (map (λ (n) (cons n 0)) node-type-list)))

(define (increment-histo h symbol . leaves)
  (hash-set! h symbol (add1 (hash-ref h symbol))))

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
               
              (exp [(NUM) (increment-histo node-hash 'imm $1)]
                   [(VAR) $1]
                   [(TRUE) (increment-histo node-hash 'imm)]
                   [(FALSE) (increment-histo node-hash 'imm)]
                   [(OP EQ exp exp CP)  (increment-histo node-hash 'EQ $3 $4)]
                   [(OP MAX exp exp CP) (increment-histo node-hash 'minmax $3 $4)]
                   [(OP MIN exp exp CP) (increment-histo node-hash 'minmax $3 $4)]
                   [(OP NOT exp CP) (increment-histo node-hash 'not $3)]
                   [(OP ITE exp exp exp CP) (increment-histo node-hash 'select $3 $4 $5)]
                   [(OP AND exp exp CP) (increment-histo node-hash 'and $3 $4)]
                   [(OP OR exp exp CP) (increment-histo node-hash 'or $3 $4)]
                   [(OP + exp exp CP) (increment-histo node-hash 'add $3 $4)]
                   [(OP - exp exp CP) (increment-histo node-hash 'sub $3 $4)]
                   [(OP * exp exp CP) (increment-histo node-hash 'mul $3 $4)]
                   [(OP DIV exp exp CP) (increment-histo node-hash 'div $3 $4)]
                   [(OP < exp exp CP) (increment-histo node-hash 'LT $3 $4)]
                   [(OP > exp exp CP) (increment-histo node-hash 'GT $3 $4)]
                   [(OP MOD exp exp CP) (increment-histo node-hash 'mod $3 $4)]
                   [(OP GE exp exp CP) (increment-histo node-hash 'GE $3 $4)]
                   [(OP LE exp exp CP) (increment-histo node-hash 'LE $3 $4)]
                   [(OP - exp CP) (prec NEG) (increment-histo node-hash 'sub $3)]
                   [(- exp) (prec NEG) (increment-histo node-hash 'sub $2)]
                   [(OP exp CP) $2]
                   [(LII exp) $2])))]
         [_ (evaluate-smt2-parser p expr-str)])
    node-hash))

(define (node-type-gt? nt1 nt2)
  (> (hash-ref node-type-ordering nt1) (hash-ref node-type-ordering nt2)))

(define (node-histo-gt? h1 h2)
  (letrec ([f (λ (node-list) (cond [(empty? node-list) #f]
                                   [(eq? (hash-ref h1 (first node-list)) (hash-ref h2 (first node-list)))
                                    (f (cdr node-list))]
                                   [else (> (hash-ref h1 (first node-list)) (hash-ref h2 (first node-list)))]))])
    (f (reverse node-type-list))))

(define (root-sym-gt? e1 e2)
  (node-type-gt? (get-smt2-root-symbol e1) (get-smt2-root-symbol e2)))

(define (smt2-expr-gt? e1 e2)
  (let ([histo1 (build-smt2-node-histo e1)]
        [histo2 (build-smt2-node-histo e2)])
    (if (eq? histo1 histo2)
        (root-sym-gt? e1 e2)
        (node-histo-gt? histo1 histo2))))

;; for a given term t1, find all node types that can occur in a term t2 if t1 > t2
(define (get-less-than-term-symbols term)
  (let ([h (build-smt2-node-histo term)])
    (memf (λ (nt) (> (hash-ref h nt) 0)) (reverse node-type-list))))