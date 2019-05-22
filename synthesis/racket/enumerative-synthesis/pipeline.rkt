#lang racket

;(require "enumerate.rkt")
;(require "comparison.rkt")
;(require "callz3.rkt")

(require "../halide-dsl/halide-to-smt2.rkt")

;; start with expression that simplifier cannot reduce

(define e "(((min(((((((v4 + 3)/4)*4) + -1)/63)*63), -2) + ((v1*125) + v2)) + 2) <= ((v1*125) + v2))")

;; parse halide expression into SMT2

(define smt2-e (halide->smt2 e))

;; replace all constants with fresh variables

;(define const-e (const-to-fresh-vars e))

;; verify that expression is still true

;(if (call-z3 (get-verify-true-formula 




;; get all subterms/substitutions from source expr

;; filter out candidate LHSs below a certain size

;; for each candidate LHS, find all variables (assume that all vars are of type integer)

#;(define (get-string-variables s)
  (map symbol->string (set->list (get-variables s))))

;(define e1-vars (map symbol->string (set->list (get-variables e1))))

;; enumerate all expressions up to a given size
;; for those expressions, filter if they are not less than LHS in ordering

;(define smt2-e1 (get-smt2-formula e1))



;(define inr1 (int-next-round e1-vars '()))
;(define bnr1 (bool-next-round e1-vars '()))

;(define inr2 (int-next-round (append e1-vars (filter-by-gt smt2-e1 inr1)) (filter-by-gt smt2-e1 bnr1)))
;(define bnr2 (bool-next-round (append e1-vars (filter-by-gt smt2-e1 inr1)) (filter-by-gt smt2-e1 bnr1)))

;; if LHS > RHS, query z3 for equivalence







#;(time (for ([rhs (filter-by-gt smt2-e1 bnr2)])
        (unless (not (verify-exprs-are-equal e1-vars '() smt2-e1 rhs))
          (println (format "Candidate rule: ~a ---> ~a" smt2-e1 rhs)))))

;(define smt2-candidate-lhs (filter (λ (t) (string-contains? t "(")) (map get-smt2-formula (get-all-substs-and-subterms e1))))

;(define type-classified-candidates (make-hash (map (λ (xs) (cons (get-type-smt2 (first xs)) xs)) (group-by get-type-smt2 smt2-candidate-lhs))))

#;(for ([t (hash-ref type-classified-candidates 'boolean)])
  (if (call-z3 (z3-verify-true e1-vars '() t))
      (println (format "~a ---> true" t))
      (if (call-z3 (z3-verify-false e1-vars '() t))
          (println (format "~a ----> false" t))
          (println (format "~a ----> neither true nor false" t)))))

#;(hash-set! type-classified-candidates 'boolean (filter (λ (t) (not (or (call-z3 (z3-verify-true e1-vars '() t)) (call-z3 (z3-verify-false e1-vars '() t)))))
        (hash-ref type-classified-candidates 'boolean)))

#;(call-with-input-file "/Users/mpu/research/termrewriting/pipeline_verified_exprs.txt"
  (λ (f)
    (for/fold ([counter 0])
              ([line (in-lines f)])
      (begin
        (if (call-z3 (z3-verify-true (map symbol->string (set->list (get-variables (masked-constants line)))) '()
                                 (get-smt2-formula (masked-constants line))))
            (println (format "TRUE: ~a" line))
            (println (format "FALSE: ~a" line)))))))

;;; an expression verified true when constants are replaced with fresh vars
;(define s "(((min(((((((v4 + 3)/4)*4) + -1)/63)*63), -2) + ((v1*125) + v2)) + 2) <= ((v1*125) + v2))")
;(define s-vars (get-string-variables (masked-constants s)))

(define (get-smt2-vars s)
  (set->list (list->set (regexp-match* #rx"v[0-9]+" s))))

(define (get-typed-smt2-terms s)
  (make-hash (map (λ (xs) (cons (get-type-smt2 (first xs)) xs))
                  (group-by get-type-smt2 (map get-smt2-formula (get-all-substs-and-subterms (masked-constants s)))))))

(define s-terms (get-typed-smt2-terms s))

(define (find-true-exprs terms)
  (sort (filter (λ (t) (call-z3 (z3-verify-true (get-smt2-vars t) '() t))) terms) (λ (x y) (< (string-length x) (string-length y)))))
(define (find-false-exprs terms)
  (sort (filter (λ (t) (call-z3 (z3-verify-false (get-smt2-vars t) '() t))) terms) (λ (x y) (< (string-length x) (string-length y)))))

(define s-terms-true (find-true-exprs (hash-ref s-terms 'boolean)))
(define s-terms-false (find-false-exprs (hash-ref s-terms 'boolean)))

(hash-set! s-terms 'boolean (filter (λ (t) (and (not (member t s-terms-true)) (not (member t s-terms-false)))) (hash-ref s-terms 'boolean)))

(define (find-single-var-equiv-exprs terms)
  (for/list ([t terms])
    (cons t (filter (λ (v) (verify-exprs-are-equal (get-smt2-vars t) '() t v)) (get-smt2-vars t)))))

(define (get-terms-by-depth terms)
  (make-hash (map (λ (xs) (cons (get-smt2-node-depth (first xs)) xs)) (group-by get-smt2-node-depth terms))))

(define (find-int-depth1-equiv-exprs term)
  (let* ([vars (get-smt2-vars term)]
         [exprs ((get-int-expr-function term) vars '())])
    (filter (λ (e) (verify-exprs-are-equal vars '() term e)) exprs)))

(define (check-terms-int-depth1 int-terms)
  (for ([t int-terms])
    (let* ([t-vars (get-smt2-vars t)]
           [inr1-terms ((get-int-expr-function t) t-vars '())])
      (println t)
      (println (format "Checked against ~a terms" (length inr1-terms)))
      (println (filter (λ (e) (verify-exprs-are-equal t-vars '() t e)) inr1-terms)))))

(define (check-terms-bool-depth1 bool-terms)
  (for ([t bool-terms])
    (let* ([t-vars (get-smt2-vars t)]
           [bnr1-terms ((get-bool-expr-function t) t-vars '())])
      (println t)
      (println (format "Checked against ~a terms" (length bnr1-terms)))
      (println (filter (λ (e) (verify-exprs-are-equal t-vars '() t e)) bnr1-terms)))))
      
(define (find-int-depth2-equiv-exprs term)
  (let* ([vars (get-smt2-vars term)]
         [inr1-exprs (filter-by-gt term (int-next-round vars '()))]
         [bnr1-exprs (filter-by-gt term (bool-next-round vars '()))]
         [inr2-exprs (filter-by-gt term (int-next-round (append vars inr1-exprs) bnr1-exprs))])
    (println (format "INR1: ~a" (length inr1-exprs)))
    (println (format "BNR1: ~a" (length bnr1-exprs)))
    (println (format "INR2: ~a" (length inr2-exprs)))
    (filter (λ (e) (verify-exprs-are-equal vars '() term e) inr2-exprs))))

(define (find-bool-depth2-equiv-exprs term)
  (let* ([vars (append '(0 1) (get-smt2-vars term))]
         [inr1-exprs (filter-by-gt term (int-next-round vars '()))]
         [bnr1-exprs (filter-by-gt term (bool-next-round vars '()))]
         [bnr2-exprs (filter-by-gt term (bool-next-round (append vars inr1-exprs) bnr1-exprs))])
    (println (format "INR1: ~a" (length inr1-exprs)))
    (println (format "BNR1: ~a" (length bnr1-exprs)))
    (println (format "BNR2: ~a" (length bnr2-exprs)))
    (filter (λ (e) (verify-exprs-are-equal vars '() term e)) bnr2-exprs)))