#lang racket

(require "../halide-dsl/halide-to-smt2.rkt")
(require "../halide-dsl/rename-constants.rkt")
(require "../halide-dsl/subterms.rkt")
(require "../halide-dsl/halide-helpers.rkt")
(require "../smt2/smt2-to-halide.rkt")
(require "../smt2/smt2-helpers.rkt")
(require "../smt2/smt2-gt.rkt")
(require "callz3.rkt")
(require "enumerate.rkt")

;; start with expression that simplifier cannot reduce

(define e "(((min(((((((v4 + 3)/4)*4) + -1)/63)*63), -2) + ((v1*125) + v2)) + 2) <= ((v1*125) + v2))")

;; replace all constants with fresh variables

(define newconsts-e (get-halide-renamed-constants-expr e))

;; parse halide expression into SMT2

(define smt2-e (halide->smt2 newconsts-e))

;; verify that expression is true when constants are renamed

(if (call-z3 (get-verify-true-formula (get-smt2-variables smt2-e) '() smt2-e))
    (println "Expression with renamed constants is true")
    (println "Expression with renamed constants is not always true"))

;; get all subterms/substitutions from source expr

(define all-candidate-LHSs (get-all-substs-and-subterms newconsts-e))

;; filter out all candidate LHSs that have more than 6 unique variables

(define lessthan6v-candidate-LHSs (filter (λ (e) (< (set-count (get-halide-variables e)) 7)) all-candidate-LHSs))

;; remove all candidate LHSs that are a single variable
;; because of variable renaming, the only such term will be v0

(define candidate-LHSs (remove "v0" lessthan6v-candidate-LHSs))

;; translate candidate LHSs into SMT2 and type them

(define typed-smt2-LHSs (hash-smt2-terms-by-type (map halide->smt2 candidate-LHSs)))

;; find all boolean LHSs that are equivalent to true
(define true-LHSs (time (filter (λ (e) (call-z3 (get-verify-true-formula (get-smt2-variables e) '() e)))
                          (hash-ref typed-smt2-LHSs 'boolean))))

(println "Candidate LHSs equivalent to true:")
(for ([t (sort-smt2-by-node-count true-LHSs)])
  (println (smt2->halide t)))
(println "")

;; find all boolean LHSs that are equivalent to false
(define false-LHSs (time (filter (λ (e) (call-z3 (get-verify-false-formula (get-smt2-variables e) '() e)))
                           (remove* true-LHSs (hash-ref typed-smt2-LHSs 'boolean)))))

(println "Candidate LHSs equivalent to false:")
(for ([t false-LHSs])
  (println (smt2->halide t)))
(println "")

;; find equivalent expressions of depth 1

(define (find-rules-bool-depth1 bool-terms)
  (make-hash (for/list ([t bool-terms])
               (let* ([t-vars (get-smt2-variables t)]
                      [bnr1-terms (filter (λ (e) (smt2-expr-gt? t e)) ((get-bool-expr-function t) (append (list "0" "1" "2") t-vars) '()))]
                      [RHSs (filter (λ (e) (call-z3 (get-verify-equiv-formula t-vars '() t e))) bnr1-terms)])
                 (println t)
                 (println (format "Checked against ~a terms" (length bnr1-terms)))
                 (if (not (empty? RHSs))
                     (println (format "Found ~a equivalent terms" (length RHSs)))
                     (println "Found no equivalent terms"))
                 (cons t RHSs)))))

(define (find-rules-int-depth1 int-terms)
  (make-hash (for/list ([t int-terms])
               (let* ([t-vars (get-smt2-variables t)]
                      [inr1-terms (filter (λ (e) (smt2-expr-gt? t e)) ((get-int-expr-function t) (append (list "0" "1" "2") t-vars) '()))]
                      [RHSs (filter (λ (e) (call-z3 (get-verify-equiv-formula t-vars '() t e))) inr1-terms)])
                 (println t)
                 (println (format "Checked against ~a terms" (length inr1-terms)))
                 (if (not (empty? RHSs))
                     (println (format "Found ~a equivalent terms" (length RHSs)))
                     (println "Found no equivalent terms"))
                 (cons t RHSs)))))

(define (find-rules-bool-depth2 bool-terms)
  (make-hash (for/list ([t bool-terms])
               (let* ([ground-int-terms (append (list "0" "1" "2") (get-smt2-variables t))]
                      [bnr1-terms (filter (λ (e) (smt2-expr-gt? t e)) ((get-bool-expr-function t) ground-int-terms '()))]
                      [inr1-terms (filter (λ (e) (smt2-expr-gt? t e)) ((get-int-expr-function t) ground-int-terms '()))]
                      [bnr2-terms (filter (λ (e) (smt2-expr-gt? t e)) ((get-bool-expr-function t) (append ground-int-terms inr1-terms)
                                                                                                  (append (list "true" "false") bnr1-terms)))]
                      [RHSs (filter (λ (e) (call-z3 (get-verify-equiv-formula ground-int-terms '() t e))) bnr2-terms)])
                 (println t)
                 (println (format "Checked against ~a terms" (length bnr2-terms)))
                 (if (not (empty? RHSs))
                     (println (format "Found ~a equivalent terms" (length RHSs)))
                     (println "Found no equivalent terms"))
                 (cons t RHSs)))))

(define (find-rules-int-depth2 int-terms)
  (make-hash (for/list ([t int-terms])
               (let* ([ground-int-terms (append (list "0" "1" "2") (get-smt2-variables t))]
                      [bnr1-terms (filter (λ (e) (smt2-expr-gt? t e)) ((get-bool-expr-function t) ground-int-terms '()))]
                      [inr1-terms (filter (λ (e) (smt2-expr-gt? t e)) ((get-int-expr-function t) ground-int-terms '()))]
                      [inr2-terms (filter (λ (e) (smt2-expr-gt? t e)) ((get-int-expr-function t) (append ground-int-terms inr1-terms)
                                                                                                  (append (list "true" "false") bnr1-terms)))]
                      [RHSs (filter (λ (e) (call-z3 (get-verify-equiv-formula ground-int-terms '() t e))) inr2-terms)])
                 (println t)
                 (println (format "Checked against ~a terms" (length inr2-terms)))
                 (if (not (empty? RHSs))
                     (println (format "Found ~a equivalent terms" (length RHSs)))
                     (println "Found no equivalent terms"))
                 (cons t RHSs)))))