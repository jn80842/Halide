#lang racket

(require "../halide-dsl/halide-to-smt2.rkt")
(require "../halide-dsl/halide-helpers.rkt")
(require "../halide-dsl/rename-constants.rkt")
(require "../halide-dsl/subterms.rkt")
(require "../smt2/smt2-helpers.rkt")
(require "../smt2/smt2-to-halide.rkt")
(require "callz3.rkt")

;(define e "(min(((((v4 + 11)/4)*4) + (((((((v4 + 3)/4)*4) + 10)/34)*34) + ((v1*125) + v2))), (((((v4 + 3)/4)*4) + ((v1*125) + v2)) + 7)) <= (min((((v4 + 11)/4)*4), ((((v4 + 3)/4)*4) + 7)) + ((v1*125) + v2)))")
(define e "((((((((((v1 - v2) + 7)/4)*4) + v2) - v1) + 3)/4) - (((v2 - v1)/4) + (((v1 - v2) + 7)/4))) <= 1)")

(define (check-expr-true-without-constants e)
  (let ([smt2-e (halide->smt2 (get-halide-renamed-constants-expr e))])
    (call-z3 (get-verify-true-formula (get-smt2-variables smt2-e) '() smt2-e))))

(define (get-constants-mapping e)
  (let ([constants (set->list (get-halide-constants e))]
        [mapping (make-hash)])
    (for ([i (range (length constants))])
      (hash-set! mapping (list-ref constants i) (format "c~a" i)))
    mapping))

(define (replaced-unneeded-constants e)
  (let* ([replaceable-vars (make-hash)]
         [constants-mapping (get-constants-mapping e)]
         [smt2-e (halide->smt2 e)]
         [smt2-variables (get-smt2-variables smt2-e)])
    (for ([c (hash-keys constants-mapping)])
      (let ([const-var (hash-ref constants-mapping c)])
        (unless (not (call-z3 (get-verify-true-formula (append (list const-var) smt2-variables) '()
                                                       (get-smt2-replaced-consts-expr smt2-e (make-hash (list (cons c const-var)))))))
          (hash-set! replaceable-vars c const-var))))
    (smt2->halide (get-smt2-replaced-consts-expr smt2-e replaceable-vars))))

#;(call-with-input-file "/Users/mpu/research/termrewriting/resimplify/xac_final.txt"
  (λ (in)
    (for ([line (in-lines in)])
      (if (check-expr-true-without-constants line)
          (begin
            (call-with-output-file "xac_alltrue2.txt"
              (λ (out) (displayln (get-halide-renamed-constants-expr line) out)) #:exists 'append)
            (println "all true"))
          (begin
            (call-with-output-file "xac_replaced2.txt"
              (λ (out) (displayln (replaced-unneeded-constants line) out)) #:exists 'append)
            (println "replaced consts"))
      ))))

#;(call-with-input-file "/Users/mpu/research/termrewriting/resimplify/replaced.txt"
  (λ (in)
    (for ([line (in-lines in)])
      (call-with-output-file "replaced_const_counts.txt"
        (λ (out) (displayln (format "~a ~a" (set-count (get-halide-constants line)) line) out)) #:exists 'append))))

(define predicates_c1 (list "(<= ~a 0)" "(>= ~a 0)" "(< ~a 0)" "(> ~a 0)" "(not (= ~a 0))" "(= ~a 0)"))

(define (find-predicate e)
  (let* ([renamed-vars-e (rename-vars-parse e)]
         [const-mapping (get-constants-mapping e)]
         [smt2-e (get-smt2-replaced-consts-expr (halide->smt2 renamed-vars-e) const-mapping)])
    (for ([p predicates_c1])
      (let ([pred-string (apply format p (hash-values const-mapping))])
        (if (call-z3 (get-verify-true-formula-with-predicate (get-smt2-variables smt2-e) '()
                                                                      smt2-e (apply format p (hash-values const-mapping))))
          (println pred-string)
          (void))))))
        