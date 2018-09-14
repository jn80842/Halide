#lang rosette

(provide (all-defined-out))

(define bvw 8)

(current-bitwidth bvw)

(define (get-sym-bv)
  (define-symbolic* b (bitvector bvw))
  b)

;; Expr -> IntExpr | BoolExpr;
;; 
;; IntExpr -> IntExpr + IntExpr
;;         | IntExpr - IntExpr
;;         | IntExpr * IntExpr
;;         | IntExpr / IntExpr
;;         | IntExpr % IntExpr
;;         | max(IntExpr, IntExpr)
;;         | min(IntExpr, IntExpr)
;;         | Int;
;; 
;; BoolExpr -> ! BoolExpr
;;         | BoolExpr && BoolExpr
;;         | BoolExpr || BoolExpr
;;         | IntExpr < IntExpr
;;         | IntExpr - Intexpr == 0
;;         | BoolExpr == BoolExpr
;;         | Bool;

(define (bvand-hld b1 b2)
  (let ([btrue (bv 1 bvw)]
        [bfalse (bv 0 bvw)])
    (if (bveq b1 bfalse)
        bfalse
        (if (bveq b2 bfalse)
            bfalse
            btrue))))

(define (bvor-hld b1 b2)
  (let ([btrue (bv 1 bvw)]
        [bfalse (bv 0 bvw)])
    (if (not (bveq b1 bfalse))
        btrue
        (not (bveq b2 bfalse)))))

(define (bvsmax b1 b2)
  (if (bvsgt b1 b2) b1 b2))

(define (bvsmin b1 b2)
  (if (bvsgt b1 b2) b2 b1))

(define (hld-div b1 b2)
  (if (equal? b2 (bv 0 bvw))
      (bv 0 bvw)
      (bvsdiv b1 b2)))

(define (bvnot-hld b1 b2)
  (not b1))

(define (hld-and b1 b2)
  (if (and b1 b2) #t #f))

(define (hld-or b1 b2)
  (if (or b1 b2) #t #f))

(define (noop b1 b2)
  b1)

(define bvadd-idx (bv 0 bvw))
(define bvsub-idx (bv 1 bvw))
(define bvmul-idx (bv 2 bvw))
(define bvsdiv-idx (bv 3 bvw))
(define bvsmod-idx (bv 4 bvw))
(define bvsmax-idx (bv 5 bvw))
(define bvsmin-idx (bv 6 bvw))
(define bvand-idx (bv 7 bvw))
(define bvor-idx (bv 8 bvw))
(define bvslt-idx (bv 9 bvw))
(define bvsle-idx (bv 10 bvw))
(define bvsgt-idx (bv 11 bvw))
(define bvsge-idx (bv 12 bvw))
(define bveq-idx (bv 13 bvw))
(define bvnot-idx (bv 14 bvw))
(define noop-idx (bv 32 bvw)) ;; note that noop is any val greater than 14

(define (get-operator-function-by-idx idx)
  (if (bveq idx bvadd-idx)
      bvadd
      (if (bveq idx bvsub-idx)
          bvsub
          (if (bveq idx bvmul-idx)
              bvmul
              (if (bveq idx bvsdiv-idx)
                  hld-div
                  (if (bveq idx bvsmod-idx)
                      bvsmod
                      (if (bveq idx bvsmax-idx)
                          bvsmax
                          (if (bveq idx bvsmin-idx)
                              bvsmin
                              (if (bveq idx bvand-idx)
                                  hld-and
                                  (if (bveq idx bvor-idx)
                                      hld-or
                                      (if (bveq idx bvslt-idx)
                                          bvslt
                                          (if (bveq idx bvsle-idx)
                                              bvsle
                                              (if (bveq idx bvsgt-idx)
                                                  bvsgt
                                                  (if (bveq idx bvsge-idx)
                                                      bvsge
                                                      (if (bveq idx bveq-idx)
                                                          bveq
                                                          (if (bveq idx bvnot-idx)
                                                              not
                                                              noop))))))))))))))))

(define (is-noop? idx)
  (bvsgt idx bvnot-idx))

(define (get-operator-name-by-idx idx)
  (if (bveq idx bvadd-idx)
      "bvadd"
      (if (bveq idx bvsub-idx)
          "bvsub"
          (if (bveq idx bvmul-idx)
              "bvmul"
              (if (bveq idx bvsdiv-idx)
                  "hld-div"
                  (if (bveq idx bvsmod-idx)
                      "bvsmod"
                      (if (bveq idx bvsmax-idx)
                          "bvsmax"
                          (if (bveq idx bvsmin-idx)
                              "bvsmin"
                              (if (bveq idx bvand-idx)
                                  "hld-and"
                                  (if (bveq idx bvor-idx)
                                      "hld-or"
                                      (if (bveq idx bvslt-idx)
                                          "bvslt"
                                          (if (bveq idx bvsle-idx)
                                              "bvsle"
                                              (if (bveq idx bvsgt-idx)
                                                  "bvsgt"
                                                  (if (bveq idx bvsge-idx)
                                                      "bvsge"
                                                      (if (bveq idx bveq-idx)
                                                          "bveq"
                                                          (if (bveq idx bvnot-idx)
                                                              "bvnot-hld"
                                                              "noop"))))))))))))))))

(define get-op get-operator-function-by-idx)

(define (single-arg-function? idx)
  (or (is-noop? idx)
      (bveq idx bvnot-idx)))

(define (count-variables1 idx)
  (if (single-arg-function? idx) 1 2))

(define (count-variables2 op0 op1 op2)
  (if (single-arg-function? op0)
      (count-variables1 op1)
      (+ (count-variables1 op1) (count-variables1 op2))))
  
(define (count-variables3 fsk)
  (if (single-arg-function? (fixedsk3-op0 fsk))
      (count-variables2 (fixedsk3-op1 fsk) (fixedsk3-op3 fsk) (fixedsk3-op4 fsk))
      (+ (count-variables2 (fixedsk3-op1 fsk) (fixedsk3-op3 fsk) (fixedsk3-op4 fsk))
         (count-variables2 (fixedsk3-op2 fsk) (fixedsk3-op5 fsk) (fixedsk3-op6 fsk)))))

(define (count-variables2a fsk)
  (+ (if (single-arg-function? (fixedsk2-op1 fsk)) 1 2)
     (if (single-arg-function? (fixedsk2-op0 fsk)) 0 (if (single-arg-function? (fixedsk2-op2 fsk)) 1 2))))

(define (count-variables3a fsk)
  (+ (+ (if (single-arg-function? (fixedsk3-op3 fsk)) 1 2) (if (single-arg-function? (fixedsk3-op1 fsk)) 0 (if (single-arg-function? (fixedsk3-op4 fsk)) 1 2)))
     (if (single-arg-function? (fixedsk3-op0 fsk)) 0
         (+ (if (single-arg-function? (fixedsk3-op5 fsk)) 1 2) (if (single-arg-function? (fixedsk3-op2 fsk)) 0 (if (single-arg-function? (fixedsk3-op6 fsk)) 1 2))))))

(define (get-fixed-input2 idx i0 i1 i2 i3)
  (if (bveq idx (bv 0 bvw))
      i0
      (if (bveq idx (bv 1 bvw))
          i1
          (if (bveq idx (bv 2 bvw))
              i2 i3))))

(define (get-fixed-input-names2 idx)
  (let ([inputs (for/list ([i (range (expt 2 2))]) (string-append "b" (number->string i)))])
    (if (term? idx)
        "null"
        (if (bveq idx (bv 0 bvw))
            (list-ref inputs 0)
            (if (bveq idx (bv 1 bvw))
                (list-ref inputs 1)
                (if (bveq idx (bv 2 bvw))
                    (list-ref inputs 2)
                    (list-ref inputs 3)))))))

(define (get-fixed-input3 idx inputs)
  (if (bveq idx (bv 0 bvw))
      (list-ref inputs 0)
      (if (bveq idx (bv 1 bvw))
          (list-ref inputs 1)
          (if (bveq idx (bv 2 bvw))
              (list-ref inputs 2)
              (if (bveq idx (bv 3 bvw))
                  (list-ref inputs 3)
                  (if (bveq idx (bv 4 bvw))
                      (list-ref inputs 4)
                      (if (bveq idx (bv 5 bvw))
                          (list-ref inputs 5)
                          (if (bveq idx (bv 6 bvw))
                              (list-ref inputs 6)
                              (list-ref inputs 7)))))))))

(define (get-fixed-input-names3 idx)
  (let ([inputs (for/list ([i (range (expt 2 3))]) (string-append "b" (number->string i)))])
    (if (term? idx)
        "null"
        (if (bveq idx (bv 0 bvw))
            (list-ref inputs 0)
            (if (bveq idx (bv 1 bvw))
                (list-ref inputs 1)
                (if (bveq idx (bv 2 bvw))
                    (list-ref inputs 2)
                    (if (bveq idx (bv 3 bvw))
                        (list-ref inputs 3)
                        (if (bveq idx (bv 4 bvw))
                            (list-ref inputs 4)
                            (if (bveq idx (bv 5 bvw))
                                (list-ref inputs 5)
                                (if (bveq idx (bv 6 bvw))
                                    (list-ref inputs 6)
                                    (list-ref inputs 7)))))))))))

(struct fixedsk2 (op0 op1 op2 idx0 idx1 idx2 idx3) #:transparent)

(struct fixedsk3 (op0 op1 op2 op3 op4 op5 op6 idx0 idx1 idx2 idx3 idx4 idx5 idx6 idx7) #:transparent)

(define (get-fixed-symbolic-sketch2)
  (let ([ops (for/list ([i (range (sub1 (expt 2 2)))]) (get-sym-bv))]
        [indexes (for/list ([i (range (expt 2 2))]) (get-sym-bv))])
    (apply fixedsk2 (append ops indexes))))

(define (get-fixed-symbolic-sketch3)
  (let ([ops (for/list ([i (range (sub1 (expt 2 3)))]) (get-sym-bv))]
        [indexes (for/list ([i (range (expt 2 3))]) (get-sym-bv))])
    (apply fixedsk3 (append ops indexes))))

(define (get-sketch-function2 fsk)
  (λ (i0 i1 i2 i3)
    ((get-op (fixedsk2-op0 fsk)) ((get-op (fixedsk2-op1 fsk)) (get-fixed-input2 (fixedsk2-idx0 fsk) i0 i1 i2 i3)
                                                              (get-fixed-input2 (fixedsk2-idx1 fsk) i0 i1 i2 i3))
                                 ((get-op (fixedsk2-op2 fsk)) (get-fixed-input2 (fixedsk2-idx2 fsk) i0 i1 i2 i3)
                                                              (get-fixed-input2 (fixedsk2-idx3 fsk) i0 i1 i2 i3)))))
(define (get-sketch-function3 fsk)
  (λ (i0 i1 i2 i3 i4 i5 i6 i7)
    (let ([inputs (list i0 i1 i2 i3 i4 i5 i6 i7)])
      ((get-op (fixedsk3-op0 fsk)) ((get-op (fixedsk3-op1 fsk)) ((get-op (fixedsk3-op3 fsk)) (get-fixed-input3 (fixedsk3-idx0 fsk) inputs)
                                                                                             (get-fixed-input3 (fixedsk3-idx1 fsk) inputs))
                                                                ((get-op (fixedsk3-op4 fsk)) (get-fixed-input3 (fixedsk3-idx2 fsk) inputs)
                                                                                             (get-fixed-input3 (fixedsk3-idx3 fsk) inputs)))
                                   ((get-op (fixedsk3-op2 fsk)) ((get-op (fixedsk3-op5 fsk)) (get-fixed-input3 (fixedsk3-idx4 fsk) inputs)
                                                                                             (get-fixed-input3 (fixedsk3-idx5 fsk) inputs))
                                                                ((get-op (fixedsk3-op6 fsk)) (get-fixed-input3 (fixedsk3-idx6 fsk) inputs)
                                                                                             (get-fixed-input3 (fixedsk3-idx7 fsk) inputs)))))))

(define (get-string-sketch-function2 fsk)
  (string-append "(define (synthesized-function "
                 (string-join (for/list ([i (range (expt 2 2))]) (string-append "b" (number->string i))) " ")
                 ")\n"
                 "  (" (get-operator-name-by-idx (fixedsk2-op0 fsk)) " "
                 "(" (get-operator-name-by-idx (fixedsk2-op1 fsk)) " "
                 (get-fixed-input-names2 (fixedsk2-idx0 fsk)) " "
                 (get-fixed-input-names2 (fixedsk2-idx1 fsk)) ") "
                 "(" (get-operator-name-by-idx (fixedsk2-op2 fsk)) " "
                 (get-fixed-input-names2 (fixedsk2-idx2 fsk)) " "
                 (get-fixed-input-names2 (fixedsk2-idx3 fsk)) ")))")) 
                 
(define (get-string-sketch-function3 fsk)
    (string-append "(define (synthesized-function "
                   (string-join (for/list ([i (range (expt 2 3))]) (string-append "b" (number->string i))) " ")
                   ")\n"
                   "  (" (get-operator-name-by-idx (fixedsk3-op0 fsk)) " "
                   "(" (get-operator-name-by-idx (fixedsk3-op1 fsk)) " "
                   "(" (get-operator-name-by-idx (fixedsk3-op3 fsk)) " "
                   (get-fixed-input-names3 (fixedsk3-idx0 fsk)) " "
                   (get-fixed-input-names3 (fixedsk3-idx1 fsk)) ") "
                   "(" (get-operator-name-by-idx (fixedsk3-op4 fsk)) " "
                   (get-fixed-input-names3 (fixedsk3-idx2 fsk)) " "
                   (get-fixed-input-names3 (fixedsk3-idx3 fsk)) ")) "
                   "(" (get-operator-name-by-idx (fixedsk3-op2 fsk)) " "
                   "(" (get-operator-name-by-idx (fixedsk3-op5 fsk)) " "
                   (get-fixed-input-names3 (fixedsk3-idx4 fsk)) " "
                   (get-fixed-input-names3 (fixedsk3-idx5 fsk)) ") "
                   "(" (get-operator-name-by-idx (fixedsk3-op6 fsk)) " "
                   (get-fixed-input-names3 (fixedsk3-idx6 fsk)) " "
                   (get-fixed-input-names3 (fixedsk3-idx7 fsk)) "))))"))

#;(define (synthesize-predicate expr sk nc-inputs const-inputs)
  (let* ([sym-consts (append (map (λ (i) (get-sym-bv)) (list-tail const-inputs 1)) (list (bv 0 bvw)))]
         [evaled-sketch (apply (get-sketch-function sk) sym-consts)]
         [evaled-const-sketch (apply (get-sketch-function sk) const-inputs)]
         [evaled-expr (apply expr (append nc-inputs sym-consts))]
         [binding (time (synthesize #:forall (append nc-inputs sym-consts)
                                    #:guarantee (assert (and (or (not evaled-sketch) evaled-expr)
                                                             evaled-const-sketch))))])
    (if (unsat? binding)
        (displayln "no solution")
        (displayln binding))))

(define (synthesize-rewrite2 expr sk sym-inputs expr-var-count)
  (begin
    (define binding (time (synthesize #:forall (symbolics sym-inputs)
                                      #:guarantee (assert (and (equal? (apply (get-sketch-function2 sk) sym-inputs)
                                                                       (apply expr sym-inputs))
                                                               (< (count-variables2a sk) expr-var-count))))))
    (if (unsat? binding)
        (displayln "could not find expression")
        (displayln (get-string-sketch-function2 (evaluate sk binding))))))

(define (synthesize-rewrite3 expr sk sym-inputs expr-var-count)
  (let ([evaled-rhs (apply (get-sketch-function3 sk) sym-inputs)]
        [evaled-lhs (apply expr sym-inputs)]
        [sketch-var-count (count-variables3a sk)])
    (begin
      (define binding (time (synthesize #:forall (symbolics sym-inputs)
                                        #:guarantee (assert (and (equal? evaled-rhs evaled-lhs)
                                                                 (> expr-var-count sketch-var-count))))))
      (if (unsat? binding)
          (displayln "could not find expression")
          (displayln (get-string-sketch-function3 (evaluate sk binding)))))))

(define (testcase x y z w p q r s)
  (bvsle (bvsdiv (bvsub q p) r) (bvsdiv (bvsub s p) r)))

(define (testcase-c-expr x y z a b c d)
  (bvsle (bvadd (bvmul (bvadd (bvsmin z a) (bvadd (bvmul x b) y)) c) (bvsub (bv 0 7) d))
      (bvmul (bvadd (bvmul x b) y) c)))

(define-symbolic* bx (bitvector bvw))
(define-symbolic* by (bitvector bvw))
(define-symbolic* bz (bitvector bvw))
(define-symbolic* bw (bitvector bvw))
(define zero (bv 0 bvw))
(define one (bv 1 bvw))
(define two (bv 2 bvw))