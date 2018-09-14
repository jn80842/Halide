#lang rosette

(require "lang.rkt")
(require "sketch.rkt")

(provide print-sketch print-live-regs-sketch)

(define (print-sketch sk)
  (displayln (string-join (sketch->string sk) "\n")))

(define (print-live-regs-sketch sk)
  (displayln (string-join (live-reg-sketch->string sk) "\n")))

(define (args->string-list sk)
  (append (for/list ([i (range (sketch-nc-input-count sk))]) (format "_~a" i))
          (for/list ([j (range (sketch-nc-input-count sk) (+ (sketch-nc-input-count sk) (sketch-const-input-count sk)))]) (format "c~a" j))
          (list "0")))

(define (inputs->string-list sk)
  (let ([args (args->string-list sk)])
    (for/list ([i (range (length args))])
      (format "  (define R~a ~a)" i (list-ref args i)))))

(define (insn-args->string i)
  (case (get-operator-arity-by-idx (insn-op-idx i))
    [(1) (format "R~a" (number->string (insn-arg1-idx i)))]
    [(2) (format "R~a R~a" (number->string (insn-arg1-idx i)) (number->string (insn-arg2-idx i)))]
    [(3) (format "R~a R~a R~a" (number->string (insn-arg1-idx i)) (number->string (insn-arg2-idx i)) (number->string (insn-arg3-idx i)))]))

(define (insns->string-list sk)
  (let ([input-offset (get-sketch-input-count sk)])
    (for/list ([i (range (length (sketch-insn-list sk)))])
      (let ([current-insn (list-ref (sketch-insn-list sk) i)])
        (format "  (define R~a (~a ~a))" (+ input-offset i) (get-operator-name-by-idx (insn-op-idx current-insn)) (insn-args->string current-insn))))))

(define (sketch->string sk)
  (append (list (format "(define (sketch-function ~a)" (string-join (args->string-list sk) " ")))
          (inputs->string-list sk)
          (insns->string-list sk)
          (list (format "  R~a)" (sketch-retval-idx sk)))))

(define (live-reg-sketch->string sk)
  (let ([args (args->string-list sk)]
        [live-regs (find-live-registers sk)]
        [input-count (get-sketch-input-count sk)]
        [input-strings (inputs->string-list sk)]
        [insn-strings (insns->string-list sk)])
    (append (list (format "(define (sketch-function ~a)" (string-join (take args (sub1 (length args))) " ")))
            (filter identity (map (λ (x) (if (member x live-regs)
                                             (list-ref input-strings x)
                                             #f))
                                  (range input-count)))
            (filter identity (map (λ (x) (if (member x live-regs)
                                             (list-ref insn-strings (- x input-count))
                                             #f))
                                  (range input-count (+ input-count (length (sketch-insn-list sk))))))
            (list (format "  R~a)" (sketch-retval-idx sk))))))
