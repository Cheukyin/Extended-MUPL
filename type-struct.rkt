#lang racket
(provide (all-defined-out))

(struct int-type () #:transparent)
(struct bool-type () #:transparent)
(struct ref-type (t) #:transparent)
(struct -> (arg-type result-type) #:transparent) ;; function type
(struct type-var (num) #:transparent) ;; type variable
(struct pair-type (t1 t2) #:transparent)
(struct unit-type () #:transparent) ;; type of (aunit)

(struct type-scheme (param-list type-exp) #:transparent) ;; param-list is a list of type-var

(define fresh-type-var
  (let ([num 0])
    (λ ()
      (set! num (+ num 1))
      (type-var num))))
