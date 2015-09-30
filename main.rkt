;; Extended MUPL Interpreter

#lang racket

(require "ast-struct.rkt")
(require "evaluator.rkt")
(require "type-inferencer.rkt")
(provide (all-defined-out))


(define (type-of e)
  (type-of-under-env-subst e (list (make-hash)) (make-hash)))

;; evaluate the expression e under the top env and the top continuation
(define (eval-exp e)
  (eval-under-env-cont e (list (make-hash)) (λ (val) val)))


;;----------------------------------- Syntatic Sugar ----------------------------------------

;; act like list in Racket
(define (alist . args)
  (foldr apair (aunit) args))

;; e1 = (aunit), e2; otherwise e3
(define-syntax ifaunit
  (syntax-rules ()
    [(ifaunit e1 e2 e3)
     (if-then-else (isaunit e1)
                   e2 e3)]))

;; (fun fn-name (var0 ...) body)
(define-syntax fun
  (syntax-rules ()
    [(fun fn-name () body)
     (_fun fn-name (list (aunit)) body)]
    [(fun fn-name (var0 var-rest ...) body)
     (_fun fn-name (list var0 var-rest ...) body)]))

;; (call fn val0 val1 ...)
(define-syntax call
  (syntax-rules ()
    [(call fn)
     (_call fn (list (aunit)))]
    [(call fn val0 val-rest ...)
     (_call fn (list val0 val-rest ...))]))


;; sequentially execute, equivalent to 'begin' in racket
(define-syntax seq
  (syntax-rules ()
    [(seq e0)
     (_seq e0 (aunit))]
    [(seq e0 e-rest ...)
     (_seq e0 (seq e-rest ...))]))


;; a local binding (mlet ([var0 val0] ...) body), vark is a Racket string
;; named-mlet: (mlet fn-name ([var0 val0] ...) body)
(define-syntax mlet
  (syntax-rules ()
    [(mlet () body)
     body]
    [(mlet fn-name ([var0 val0] [var-rest val-rest] ...) body) ;; named-mlet
     (call (fun fn-name (var0 var-rest ...) body) val0 val-rest ...)]
    [(mlet ([var0 val0] [var-rest val-rest] ...) body)
     (call (fun #f (var0 var-rest ...) body) val0 val-rest ...)]))

;; (mlet* ([var0 val0] ...) body) = (mlet var0 val1 (mlet ...))
(define-syntax mlet*
  (syntax-rules ()
    [(mlet* () body)
     body]
    [(mlet* ([var0 val0]
             [var-rest val-rest] ...)
            body)
     (mlet ([var0 val0])
           (mlet* ([var-rest val-rest] ...)
                  body))]))

;; (mletrec ([var0 val0] ...) body) = (let ([var0 (aunit] ...)
;;                                       (let ([var0.__tmp__ val0] ...)
;;                                          (seq (_modify-env var0)
;;                                               (_modify-env var-rest) ...
;;                                               body)))
;; (_modify-env body) will modify the bindings of var0, var1, ... before calling the body
(define-syntax mletrec
  (syntax-rules ()
    [(mletrec () body)
     body]
    [(mletrec ([var0 val0] [var-rest val-rest]  ...)
              body)
     (_letrec (list var0 var-rest ...) (list val0 val-rest ...) body)]))

;; ---- mutable ------

(define-syntax ampair
  (syntax-rules ()
    [(ampair e1 e2)
     (apair (newref! e1) (newref! e2))]))

(define-syntax amlist
  (syntax-rules ()
    [(amlist)
     (newref! (aunit))]
    [(amlist e1 e-rest ...)
     (apair (newref! e1) (newref! (amlist e-rest ...)))]))

(define-syntax mfst
  (syntax-rules ()
    [(mfst mpair-e)
     (deref (fst mpair-e))]))

(define-syntax msnd
  (syntax-rules ()
    [(msnd mpair-e)
     (deref (snd mpair-e))]))

(define-syntax set-mfst!
  (syntax-rules ()
    [(set-mfst! mpair-e v)
     (setref! (fst mpair-e) v)]))

(define-syntax set-msnd!
  (syntax-rules ()
    [(set-msnd! mpair-e v)
     (setref! (snd mpair-e) v)]))
