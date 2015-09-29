#lang racket
(require "ast-struct.rkt")
(require "type-struct.rkt")
(provide type-of-under-env-subst)

;; env is a list of hash-table,
;; subst for substition, is a hash-table( key is type-var, value is its concrete type)
;; Caveat: this proc has side effect on subst
(define (type-of-under-env-subst exp env subst)
  (match exp
    [(int val)
     (int-type)]
    
    [(bool val)
     (bool-type)]
    
    [(var v)
     (envlookup env v)]))


(define (envlookup env var)
  (if (null? env)
      (error "unbound varible while type checking" var)
      (hash-ref env var
                (λ () (envlookup (cdr env) var)))))


;; insert typed-lhs = type-rhs into subst return 'ok
;; if no inconsistency or violation occurs
;; otherwise, printx the error and the exp that cause the error
;;            then return the error equation (t-lhs . t-rhs)
(define (unifier type-lhs type-rhs subst exp)
  (define (_unifier type-lhs type-rhs kont)
    (let ([t-lhs (apply-subst-to-type type-lhs subst)]
          [t-rhs (apply-subst-to-type type-rhs subst)])
      (cond
        [(equal? t-lhs t-rhs) 'ok] ;; t-lhs == t-rhs
        
        [(type-var? t-lhs) ;; t-lhs is a type var
         (if (tvar-occur-in-type? t-lhs t-rhs)
             (kont (report-type-error "occurrence-violation:" exp t-lhs t-rhs))
             (begin (extend-subst t-lhs t-rhs subst)
                    'ok))]
        
        [(type-var? t-rhs) ;; t-rhs is a type var
         (if (tvar-occur-in-type? t-rhs t-lhs)
             (kont (report-type-error "occurrence-violation:" exp t-rhs t-lhs))
             (begin (extend-subst t-rhs t-lhs subst)
                    'ok))]
        
        [(and (->? t-lhs) (->? t-rhs)) ;; proc type
         (_unifier (->-arg-type t-lhs) (->-arg-type t-rhs) kont)
         (_unifier (->-result-type t-lhs) (->-result-type t-rhs) kont)
         'ok]
        
        [(and (pair-type? t-lhs) (pair-type? t-rhs)) ;; pair type
         (_unifier (pair-type-t1 t-lhs) (pair-type-t1 t-rhs) kont)
         (_unifier (pair-type-t2 t-lhs) (pair-type-t2 t-rhs) kont)
         'ok]
        
        [else
         (kont (report-type-error "type-inconsistency:" exp t-lhs t-rhs))])))
  
  (call/cc 
   (λ (kont)
     (_unifier type-lhs type-rhs kont))))


;; check if tvar occurs in type
(define (tvar-occur-in-type? tvar type)
  (match type
    [(int-type) #f]
    [(bool-type) #f]
    [(ref-type t) (tvar-occur-in-type? tvar t)]
    [(pair-type t1 t2) (and (tvar-occur-in-type? tvar t1)
                            (tvar-occur-in-type? tvar t2))]
    [(-> arg-type result-type)
     (or (tvar-occur-in-type? tvar arg-type)
         (tvar-occur-in-type? tvar result-type))]
    [(type-var num) (equal? type tvar)]))


(define (report-type-error prefix-str exp t1 t2)
  (print prefix-str)
  (newline)
  (print "in the exp: ") (newline) (print exp)
  (newline)
  (print "inferenced result: ") (newline)
  (print t1) (print " = ") (print t2)
  (newline) (newline)
  (cons t1 t2))
  

;; insert new-tvar = new-type into subst
;; update the original subst
(define (extend-subst new-tvar new-type subst)
  (hash-for-each subst
                 (λ (tvar type)
                   (hash-set! subst ;; update the original subst with new-type-var
                              tvar 
                              (apply-one-subst type new-tvar new-type))))
  ;; insert new-type-var = new-type into subst
  (hash-set! subst new-tvar new-type))


;; substitute type for every occurrence of tvar in _type
(define (apply-one-subst _type tvar type)
  (match _type
    [(int-type)
     (int-type)]
    
    [(bool-type)
     (bool-type)]
    
    [(ref-type t)
     (ref-type (apply-one-subst t tvar type))]
    
    [(pair-type t1 t2)
     (pair-type (apply-one-subst t1 tvar type)
                 (apply-one-subst t2 tvar type))]
    
    [(-> arg-type result-type)
     (-> (apply-one-subst arg-type tvar type)
         (apply-one-subst result-type tvar type))]
    
    [(type-var num)
     (if (equal? _type tvar)
         type
         _type)]))


;; for all tva[i] = t[i] in subst,
;; substitute t[i] for every occurrence of tvar[i] in type
(define (apply-subst-to-type type subst)
  (match type
    [(int-type)
     (int-type)]
    
    [(bool-type)
     (bool-type)]
    
    [(ref-type t)
     (ref-type (apply-subst-to-type t subst))]
    
    [(pair-type t1 t2)
     (pair-type (apply-subst-to-type t1 subst)
                (apply-subst-to-type t2 subst))]
    
    [(-> arg-type result-type)
     (-> (apply-subst-to-type arg-type subst)
         (apply-subst-to-type result-type subst))]
    
    [(type-var num)
     (hash-ref subst type (λ () type))]))