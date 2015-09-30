#lang racket
(require "ast-struct.rkt")
(require "type-struct.rkt")
(provide type-of-under-env-subst)

;; env is a list of hash-table,
;; subst for substition, is a hash-table( key is type-var, value is its concrete type)
;; Caveat: this proc has side effect on subst
;; if the type of exp can be inferred correctly, return ('ok type-of-exp)
;; otherwise, return the wrong type-equation ('error (exp . (type-lhs . type-rhs)))
(define (type-of-under-env-subst exp env subst)
  
  (define (_type_of exp env kont)
    
    ;; for add, isgreater, isless, isequal
    (define (type-infer-binary-int-op e1 e2 inferred-type env exp)
      (let ([t1 (_type_of e1 env kont)]
            [t2 (_type_of e2 env kont)])
        (unifier t1 (int-type) subst exp kont)
        (unifier t2 (int-type) subst exp kont)
        inferred-type))
    
    (match exp
      ;; int
      [(int val)
       (int-type)]
      
      ;; bool
      [(bool val)
       (bool-type)]
      
      ;; unit-type
      [(aunit)
       (unit-type)]
      
      ;; e: any type --> bool
      [(isaunit e)
       (let ([t (_type_of e env kont)])
         (bool-type))]
      
      ;; e: t --> (ref-type t)
      [(newref! e)
       (let ([t (_type_of e env kont)])
         (ref-type t))]
      
      ;; e: (ref-type t) --> t
      [(deref e)
       (let ([t (_type_of e env kont)]
             [t-result (fresh-type-var)])
         (unifier t (ref-type t-result) subst exp kont)
         t-result)]
      
      ;; loc: (ref-type t), v: t --> unit-type
      [(setref! loc v)
       (let ([t-loc (_type_of loc env kont)]
             [t-v (_type_of v env kont)]
             [t (fresh-type-var)])
         (unifier t-loc (ref-type t) subst exp kont)
         (unifier t-v t subst exp kont)
         (unit-type))]
      
      ;; e1: int, e2: int --> int
      [(add e1 e2)
       (type-infer-binary-int-op e1 e2 (int-type) env exp)]
      ;; e1: int, e2: int --> bool
      [(isgreater e1 e2)
       (type-infer-binary-int-op e1 e2 (bool-type) env exp)]
      [(isless e1 e2)
       (type-infer-binary-int-op e1 e2 (bool-type) env exp)]
      [(isequal e1 e2)
       (type-infer-binary-int-op e1 e2 (bool-type) env exp)]
      
      ;; cond: bool, e1: t, e2: t --> t
      [(if-then-else cond e1 e2)
       (let* ([t-cond (_type_of cond env kont)]
              [t1 (_type_of e1 env kont)]
              [t2 (_type_of e2 env kont)])
         (unifier t-cond (bool-type) subst exp kont)
         (unifier t1 t2 subst exp kont)
         t1)]
      
      ;; e1: t1, ..., ei: ti --> unit-type
      [(_seq hd tl)
       (_type_of hd env kont)
       (_type_of tl env kont)]
      
      ;; e:t, env --> [v: t]env
      [(def v e)
       (hash-set! (car env) v
                  (_type_of e env kont))]
      
      ;; lookup v's type
      [(var v) ;; !!!!!!!!! very strange, v captured hear is a var struct
       ;; (envlookup env v)
       (envlookup env (var-str v))]
      
      [_
       (error "error expression:" exp)]))
  
  (call/cc 
   (λ (kont)
     (let ([t (_type_of exp env kont)])
       (cons 'ok (apply-subst-to-type t subst))))))


;; lookup var's type in env
(define (envlookup env var)
  (if (null? env)
      (error "unbound varible while type checking:" var)
      (hash-ref (car env) var
                (λ () (envlookup (cdr env) var)))))


;; insert typed-lhs = type-rhs into subst return 'ok
;; if no inconsistency or violation occurs
;; otherwise, print the error and the exp that cause the error
;;            then return the error equation ('error (exp . (t-lhs . t-rhs)))
(define (unifier type-lhs type-rhs subst exp kont)
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
         (unifier (->-arg-type t-lhs) (->-arg-type t-rhs) subst exp kont)
         (unifier (->-result-type t-lhs) (->-result-type t-rhs) subst exp kont)
         'ok]
        
        [(and (pair-type? t-lhs) (pair-type? t-rhs)) ;; pair type
         (unifier (pair-type-t1 t-lhs) (pair-type-t1 t-rhs) subst exp kont)
         (unifier (pair-type-t2 t-lhs) (pair-type-t2 t-rhs) subst exp kont)
         'ok]
        
        [(and (ref-type? t-lhs) (ref-type? t-rhs) subst exp kont)
         (unifier (ref-type-t t-lhs) (ref-type-t t-rhs) subst exp kont)
         'ok]
        
        [else
         (kont (report-type-error "type-inconsistency:" exp t-lhs t-rhs))])))


;; check if tvar occurs in type
(define (tvar-occur-in-type? tvar type)
  (match type
    [(int-type) #f]
    [(bool-type) #f]
    [(unit-type) #f]
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
  (cons 'error (cons exp (cons t1 t2))))
  

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
    
    [(unit-type)
     (unit-type)]
    
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
    
    [(unit-type)
     (unit-type)]
    
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