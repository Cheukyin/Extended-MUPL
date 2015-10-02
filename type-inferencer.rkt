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
       (let ([t-hd (_type_of hd env kont)])
         (if (aunit? tl)
             t-hd
             (_type_of tl env kont)))]
      
      ;; e:t, env --> [v: t]env
      [(def v e)
       (hash-set! (car env) v
                  (_type_of e env kont))]
      
      ;; (arg1, .., argn): (t1, ..., tn), env
      ;; fn-body: tbody, [arg1: t1, ..., argn: tn, fn-name: tf]env
      ;; -->
      ;; tf = (arg1, ..., argn) -> tbody, env
      [(_fun fn-name fn-var-list fn-body)
       (let* ([fn-env (make-hash)] ;; create a new env
              [fn-t (fresh-type-var)] ;; type of the function
              [arg-type-list (if (equal? fn-var-list (list (aunit)))
                                 (list (unit-type)) ;; if no args
                                 (map (λ (arg) ;; map arg types in fn-env and return a list of arg-type
                                        (let ([t (fresh-type-var)])
                                          (hash-set! fn-env arg t)
                                          t))
                                      fn-var-list))])
         (if fn-name ;; if not anonymous function, map fn-t in fn-env
             (hash-set! fn-env fn-name fn-t)
             null)
         ;; infer type of fn-body
         (let ([t-body (_type_of fn-body (cons fn-env env) kont)])
           ;; add fn-t = arg-type-list -> t-body to subst
           (unifier fn-t (-> arg-type-list t-body) subst exp kont)
           ;; return type the funtion
           fn-t))]
      
      
      ;; call anonymous function, let semantics
      ;; types of val may be polymorphic
      ;; (val0, ..., valn): (t0, ..., tn), env
      ;; fn-body: t, [val0: t0, ..., valn: tn]env
      ;; -->
      ;; t
      [(_call (_fun #f fn-var-list fn-body) val-list)
       (let* ([fn-env (make-hash)] ;; create a new env
              [val-type-list (if (equal? fn-var-list (list (aunit)))
                                 (list (unit-type)) ;; if no args
                                 (map (λ (val) ;; infer type of val-list return a list of val-type
                                        (generize-type-exp (_type_of val env kont) subst)) ;; generize t if possible
                                      val-list))])
         ;; hash types of val into fn-env
         (hash-var-val-list-into-env fn-var-list val-type-list fn-env)
         ;; infer type of fn-body
         (_type_of fn-body (cons fn-env env) kont))]
      
      
      ;; letrec polymorphic
      [(_letrec var-list val-list body)
       (let* ([new-env (make-hash)]
              [var-tvar-pair-list (map (λ (var) 
                                         (let ([tvar (fresh-type-var)])
                                           (hash-set! new-env var tvar) ;; hash new tvar into new-env
                                           (cons var tvar))) ;; return var-tvar pairs
                                       var-list)]) ;; allocate a new type-var for each var
         (let* ([env (cons new-env env)] ;; extend env
                [val-type-list (map (λ (val) (_type_of val env kont)) ;; infer type of val-list
                                    val-list)])
           ;;unifiy var-tvar-pair and val-type-list
           (letrec ([unify-vart-valt (λ (var-tvar-list val-type-list)
                                       (if (null? val-type-list)
                                           null
                                           (begin
                                             (unifier (cdar var-tvar-list)
                                                      (car val-type-list)
                                                      subst exp kont)
                                             (unify-vart-valt (cdr var-tvar-list)
                                                              (cdr val-type-list)))))])
             (unify-vart-valt var-tvar-pair-list val-type-list))
           ;; generize and again hash into new-env
           (map (λ (var-tvar)
                  (hash-set! new-env
                             (car var-tvar)
                             (generize-type-exp (cdr var-tvar) subst)))
                var-tvar-pair-list)
           ;; infer type of body
           (_type_of body env kont)))]
      
     
      
      ;; (val0, ..., valn): (t0, ..., tn), fn: (t0, ..., tn) -> t
      ;; -->
      ;; t
      
      ;; call named function, polymorphisim not supported
      [(_call (_fun fn-name fn-var-list fn-body) val-list)
       (let ([fn-t (_type_of (_fun fn-name fn-var-list fn-body) env kont)] ;; infer fn's type
             [val-type-list (map (λ (val) ;; infer val-list's type
                                   (_type_of val env kont))
                                 val-list)]
             [t-result (fresh-type-var)]) ;; type calling result
         (unifier fn-t (-> val-type-list t-result) subst exp kont) ;; fn-t = val-type-list -> t-result
         t-result)]
      
      ;; call function defined elsewhere
      [(_call fn val-list)
       (let ([fn-t (_type_of fn env kont)] ;; lookup fn's type
             [val-type-list (map (λ (val) ;; infer val-list's type
                                   (_type_of val env kont))
                                 val-list)]
             [t-result (fresh-type-var)]) ;; type calling result
         (unifier fn-t (-> val-type-list t-result) subst exp kont) ;; fn-t = val-type-list -> t-result
         t-result)]
      
      
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
      (let ([t (hash-ref (car env) var
                         (λ () (envlookup (cdr env) var)))])
        (if (type-scheme? t)
            (instantiate-type-scheme t) ;; if t is a type scheme, instantiate it
            t))))


(define (hash-var-val-list-into-env var-list val-list env)
  (if (and (null? var-list)
           (null? val-list))
      null
      (if (or (null? var-list)
              (null? val-list))
          (error "len of var and val different")
          (begin
            (hash-set! env (car var-list) (car val-list))
            (hash-var-val-list-into-env (cdr var-list) (cdr val-list) env)))))


(define (generize-type-exp type subst)
  (letrec ([find-tvar (λ (t tvar-list) ;; generize type if any tvar is found
                        (match t
                          [(int-type)
                           tvar-list]
                          
                          [(bool-type)
                           tvar-list]
                          
                          [(unit-type)
                           tvar-list]
                          
                          [(ref-type tr)
                           (find-tvar tr tvar-list)]
                          
                          [(pair-type t1 t2)
                           (let ([l (find-tvar t1 tvar-list)])
                             (find-tvar t2 l))]
                          
                          ;; function args type list
                          [(cons hd tl)
                           (let ([l (find-tvar hd tvar-list)])
                             (if (null? tl)
                                 l
                                 (find-tvar tl l)))]
                          
                          [(-> arg-type result-type)
                           (let ([l (find-tvar arg-type tvar-list)])
                             (find-tvar result-type l))]
                          
                          [(type-var num)
                           (if (member t tvar-list)
                               tvar-list
                               (cons t tvar-list))]))])
    
    (let* ([t (apply-subst-to-type type subst)]
           [tvar-list (find-tvar t null)])
      (if (null? tvar-list)
          t ;; if no tvar found, return type directly
          (type-scheme tvar-list t)))))


(define (instantiate-type-scheme type-schm) ;; instantiate type-scheme
  (let ([subst (make-hash)])
    (match type-schm
      [(type-scheme tvar-list type)
       (map (λ (tvar)
              (hash-set! subst tvar (fresh-type-var)))
            tvar-list)
       (apply-subst-to-type type subst)])))


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
        
        ;; function args type list
        [(and (list? t-lhs) (list? t-rhs))
         (let ([hd-lhs (car t-lhs)]
               [hd-rhs (car t-rhs)]
               [tl-lhs (cdr t-lhs)]
               [tl-rhs (cdr t-rhs)])
           (unifier hd-lhs hd-rhs subst exp kont)
           (if (and (not (null? tl-lhs))
                    (not (null? tl-rhs)))
               (unifier tl-lhs tl-lhs subst exp kont)
               (if (or (not (null? tl-lhs))
                       (not (null? tl-rhs)))
                   (kont (report-type-error "len of args different" exp t-lhs t-rhs))
                   'ok)))]
        
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
    
    ;; function args type list
    [(cons hd tl)
     (or (tvar-occur-in-type? tvar hd)
         (if (null? tl)
             #f
             (tvar-occur-in-type? tvar tl)))]
    
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
    
    ;; function args type list
    [(cons hd tl)
     (cons (apply-one-subst hd tvar type)
           (if (null? tl)
               null
               (apply-one-subst tl tvar type)))]
    
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
    
    ;; function args type list
    [(cons hd tl)
     (cons (apply-subst-to-type hd subst)
           (if (null? tl)
               null
               (apply-subst-to-type tl subst)))]
    
    [(-> arg-type result-type)
     (-> (apply-subst-to-type arg-type subst)
         (apply-subst-to-type result-type subst))]
    
    [(type-var num)
     (hash-ref subst type (λ () type))]))