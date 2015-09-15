;; Extended MUPL Interpreter

#lang racket
(provide (all-defined-out)) ;; so we can put tests in a second file

;; definition of structures for  MUPL programs - Do NOT change
(struct var  (string) #:transparent)  ;; a variable, e.g., (var "foo")
(struct int  (num)    #:transparent)  ;; a constant number, e.g., (int 17)
(struct add  (e1 e2)  #:transparent)  ;; add two expressions
(struct ifgreater (e1 e2 e3 e4)    #:transparent) ;; if e1 > e2 then e3 else e4
(struct apair (e1 e2)     #:transparent) ;; make a new pair
(struct fst  (e)    #:transparent) ;; get first part of a pair
(struct snd  (e)    #:transparent) ;; get second part of a pair
(struct aunit ()    #:transparent) ;; unit value -- good for ending a list
(struct isaunit (e) #:transparent) ;; evaluate to 1 if e is unit else 0

(define tmpstr ".__tmp__.__tmp__.") ;; used by letrec

;;; used by interpreter program only

;; a closure is not in "source" programs; it is what functions evaluate to
(struct closure (env fun) #:transparent)
;; a recursive(?) k-argument function
(struct _fun  (nameopt var-list body) #:transparent)
;; function call, !!!assume the length of two lists are the same
(struct _call (funexp val-list)       #:transparent)
;; used in mletrec, modify the binding of var in the parent env
(struct _modify-env (var))
;; sequential exp
(struct _seq (hd rest))

;; convert racketlist to mupllist
(define (racketlist->mupllist list)
  (if (null? list)
      (aunit)
      (apair (let ([ head (car list) ])
               (if (pair? head)
                   (racketlist->mupllist head)
                   head))
             (racketlist->mupllist (cdr list)))))

;; convert mupllist to racketlist
(define (mupllist->racketlist list)
  (if (aunit? list)
      null
      (cons (let ([ head (apair-e1 list) ])
              (if (apair? head)
                  (mupllist->racketlist head)
                  head))
            (mupllist->racketlist (apair-e2 list)))))

;; act like list in Racket
(define (alist . args)
  (foldr apair (aunit) args))


;; env structure:
;; each env of the current function is a hash table for storing its own local bindings
;; and a pointer pointing to its parent's env
;; hash-table -> hash-tabl -> hash-table -> ... -> null

;; lookup a variable in an environment
(define (envlookup env str)
  (if (null? env)
      (error "unbound variable during evaluation" str)
      (let ([cur-env (car env)])
        (hash-ref cur-env str
                  (λ () (envlookup (cdr env) str))))))


;; test if e a basic value( int or aunit or closure? )
(define (mvalue? e)
  (or (int? e) (aunit? e) (closure? e)))

;; analyze the grammar of an exp, then return a proc that takes env as its param
(define (grammar-analyze e)
  (cond [(var? e)
         (λ (env)
           (envlookup env (var-string e)))] ;; lookup var in the env
        
        [(mvalue? e)
         (λ (env) e)] ;; basic values evaluate to themselves
        
        [(isaunit? e)
         (let ([eproc (grammar-analyze (isaunit-e e))])
           (λ (env)
             (if (aunit? (eproc env))
                 (int 1)
                 (int 0))))]
        
        ;; eval each parts of a apair to val
        [(apair? e)
         (let ([e1-proc (grammar-analyze (apair-e1 e))]
               [e2-proc (grammar-analyze (apair-e2 e))])
           (λ (env)
             (apair (e1-proc env)
                    (e2-proc env))))]
        
        [(fst? e)
         (let ([eproc (grammar-analyze (fst-e e))])
           (λ (env)
             (let ([v (eproc env)])
               (if (apair? v)
                   (apair-e1 v)
                   (error "MUPL fst applied to non-apair")))))]
        
        [(snd? e)
         (let ([eproc (grammar-analyze (snd-e e))])
           (λ (env)
             (let ([v (eproc env)])
               (if (apair? v)
                   (apair-e2 v)
                   (error "MUPL fst applied to non-apair")))))]
        
        ;; (add e1 e2) = e1 + e2 iff e1 and e2 are int type
        [(add? e)
         (let ([e1proc (grammar-analyze (add-e1 e))]
               [e2proc (grammar-analyze (add-e2 e))])
           (λ (env)
             (let ([v1 (e1proc env)]
                   [v2 (e2proc env)])
               (if (and (int? v1)
                        (int? v2))
                   (int (+ (int-num v1) 
                           (int-num v2)))
                   (error "MUPL addition applied to non-number")))))]
        
        ;; (ifgreater e1 e2 e3 e4), eval e1 and e2 first, if e1 and e2 are int type, ...
        [(ifgreater? e)
         (let ([e1proc (grammar-analyze (ifgreater-e1 e))]
               [e2proc (grammar-analyze (ifgreater-e2 e))]
               [e3proc (grammar-analyze (ifgreater-e3 e))]
               [e4proc (grammar-analyze (ifgreater-e4 e))])
           (λ (env)
             (let ([v1 (e1proc env)]
                   [v2 (e2proc env)])
               (if (and (int? v1) (int? v2))
                   (if (> (int-num v1) (int-num v2))
                       (e3proc env)
                       (e4proc env))
                   (error "MUPL ifgreater applied to non-number")))))]
        
        ;; lexical scoped function
        [(_fun? e)
         (let ([fn-name (_fun-nameopt e)]
               [fn-var-list (_fun-var-list e)]
               [fn-body (grammar-analyze (_fun-body e))])
           (λ (env)
             (closure env (_fun fn-name fn-var-list fn-body))))]
        
        ;; (_seq (hd rest)), sequential exps
        [(_seq? e)
         (let ([hd-proc (grammar-analyze (_seq-hd e))]
               [erest (_seq-rest e)])
           (if (aunit? erest)
               (λ (env)
                 (hd-proc env))
               (let ([rest-proc (grammar-analyze erest)])
                 (λ (env)
                   (begin
                     (hd-proc env)
                     (rest-proc env))))))]
        
        ;; used in mletrec,
        ;; modify the var's binding
        [(_modify-env? e)
         (let ([var (_modify-env-var e)])
           (λ (env)
             (let* ([cur-env (car env)]
                    [parent-env (cadr env)]
                    [val (hash-ref cur-env (string-append var tmpstr)
                                   (λ () (error "unbound variable" (string-append var tmpstr))))])
               (hash-update! parent-env var (λ (_) val)
                             (λ () (error "unbound variable" var))))))]
        
        ;; function call,
        ;; (struct _fun  (nameopt var-list body))
        ;; (struct _call (funexp val-list))
        [(_call? e)
         (let ([funexp-proc (grammar-analyze (_call-funexp e))])
           (λ (env)
             (let ([clos (funexp-proc env)])
               (if (closure? clos)
                   (let* ([_call-val-list (_call-val-list e)]
                          [fn (closure-fun clos)]
                          [fn-env (closure-env clos)]
                          [fn-name (_fun-nameopt fn)]
                          [fn-var-list (_fun-var-list fn)]
                          [fn-body-proc (_fun-body fn)]
                          [cur-env (make-hash)])
                     
                     (begin
                       (if fn-name
                           (hash-set! cur-env fn-name clos) ;; fn-name != #f, bind the function name : function body
                           null)
                       
                       ;; bind the var-val pairs
                       (letrec ([hash-var-val (λ (var-list val-list) ;; !!!assume the length of two lists are the same
                                                (if (null? var-list)
                                                    null
                                                    (begin
                                                      (hash-set! cur-env (car var-list) (eval-under-env (car val-list) env))
                                                      (hash-var-val (cdr var-list) (cdr val-list)))))])
                         (hash-var-val fn-var-list _call-val-list)
                         )
                       
                       ;; eval the function call
                       (fn-body-proc (cons cur-env fn-env)) ;; extend fn-env, the inner bindings will hide the outer env's)
                       ))
                   
                   (error "MUPL call applied to non-function")
                   ))))]
        
        [#t (error (format "bad MUPL expression: ~v" e))]))

;; evaluate e under env
(define (eval-under-env e env)
  ((grammar-analyze e) env))

;; evaluate the expression e under the null evn
(define (eval-exp e)
  (eval-under-env e null))


;;----------------------------------- Syntatic Sugar ----------------------------------------

;; e1 = (aunit), e2; otherwise e3
(define (ifaunit e1 e2 e3)
  (ifgreater (isaunit e1) (int 0)
             e2 e3))

;; (fun fn-name (var0 ...) body)
(define-syntax fun
  (syntax-rules ()
    [(fun fn-name () body)
     (_fun fn-name (list "") body)]
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

;; (mletrec ([var0 val0] ...) body) = (mlet ([var0 (aunit] ...)
;;                                       (mlet ([var0.__tmp__ val0] ...)
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
     (mlet ([var0 (aunit)] [var-rest (aunit)] ...)
           (mlet ([(string-append var0 tmpstr) val0]
                  [(string-append var-rest tmpstr) val-rest] ...)
                 (seq (_modify-env var0)
                      (_modify-env var-rest) ...
                      body)))]))