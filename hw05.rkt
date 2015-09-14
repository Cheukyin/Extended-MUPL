;; MUPL Interpreter

#lang racket
(provide (all-defined-out)) ;; so we can put tests in a second file

;; definition of structures for MUPL programs - Do NOT change
(struct var  (string) #:transparent)  ;; a variable, e.g., (var "foo")
(struct int  (num)    #:transparent)  ;; a constant number, e.g., (int 17)
(struct add  (e1 e2)  #:transparent)  ;; add two expressions
(struct ifgreater (e1 e2 e3 e4)    #:transparent) ;; if e1 > e2 then e3 else e4
(struct apair (e1 e2)     #:transparent) ;; make a new pair
(struct fst  (e)    #:transparent) ;; get first part of a pair
(struct snd  (e)    #:transparent) ;; get second part of a pair
(struct aunit ()    #:transparent) ;; unit value -- good for ending a list
(struct isaunit (e) #:transparent) ;; evaluate to 1 if e is unit else 0


;;; used by interpreter program only

;; a closure is not in "source" programs; it is what functions evaluate to
(struct closure (env fun) #:transparent)
;; a recursive(?) k-argument function
(struct _fun  (nameopt var-list body) #:transparent)
;; function call, !!!assume the length of two lists are the same
(struct _call (funexp val-list)       #:transparent)
;; modify var's binding
(struct _modify-env (var))

;; convert racketlist to mupllist
(define (racketlist->mupllist list)
  (if (null? list)
      (aunit)
      (apair (let ([ head (car list) ])
              (if (pair? head)
                 (racketlist->mupllist head)
                 head
                 )
              )
             (racketlist->mupllist (cdr list)))
      )
  )

;; convert mupllist to racketlist
(define (mupllist->racketlist list)
  (if (aunit? list)
      null
      (cons (let ([ head (apair-e1 list) ])
             (if (apair? head)
                 (mupllist->racketlist head)
                 head
                 )
              )
             (mupllist->racketlist (apair-e2 list))
             )
      )
  )

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

;; modify binding of the var
(define (modify-env env str val)
  (if (null? env)
      (error "unbound variable during evaluation" str)
      (let ([cur-env (car env)])
        (hash-update! cur-env str (λ (n) val)
                      (λ () (modify-env (cdr env) str val))))))

;; evaluate e under env
(define (eval-under-env e env)
  ;; test if e a basic value( int or aunit or closure? )
  (define (mvalue? e)
    (or (int? e) (aunit? e) (closure? e)))
  
  (cond [(var? e) 
         (envlookup env (var-string e))] ;; lookup var in the env

        ;; basic values evaluate to themselves
        [(mvalue? e)
         e]

        ;; lexical scoped function
        [(_fun? e)
         (closure env e)]

        [(isaunit? e)
         (if (aunit? (eval-under-env (isaunit-e e) env))
             (int 1)
             (int 0))]

        ;; eval each parts of a apair to val
        [(apair? e)
         (apair (eval-under-env (apair-e1 e) env)
                (eval-under-env (apair-e2 e) env))]

        [(fst? e)
         (let ([v (eval-under-env (fst-e e) env)])
           (if (apair? v)
               (apair-e1 v)
               (error "MUPL fst applied to non-apair")))]

        [(snd? e)
         (let ([v (eval-under-env (snd-e e) env)])
           (if (apair? v)
               (apair-e2 v)
               (error "MUPL fst applied to non-apair")))]

        ;; (add e1 e2) = e1 + e2 iff e1 and e2 are int type
        [(add? e) 
         (let ([v1 (eval-under-env (add-e1 e) env)]
               [v2 (eval-under-env (add-e2 e) env)])
           (if (and (int? v1)
                    (int? v2))
               (int (+ (int-num v1) 
                       (int-num v2)))
               (error "MUPL addition applied to non-number")))]

        ;; (ifgreater e1 e2 e3 e4), eval e1 and e2 first, if e1 and e2 are int type, ...
        [(ifgreater? e)
         (let ([v1 (eval-under-env (ifgreater-e1 e) env)]
               [v2 (eval-under-env (ifgreater-e2 e) env)])
           (if (and (int? v1) (int? v2))
               (if (> (int-num v1) (int-num v2))
                   (eval-under-env (ifgreater-e3 e) env)
                   (eval-under-env (ifgreater-e4 e) env))
               (error "MUPL ifgreater applied to non-number")))]

        ;; function call
        [(_call? e)
         (let ([clos (eval-under-env (_call-funexp e) env)])
           (if (closure? clos)
               (let* ([_call-val-list (_call-val-list e)]
                      [fn (closure-fun clos)]
                      [fn-env (closure-env clos)]
                      [fn-name (_fun-nameopt fn)]
                      [fn-var-list (_fun-var-list fn)]
                      [fn-body (_fun-body fn)]
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
                  (eval-under-env fn-body
                                 (cons cur-env fn-env)) ;; extend fn-env, the inner bindings will hide the outer env's)
                 ))
               (error "MUPL call applied to non-function")
               ))]
        
        [#t (error (format "bad MUPL expression: ~v" e))]))

;; evaluate the expression e under the null evn
(define (eval-exp e)
  (eval-under-env e null))


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
                  body))
     ]))