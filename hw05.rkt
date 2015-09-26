;; Extended MUPL Interpreter

#lang racket
(provide (all-defined-out)) ;; so we can put tests in a second file

;; definition of structures for  MUPL programs - Do NOT change
(struct var  (string) #:transparent)  ;; a variable, e.g., (var "foo")

(struct int  (num)    #:transparent)  ;; a constant number, e.g., (int 17)
(struct add  (e1 e2)  #:transparent)  ;; add two expressions
(struct isgreater (e1 e2) #:transparent) ;; T if e1 > e2, F otherwise
(struct isless (e1 e2) #:transparent) ;; T if e1 < e2, F otherwise
(struct isequal (e1 e2) #:transparent) ;; T if e1 = e2, F otherwise

(struct apair (e1 e2)     #:transparent) ;; make a new pair
(struct fst  (e)    #:transparent) ;; get first part of a pair
(struct snd  (e)    #:transparent) ;; get second part of a pair

(struct aunit ()    #:transparent) ;; unit value -- good for ending a list
(struct isaunit (e) #:transparent) ;; evaluate to T if e is unit else F

(struct bool (e) #:transparent) ;; boolean, T or F
(define T 'T) ;; true
(define F 'F) ;; false
(struct if-then-else (e1 e2 e3) #:transparent) ;; if e1 is true, e2; otherwise e3

(define storage (make-vector 0)) ;; model the memory to store the mutable datum

(struct ref (v) #:transparent) ;; ref type, indicate a location of a value, the contents of v is mutable
(struct newref! (v) #:transparent) ;; allocate a location to store v
(struct deref (loc) #:transparent) ;; read the value stored in loc, loc must be a ref type
(struct setref! (loc v) #:transparent) ;; set the content of loc as v, loc must be a ref type

(struct call-cc (fn) #:transparent) ;; equivalent to call/cc in Racket

(struct try-catch-except (try-exp catch-var except-handler) #:transparent) ;; exception
(struct raise (except)) ;; raise an exception
(define except-handler (λ (val) (error "exception caught:" val))) ;; global exception handler
(define (set-except-handler! new-except-handler) (set! except-handler new-except-handler)) ;; set the global exception handler


;;; used by interpreter program only

;; a closure is not in "source" programs; it is what functions evaluate to
(struct closure (env fun) #:transparent)
;; a recursive(?) k-argument function
(struct _fun  (nameopt var-list body) #:transparent)
;; function call, !!!assume the length of two lists are the same
(struct _call (funexp val-list)       #:transparent)

(define tmpstr ".__tmp__.__tmp__.") ;; used by letrec
;; used in mletrec, modify the binding of var in the parent env
(struct _modify-env (var) #:transparent)

;; sequential exp
(struct _seq (hd rest) #:transparent)

;; def, equivalent to define in racket
(struct def (var e) #:transparent)

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

;; cont:
;; (λ (val) ...)

;; lookup a variable in an environment
(define (envlookup env str)
  (if (null? env)
      (error "unbound variable during evaluation" str)
      (let ([cur-env (car env)])
        (hash-ref cur-env str
                  (λ () (envlookup (cdr env) str))))))


;; test if e a basic value( int or aunit or closure? )
(define (mvalue? e)
  (or (int? e) (bool? e) (aunit? e) (ref? e) (closure? e)))

;; analyze the syntactic of an exp, then return a proc that takes env as its param
(define (syntactic-analyze e)
  
  (define (eval-binary-op exp selector1 selector2 calc-proc)
    (let ([e1proc (syntactic-analyze (selector1 e))]
          [e2proc (syntactic-analyze (selector2 e))])
      (λ (env cont)
        (e1proc env (λ (v1)
                      (e2proc env (λ (v2)
                                    (cont (calc-proc v1 v2)))))))))
  
  (cond [(var? e)
         (λ (env cont)
           (cont (envlookup env (var-string e))))] ;; lookup var in the env
        
        [(mvalue? e)
         (λ (env cont)
           (cont e))] ;; basic values evaluate to themselves
        
        [(isaunit? e)
         (let ([eproc (syntactic-analyze (isaunit-e e))])
           (λ (env cont)
             (eproc env (λ (pred)
                          (if (aunit? pred)
                              (cont (bool T))
                              (cont (bool F)))))))]
        
        [(newref!? e)
         (let ([e-proc (syntactic-analyze (newref!-v e))])
           (λ (env cont)
             (e-proc env (λ (val)
                           (let ([storage-addr (vector-length storage)])
                             (begin (set! storage (vector-append storage (vector val)))
                                    (cont (ref storage-addr))))))))]
        
        [(deref? e)
         (let ([e-proc (syntactic-analyze (deref-loc e))])
           (λ (env cont)
             (e-proc env (λ (refv)
                           (if (ref? refv)
                               (cont (vector-ref storage (ref-v refv)))
                               (error "MUPL deref applied to non-ref"))))))]
        
        [(setref!? e)
         (let ([loc-proc (syntactic-analyze (setref!-loc e))]
               [v-proc (syntactic-analyze (setref!-v e))])
           (λ (env cont)
             (loc-proc env (λ (refv)
                             (if (ref? refv)
                                 (v-proc env (λ (val)
                                               (vector-set! storage (ref-v refv) val)
                                               (cont (aunit))))
                                 (error "MUPL setref applied to non-ref"))))))]
        
        [(if-then-else? e)
         (let ([e1-proc (syntactic-analyze (if-then-else-e1 e))]
               [e2-proc (syntactic-analyze (if-then-else-e2 e))]
               [e3-proc (syntactic-analyze (if-then-else-e3 e))])
           (λ (env cont)
             (e1-proc env (λ (pred)
                            (if (bool? pred)
                                (if (eq? T (bool-e pred))
                                    (e2-proc env cont)
                                    (e3-proc env cont))
                                (error "MUPL if-then-else applied to non-bool"))))))]
        
        ;; eval each parts of a apair to val
        [(apair? e)
         (let ([e1-proc (syntactic-analyze (apair-e1 e))]
               [e2-proc (syntactic-analyze (apair-e2 e))])
           (λ (env cont)
             (e1-proc env (λ (e1-val)
                            (e2-proc env (λ (e2-val)
                                           (cont (apair e1-val e2-val))))))))]
        
        [(fst? e)
         (let ([eproc (syntactic-analyze (fst-e e))])
           (λ (env cont)
             (eproc env (λ (val)
                          (if (apair? val)
                              (cont (apair-e1 val))
                              (error "MUPL fst applied to non-apair"))))))]
        
        [(snd? e)
         (let ([eproc (syntactic-analyze (snd-e e))])
           (λ (env cont)
             (eproc env (λ (val)
                          (if (apair? val)
                              (cont (apair-e2 val))
                              (error "MUPL snd applied to non-apair"))))))]
        
        
        ;; (add e1 e2) = e1 + e2 iff e1 and e2 are int type
        [(add? e)
         (eval-binary-op e add-e1 add-e2 (λ (v1 v2)
                                           (int (+ (int-num v1) 
                                                   (int-num v2)))))]
        
        ;; (struct isgreater (e1 e2)) , T if e1 > e2, F otherwise
        [(isgreater? e)
         (eval-binary-op e isgreater-e1 isgreater-e2 (λ (v1 v2)
                                                       (if  (> (int-num v1) 
                                                               (int-num v2))
                                                            (bool T)
                                                            (bool F))))]
        
        ;; (struct isless (e1 e2)) , T if e1 < e2, F otherwise
        [(isless? e)
         (eval-binary-op e isless-e1 isless-e2 (λ (v1 v2)
                                                 (if  (< (int-num v1) 
                                                         (int-num v2))
                                                      (bool T)
                                                      (bool F))))]
        
        ;; (struct isequal (e1 e2)) , T if e1 = e2, F otherwise
        [(isequal? e)
         (eval-binary-op e isequal-e1 isequal-e2 (λ (v1 v2)
                                                   (if  (= (int-num v1) 
                                                           (int-num v2))
                                                        (bool T)
                                                        (bool F))))]
        
        ;; (_seq (hd rest)), sequential exps
        [(_seq? e)
         (let ([hd-proc (syntactic-analyze (_seq-hd e))]
               [erest (_seq-rest e)])
           (if (aunit? erest)
               (λ (env cont)
                 (hd-proc env cont))
               (let ([rest-proc (syntactic-analyze erest)])
                 (λ (env cont)
                   (hd-proc env (λ (val)
                                  (rest-proc env cont)))))))]
        
        ;; (def (var e)), bind var to e in the current env
        [(def? e)
         (let ([var (def-var e)]
               [e-proc (syntactic-analyze (def-e e))])
           (λ (env cont)
             (e-proc env (λ (val)
                           (hash-set! (car env) var val)
                           (cont (aunit))))))]
        
        ;; (struct raise (except))
        ;; raise an exception
        ([raise? e]
         (let ([raise-proc (syntactic-analyze (raise-except e))])
           (λ (env cont)
             (raise-proc env except-handler))))
        
        ;; (struct try-catch-except (try-exp catch-var except-handler))
        ;; exception
        [(try-catch-except? e)
         (let ([try-proc (syntactic-analyze (try-catch-except-try-exp e))]
               [catch-var (try-catch-except-catch-var e)]
               [except-proc (syntactic-analyze (try-catch-except-except-handler e))])
           (λ (env cont)
             (let ([old-except-handler except-handler])
               (set-except-handler! (λ (val) ;; set the new excpet-handler
                                      (set-except-handler! old-except-handler) ;; restore the original except-handler
                                      (except-proc (let ([ext-env (make-hash)]) ;; extend env with catch-var, run except-handler
                                                     (hash-set! ext-env catch-var val)
                                                     (cons ext-env env))
                                                   cont)))
               (try-proc env (λ (val)
                               (set-except-handler! old-except-handler) ;; try returns normally, then restore the original except-handler
                               (cont val))))))]
        
        ;; used in mletrec,
        ;; modify the var's binding
        [(_modify-env? e)
         (let ([var (_modify-env-var e)])
           (λ (env cont)
             (let* ([cur-env (car env)]
                    [parent-env (cadr env)]
                    [val (hash-ref cur-env (string-append var tmpstr)
                                   (λ () (error "unbound variable" (string-append var tmpstr))))])
               (hash-update! parent-env var (λ (_) val)
                             (λ () (error "unbound variable" var))))
             (cont (aunit))))]
        
        ;; lexical scoped function
        [(_fun? e)
         (let ([fn-name (_fun-nameopt e)]
               [fn-var-list (_fun-var-list e)]
               [fn-body (syntactic-analyze (_fun-body e))])
           (λ (env cont)
             (cont (closure env (_fun fn-name fn-var-list fn-body)))))]
        
        ;; (struct call-cc (fn)), call/cc
        ;; wrap the current continuation in a closure and pass it to fn,
        ;; then call fn with cont-closure as its param
        [(call-cc? e)
         (let ([funexp-proc (syntactic-analyze (call-cc-fn e))])
           (λ (env cont)
             (funexp-proc env (λ (clos)
                                (if (closure? clos)
                                    (let ([cur-env (make-hash)]
                                          [fn (closure-fun clos)]
                                          [fn-env (closure-env clos)])
                                      (hash-set! cur-env
                                                 (car (_fun-var-list fn))
                                                 (closure null (_fun #f (list "val") ;; cont-closure shouldn't related to any env
                                                                     (λ (env _cont) (cont (envlookup env "val"))))))
                                      ((_fun-body fn) (cons cur-env fn-env)
                                                      cont))
                                    (error "MUPL call-cc applied to non-function"))))))]
        
        ;; function call,
        ;; (struct _fun  (nameopt var-list body))
        ;; (struct _call (funexp val-list))
        [(_call? e)
         (let ([funexp-proc (syntactic-analyze (_call-funexp e))]
               [val-proc-list (map syntactic-analyze (_call-val-list e))])
           (λ (env cont)
             (funexp-proc env (λ (clos)
                                (if (closure? clos)
                                    (let* ([fn (closure-fun clos)]
                                           [fn-env (closure-env clos)]
                                           [fn-name (_fun-nameopt fn)]
                                           [fn-var-list (_fun-var-list fn)]
                                           [fn-body-proc (_fun-body fn)]
                                           [cur-env (make-hash)]
                                           [fn-body-env (cons cur-env fn-env)]) ;; extend env
                                      
                                      (begin
                                        (if fn-name
                                            (hash-set! cur-env fn-name clos) ;; fn-name != #f, bind the function name : function body
                                            null)
                                        
                                        ;; bind the var-val pairs
                                        (letrec ([hash-var-val (λ (var-list val-proc-list cont)
                                                                 (if (null? var-list)
                                                                     (cont null)
                                                                     ((car val-proc-list) env (λ (val)
                                                                                                (hash-set! cur-env (car var-list) val)
                                                                                                (hash-var-val (cdr var-list)
                                                                                                              (cdr val-proc-list)
                                                                                                              cont)))))])
                                          (hash-var-val fn-var-list val-proc-list (λ (val)
                                                                                    (fn-body-proc fn-body-env cont))))))
                                    
                                    (error "MUPL call applied to non-function"))))))]
        
        
        [#t (error (format "bad MUPL expression: ~v" e))]))

;; evaluate e under env and cont
;; cont for continuation
(define (eval-under-env-cont e env cont)
  ((syntactic-analyze e) env cont))

;; evaluate the expression e under the top env and the top continuation
(define (eval-exp e)
  (eval-under-env-cont e (list (make-hash)) (λ (val) val)))


;;----------------------------------- Syntatic Sugar ----------------------------------------

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