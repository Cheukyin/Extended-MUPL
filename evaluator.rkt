#lang racket
(require rackunit "ast-struct.rkt")

(provide eval-under-env-cont)


(define storage (make-vector 0)) ;; model the memory to store the mutable datum

(define except-handler (λ (val) (error "exception caught:" val))) ;; global exception handler
(define (set-except-handler! new-except-handler) (set! except-handler new-except-handler)) ;; set the global exception handler


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
  
  (define (hash-var-val var-list val-proc-list val-env fn-body-env cont)
    (if (null? var-list)
        (cont null)
        ((car val-proc-list) val-env (λ (val)
                                       (hash-set! (car fn-body-env) (car var-list) val)
                                       (hash-var-val (cdr var-list)
                                                     (cdr val-proc-list)
                                                     val-env
                                                     fn-body-env
                                                     cont)))))
  
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
        
        [(_letrec? e)
         (let ([var-list (_letrec-var-list e)]
               [val-proc-list (map syntactic-analyze (_letrec-val-list e))]
               [fn-body-proc (syntactic-analyze (_letrec-body e))])
           (λ (env cont)
             (let* ([cur-env (make-hash)]
                   [ext-env (cons cur-env env)])
               (map (λ (var) (hash-set! cur-env var (dummy)))
                    var-list) ;; extend env, and map each var to (dummy), will be modified later
               ;; bind the var-val pairs
               (hash-var-val var-list val-proc-list ext-env ext-env (λ (val)
                                                                      (fn-body-proc ext-env cont))))))]
        
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
                                        (if fn-name ;; fn-name != #f, bind the function name : function body
                                            (hash-set! cur-env fn-name clos)
                                            null)
                                        
                                        (hash-var-val fn-var-list val-proc-list env fn-body-env 
                                                      (λ (val)
                                                        (fn-body-proc fn-body-env cont)))))
                                    
                                    (error "MUPL call applied to non-function"))))))]
        
        
        [#t (error (format "bad MUPL expression: ~v" e))]))

;; evaluate e under env and cont
;; cont for continuation
(define (eval-under-env-cont e env cont)
  ((syntactic-analyze e) env cont))