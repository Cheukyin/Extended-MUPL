#lang racket
(provide (all-defined-out))

;; definition of structures for  MUPL programs
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

(struct ref (v) #:transparent) ;; ref type, indicate a location of a value, the contents of v is mutable
(struct newref! (v) #:transparent) ;; allocate a location to store v
(struct deref (loc) #:transparent) ;; read the value stored in loc, loc must be a ref type
(struct setref! (loc v) #:transparent) ;; set the content of loc as v, loc must be a ref type

(struct call-cc (fn) #:transparent) ;; equivalent to call/cc in Racket

(struct try-catch-except (try-exp catch-var except-handler) #:transparent) ;; exception
(struct raise (except)) ;; raise an exception


;;; used by interpreter program only

;; dummy, can be any type
(struct dummy ())

;; a closure is not in "source" programs; it is what functions evaluate to
(struct closure (env fun) #:transparent)
;; a recursive(?) k-argument function
(struct _fun  (nameopt var-list body) #:transparent)
;; function call, !!!assume the length of two lists are the same
(struct _call (funexp val-list)       #:transparent)
;; letrec, !!!assume the length of two lists are the same
(struct _letrec (var-list val-list body) #:transparent)

;; sequential exp
(struct _seq (hd rest) #:transparent)

;; def, equivalent to define in racket
(struct def (var e) #:transparent)
