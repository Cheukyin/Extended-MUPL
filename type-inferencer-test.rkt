#lang racket

(require rackunit "main.rkt" "ast-struct.rkt" "type-struct.rkt")
(require rackunit/text-ui)

(define (adjust-tvar-num type)
  (let ([subst (make-hash)]
        [fresh-typevar-num (let ([num 0])
                             (λ () 
                               (set! num (+ num 1))
                               (type-var num)))])
    (letrec ([_adj (λ (t)
                     (match t
                       [(int-type)
                        (int-type)]
                       
                       [(bool-type)
                        (bool-type)]
                       
                       [(unit-type)
                        (unit-type)]
                       
                       [(ref-type rt)
                        (ref-type (_adj rt))]
                       
                       [(pair-type t1 t2)
                        (pair-type (_adj t1)
                                   (_adj t2))]
                       
                       ;; function args
                       [(cons hd tl)
                        (cons (_adj hd)
                              (if (null? tl)
                                  null
                                  (_adj tl)))]
                       
                       [(-> arg-type result-type)
                        (-> (_adj arg-type)
                            (_adj result-type))]
                       
                       [(type-var n)
                        (hash-ref subst t 
                                  (λ ()
                                    (let ([new-tvar (fresh-typevar-num)])
                                      (hash-set! subst t new-tvar)
                                      new-tvar)))]))])
      (_adj type))))

(define (adjust-type type)
  (match type
    [(cons 'ok t)
     (cons 'ok (adjust-tvar-num t))]
    
    [(cons 'error (cons exp
                        (cons t1 t2)))
     (cons 'error (cons exp
                        (cons (adjust-tvar-num t1)
                              (adjust-tvar-num t2))))]))



(define MUPL-Type-Inferencer-TESTS
  (test-suite "Tests For Extended MUPL Type Inferencer"
              (test-case "adjust-tvar-num"
                         (let ([t (-> (-> (type-var 1) 
                                          (-> (int-type)
                                              (ref-type (type-var 2))))
                                      (-> (-> (bool-type) 
                                              (type-var 3))
                                          (-> (type-var 1)
                                              (type-var 2))))])
                           (check-equal? t
                                         (adjust-tvar-num
                                          (-> (-> (type-var 34) 
                                                  (-> (int-type)
                                                      (ref-type (type-var 22))))
                                              (-> (-> (bool-type) 
                                                      (type-var 9))
                                                  (-> (type-var 34)
                                                      (type-var 22))))))
                           (check-equal? t
                                         (adjust-tvar-num
                                          (-> (-> (type-var 2) 
                                                  (-> (int-type)
                                                      (ref-type (type-var 5))))
                                              (-> (-> (bool-type) 
                                                      (type-var 55))
                                                  (-> (type-var 2)
                                                      (type-var 5)))))))
                         )
              
              (test-case "basic type"
                         (check-equal? (cons 'ok (int-type)) (type-of (int 1)))
                         (check-equal? (cons 'ok (bool-type)) (type-of (bool T)))
                         (check-equal? (cons 'ok (unit-type)) (type-of (aunit)))
                         )
              
              (test-case "isaunit"
                         (check-equal? (cons 'ok (bool-type)) (type-of (isaunit (aunit))))
                         (check-equal? (cons 'ok (bool-type)) (type-of (isaunit (int 1))))
                         (check-equal? (cons 'ok (bool-type)) (type-of (isaunit (isaunit (int 1)))))
                         )
              
              (test-case "ref"
                         (check-equal? (cons 'ok (ref-type (ref-type (bool-type))))
                                       (type-of (newref! (newref! (isaunit (isaunit (int 1)))))))
                         (check-equal? (cons 'ok (int-type))
                                       (type-of (deref (newref! (int 5)))))
                         (check-equal? (cons 'ok (unit-type))
                                       (type-of (setref! (newref! (bool T)) (bool F))))
                         (check-equal? (cons 'error (cons (setref! (newref! (bool T)) (deref (newref! (aunit))))
                                                          (cons (unit-type) (bool-type)))) ;; inconsistency
                                       (type-of (setref! (newref! (bool T)) (deref (newref! (aunit))))))
                         )
              
              (test-case "int-operator"
                         (check-equal? (cons 'ok (ref-type (int-type)))
                                       (type-of (newref! (add (int 3) (int 5)))))
                         (check-equal? (cons 'ok (ref-type (bool-type)))
                                       (type-of (newref! (isgreater (int 3) (int 5)))))
                         (check-equal? (cons 'ok (ref-type (bool-type)))
                                       (type-of (newref! (isless (int 3) (int 5)))))
                         (check-equal? (cons 'ok (ref-type (bool-type)))
                                       (type-of (newref! (isequal (int 3) (int 5)))))
                         (check-equal? (cons 'error (cons (add (newref! (int 3)) (int 2)) ;; inconsistency
                                                          (cons (ref-type (int-type)) (int-type))))
                                       (type-of (deref (newref! (add (newref! (int 3)) (int 2))))))
                         )
              
              (test-case "if-then-else"
                         (check-equal? (cons 'ok (int-type))
                                       (type-of (if-then-else (isaunit (deref (newref! (aunit))))
                                                              (int 2)
                                                              (int 4))))
                         (check-equal? (cons 'error (cons (if-then-else (deref (newref! (aunit)))
                                                                        (int 2)
                                                                        (int 4))
                                                          (cons (unit-type) (bool-type)))) ;; cond type != bool
                                       (type-of (if-then-else (deref (newref! (aunit)))
                                                              (int 2)
                                                              (int 4))))
                         (check-equal? (cons 'error (cons (if-then-else (isaunit (deref (newref! (aunit))))
                                                                        (bool T)
                                                                        (int 4))
                                                          (cons (bool-type) (int-type)))) ;; inconsistency
                                       (type-of (if-then-else (isaunit (deref (newref! (aunit))))
                                                              (bool T)
                                                              (int 4))))
                         )
              
              (test-case "seq"
                         (check-equal? (cons 'ok (bool-type))
                                       (type-of (seq (int 3)
                                                     (deref (newref! (aunit)))
                                                     (isaunit (deref (newref! (aunit)))))))
                         (check-equal? (cons 'error (cons (deref (int 3))
                                                          (cons (int-type) (ref-type (type-var 1)))))
                                       (adjust-type
                                        (type-of (seq (int 3)
                                                      (deref (int 3))
                                                      (isaunit (deref (newref! (aunit))))))))
                         )
              
              (test-case "def"
                         (check-equal? (cons 'error (cons (if-then-else (var "x")
                                                                        (int 1)
                                                                        (int 2))
                                                          (cons (int-type) (bool-type))))
                                       (type-of (seq (def "x" (add (int 1) (int 2)))
                                                     (if-then-else (var "x")
                                                                   (int 1)
                                                                   (int 2)))))
                         (check-equal? (cons 'ok (int-type))
                                       (type-of (seq (def "x" (deref (newref! (int 2))))
                                                     (add (var "x") (var "x")))))
                         )
              
              (test-case "fun"
                         (check-equal? (cons 'ok (-> (list (bool-type) (int-type))
                                                     (int-type)))
                                       (type-of (fun #f ("x" "y")
                                                     (if-then-else (var "x")
                                                                   (add (var "y")
                                                                        (int 1))
                                                                   (int 3)))))
                         (check-equal? (cons 'ok (-> (list (type-var 1))
                                                     (type-var 1)))
                                       (adjust-type (type-of (fun "self" ("f")
                                                                  (var "f")))))
                         (check-equal? (cons 'error (cons (if-then-else (var "x")
                                                                   (var "x")
                                                                   (add (int 1) (var "y")))
                                                          (cons (bool-type) (int-type))))
                                       (type-of (fun #f ("x" "y") ;; inconsistency
                                                     (if-then-else (var "x")
                                                                   (var "x")
                                                                   (add (int 1) (var "y"))))))
                         (check-equal? (cons 'error (cons (fun "rec-fun" () 
                                                               (var "rec-fun"))
                                                          (cons (type-var 1)
                                                                (-> (list (unit-type))
                                                                    (type-var 1)))))
                                       (adjust-type (type-of (fun "rec-fun" () ;; occurrence violation
                                                                  (var "rec-fun")))))
                         (check-equal? (cons 'ok (-> (list (int-type) (int-type))
                                                     (-> (list (unit-type))
                                                         (int-type))))
                                       (type-of (seq (def "f1" (fun #f ()
                                                                    (int 3)))
                                                     (fun #f ("x" "y")
                                                          (if-then-else (isless (var "x")
                                                                                (var "y"))
                                                                        (var "f1")
                                                                        (var "f1"))))))
                         )
              
              (test-case "call functions defined elsewhere"
                         (check-equal? (cons 'ok (-> (list (-> (list (int-type))
                                                               (int-type)))
                                                     (-> (list (int-type))
                                                         (int-type))))
                                       (type-of (seq (def "f1" (fun #f ("f")
                                                                    (var "f")))
                                                     (def "f2" (fun #f ("x")
                                                                    (add (var "x")
                                                                         (int 1))))
                                                     (def "f3" (fun #f ("f")
                                                                    (seq (call (var "f1")
                                                                               (var "f"))
                                                                         (var "f1"))))
                                                     (call (var "f3")
                                                           (var "f2")))))
                         (check-equal? (cons 'ok (int-type))
                                       (type-of (seq (def "f" (fun #f ("x" "y" "z")
                                                                   (if-then-else (var "x")
                                                                                 (add (var "y")
                                                                                      (var "z"))
                                                                                 (var "z"))))
                                                     (call (var "f")
                                                           (isaunit (aunit)) (int 1) (int 2)))))
                         (check-equal? (cons 'error (cons (call (var "f3")
                                                                (var "f2"))
                                                          (cons (int-type)
                                                                (-> (list (int-type))
                                                                    (int-type)))))
                                       (type-of (seq (def "f1" (fun #f ("f")
                                                                    (var "f")))
                                                     (def "f2" (fun #f ("x")
                                                                    (add (var "x")
                                                                         (int 1))))
                                                     (def "f" (int 3))
                                                     (def "f3" (fun #f ("f") ;; infer: f3: int->int
                                                                    (seq (call (var "f1")
                                                                               (var "f"))
                                                                         (call (var "f1") ;; infer: f1 : int->int, f: int
                                                                               (int 1)))))
                                                     (call (var "f3") ;; args types inconsistency
                                                           (var "f2")))))
                         )
              ))

(run-tests MUPL-Type-Inferencer-TESTS)