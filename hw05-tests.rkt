#lang racket

(require rackunit "hw05.rkt")
(require rackunit/text-ui)

(define MUPL-TESTS
  (test-suite "Tests For Extended MUPL Interpreter"
              (test-case "racketlist->mupllist"
                         (check-equal?
                          (apair (int 3) (apair (int 4) (apair (int 9) (aunit))))
                          (racketlist->mupllist (list (int 3) (int 4) (int 9)))
                          )

                         (check-equal?
                          (apair (apair (int 3)
                                        (apair (int 4)
                                               (apair (apair (int 5) (apair (int 9) (aunit)))
                                                      (aunit))))
                                 (apair (int 6)
                                        (apair (apair (int 0)
                                                      (apair (apair (int 2)
                                                                    (apair (apair (int 3) (apair (int 8) (aunit)))
                                                                           (aunit)))
                                                             (aunit)))
                                               (aunit)
                                               )
                                        )
                                 )
                          (racketlist->mupllist (list (list (int 3) (int 4) (list (int 5) (int 9)))
                                                      (int 6)
                                                      (list (int 0) (list (int 2) (list (int 3) (int 8))))))
                          )
                         )

              (test-case "mupllist->racketlist"
                         (let ( (racklist (list (list (int 3) (int 4) (list (int 5) (int 9)))
                                                (int 6)
                                                (list (int 0) (list (int 2) (list (int 3) (int 8))))))
                                 )
                           (check-equal? racklist
                                         (mupllist->racketlist (racketlist->mupllist racklist)))
                           )
                         )

              (test-case "alist"
                         (check-equal?
                          (alist (alist (int 3) (int 4) (alist (int 5) (int 9)))
                                 (int 6)
                                 (alist (int 0) (alist (int 2) (alist (int 3) (int 8)))))
                          (racketlist->mupllist (list (list (int 3) (int 4) (list (int 5) (int 9)))
                                                      (int 6)
                                                      (list (int 0) (list (int 2) (list (int 3) (int 8)))))
                                                ))
                         )

              (test-case "envlookup"
                         (let ([ht1 (hash "v1" (int 1) "v2" (int 2))]
                               [ht2 (hash "v3" (int 3) "v4" (int 4))])                      
                           (let ([env (list ht1 ht2)])
                             (check-equal? (int 1) (envlookup env "v1"))
                             (check-equal? (int 4) (envlookup env "v4"))
                             )
                         )
              )

              (test-case "modify-env"
                         (let ([ht1 (make-hash)]
                               [ht2 (make-hash)])                      
                           (begin
                             (hash-set! ht1 "v1" (int 1))
                             (hash-set! ht1 "v2" (int 2))
                             (hash-set! ht2 "v3" (int 3))
                             (hash-set! ht2 "v4" (int 4))
                             (let ([env (list ht1 ht2)])
                               (begin
                                 (modify-env env "v2" (int 8))
                                 (modify-env env "v3" (int 10))
                                 (check-equal? (int 8) (envlookup env "v2"))
                                 (check-equal? (int 10) (envlookup env "v3")))
                               ))
                           )
                         )

              (test-case "eval on values"
                         (check-equal? (int 4) (eval-exp (int 4)))
                         (check-equal? (aunit) (eval-exp (aunit)))
                         (check-equal? (alist (int 4) (int 5)) (eval-exp (alist (int 4) (int 5))))
                         (check-equal? (alist (int 4) (eval-exp (fun "A" ("k") (apair (var "k") (aunit)))))
                                       (eval-exp (alist (int 4) (fun "A" ("k") (alist (var "k") )))))
                         )

              (test-case "add"
                         (check-equal? (int 5) (eval-exp (add (int 1) (int 4))))
                         )

              (test-case "ifgreater"
                         (let ([e1 (add (int 2) (int 3))]
                               [e2 (int 8)]
                               [e3 (fun "A" ("k") (aunit))]
                               [e4 (add (int 4) (int 5))])
                           (check-equal? (int 9) (eval-exp (ifgreater e1 e2 e3 e4)))
                           (check-equal? (eval-exp e3) (eval-exp (ifgreater e2 e1 e3 e4)))
                             )
                         )

              (test-case "fst && snd"
                         (let* ([list1 (alist (int 1) (int 2))]
                                [e (apair (int 4) list1)])
                           (check-equal? (int 4) (eval-exp (fst e)))
                           (check-equal? (int 1) (eval-exp (fst (snd e))))
                           )
                         )

              (test-case "isaunit"
                         (let ([p (apair (int 4) (aunit))])
                           (check-equal? (int 1) (eval-exp (isaunit (snd p))))
                           (check-equal? (int 0) (eval-exp (isaunit (fst p)))))
                         )

              (test-case "function call"
                         (check-equal? (int 7) ;; basic
                                       (eval-exp (call (fun "test" ("x") (add (var "x") (int 3)))
                                                       (int 4))))
                         (check-equal? (int 10) ;; test lexical binding
                                       (eval-exp
                                        (call (fun "test" ("y")  ;; λy.(λx.(λy.x+y 3) y) 7
                                                   (call (fun "tmp1" ("x")
                                                              (call (fun "tmp2" ("y")
                                                                         (add (var "x") (var "y")))
                                                                    (int 3)))
                                                         (var "y")))
                                              (int 7))))
                         (check-equal? (int 5) ;; test recursive
                                       (eval-exp
                                        (call (fun "find-fst-greater-than-3" ("list")
                                                   (ifgreater (fst (var "list")) (int 3)
                                                              (fst (var "list"))
                                                              (call (var "find-fst-greater-than-3")
                                                                    (snd (var "list")))))
                                              (alist (int 1) (int 2) (int 3) (int 2) (int 5) (int 4)))))
                         (check-equal? (int 5) ;; fn without args
                                       (eval-exp (call (fun #f () (int 5)))))
                         (check-equal? (int 6) ;; fn with multi-parameter
                                       (eval-exp (call (fun #f ("v1" "v2" "v3")
                                                            (add (var "v1") (add (var "v2") (var "v3"))))
                                                       (int 1) (int 2) (int 3))))
                         )

              (test-case "mlet"
                         (check-equal? (int 8) ;; basic
                                       (eval-exp (mlet (["k" (int 7)])
                                                       (add (int 1) (var "k")))))
                         (check-equal? (int 10) ;; test recursive
                                       (eval-exp (mlet (["sum-seq" (fun "sum-seq" ("n") ;; sum-seq = λn.0+1+...+n
                                                                      (ifgreater (var "n") (int 0)
                                                                                 (add (var "n")
                                                                                      (call (var "sum-seq")
                                                                                            (add (int -1) (var "n"))))
                                                                                 (var "n")))])
                                                       (call (var "sum-seq") (int 4)))))
                         (check-equal? (int 3) ;; mlet without args
                                       (eval-exp (mlet () (add (int 1) (int 2)))))
                         (check-equal? (int 6) ;; mlet with multi-arg
                                       (eval-exp (mlet (["v1" (int 1)]
                                                        ["v2" (int 2)]
                                                        ["v3" (int 3)])
                                                       (add (var "v1") (add (var "v2") (var "v3"))))))
                         )

              (test-case "named-mlet"
                         (check-equal? (int 8)
                                       (eval-exp (call (fun #f ("n")
                                                            (mlet "fib-iter" (["a" (int 1)]
                                                                              ["b" (int 0)]
                                                                              ["count" (var "n")])
                                                                  (ifgreater (var "count") (int 0)
                                                                             (call (var "fib-iter")
                                                                                   (add (var "a") (var "b"))
                                                                                   (var "a") (add (var "count") (int -1)))
                                                                             (var "b"))))
                                                       (int 6)))))

              (test-case "mlet*"
                         (check-equal? (int 3) ;; mlet* with no args
                                       (eval-exp (mlet* () (add (int 1) (int 2)))))
                         (check-equal? (int 10) ;; mlet* with multi-args
                                       (eval-exp (mlet* (["v1" (int 1)]
                                                         ["v2" (add (var "v1") (int 2))]
                                                         ["v3" (add (var "v2") (int 3))])
                                                        (add (add (var "v1") (var "v2"))
                                                             (var "v3")))))
                         )

              (test-case "mletrec"
                         (check-equal? (int 0)
                                       (eval-exp (call (fun #f ("x")
                                                            (mletrec (["even?" (fun #f ("n")
                                                                                    (ifgreater (var "n") (int 0)                                                                                               
                                                                                               (call (var "odd?")
                                                                                                     (add (var "n") (int -1)))
                                                                                               (int 1)))]
                                                                      ["odd?" (fun #f ("n")
                                                                                   (ifgreater (var "n") (int 0)
                                                                                              (call (var "even?")
                                                                                                    (add (var "n") (int -1)))
                                                                                              (int 0)))])
                                                                     (call (var "odd?") (var "x"))))
                                                       (int 8)))))

              (test-case "ifaunit"
                         (check-equal? (int 0)
                                       (eval-exp (ifaunit (snd (apair (int 3) (aunit)))
                                                          (call (fun #f () (int 0)) (aunit))
                                                          (call (fun #f () (int 1)) (aunit)))))
                         (check-equal? (int 1)
                                       (eval-exp (ifaunit (fst (apair (int 3) (aunit)))
                                                          (call (fun #f () (int 0)) (aunit))
                                                          (call (fun #f () (int 1)) (aunit)))))
                         )
              )
  )
  

(run-tests MUPL-TESTS)