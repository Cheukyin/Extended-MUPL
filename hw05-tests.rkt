#lang racket

(require rackunit "hw05.rkt")
(require rackunit/text-ui)

; a test case that uses problems 1, 2, and 4
; should produce (list (int 10) (int 11) (int 16))
;(define test1
;  (mupllist->racketlist
;   (eval-exp (call (call mupl-mapAddN (int 7))
;                   (racketlist->mupllist 
;                    (list (int 3) (int 4) (int 9)))))))

(define MUPL-TESTS
  (test-suite "Tests For MUPL Interpreter"
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

              (test-case "eval on values"
                         (check-equal? (int 4) (eval-exp (int 4)))
                         (check-equal? (aunit) (eval-exp (aunit)))
                         (check-equal? (alist (int 4) (int 5)) (eval-exp (alist (int 4) (int 5))))
                         (check-equal? (alist (int 4) (eval-exp (fun "A" "k" (apair (var "k") (aunit)))))
                                       (eval-exp (alist (int 4) (fun "A" "k" (alist (var "k") )))))
                         )

              (test-case "add"
                         (check-equal? (int 5) (eval-exp (add (int 1) (int 4))))
                         )

              (test-case "ifgreater"
                         (let ([e1 (add (int 2) (int 3))]
                               [e2 (int 8)]
                               [e3 (fun "A" "k" (aunit))]
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
                                       (eval-exp (call (fun "test" "x" (add (var "x") (int 3)))
                                                       (int 4))))
                         (check-equal? (int 10) ;; test lexical binding
                                       (eval-exp
                                        (call (fun "test" "y"  ;; λy.(λx.(λy.x+y 3) y) 7
                                                   (call (fun "tmp1" "x"
                                                              (call (fun "tmp2" "y"
                                                                         (add (var "x") (var "y")))
                                                                    (int 3)))
                                                         (var "y")))
                                              (int 7))))
                         (check-equal? (int 5) ;; test recursive
                                       (eval-exp
                                        (call (fun "find-fst-greater-than-3" "list"
                                                   (ifgreater (fst (var "list")) (int 3)
                                                              (fst (var "list"))
                                                              (call (var "find-fst-greater-than-3")
                                                                    (snd (var "list")))))
                                              (alist (int 1) (int 2) (int 3) (int 2) (int 5) (int 4)))))
                         )

              (test-case "mlet"
                         (check-equal? (int 8) ;; basic
                                       (eval-exp (mlet "k" (int 7)
                                                       (add (int 1) (var "k")))))
                         (check-equal? (int 10) ;; test recursive
                                       (eval-exp (mlet "sum-seq" (fun "sum-seq" "n" ;; sum-seq = λn.0+1+...+n
                                                                      (ifgreater (var "n") (int 0)
                                                                                 (add (var "n")
                                                                                      (call (var "sum-seq")
                                                                                            (add (int -1) (var "n"))))
                                                                                 (var "n")))
                                                       (call (var "sum-seq") (int 4)))))
                         )

              (test-case "ifaunit"
                         (check-equal? (int 0)
                                       (eval-exp (ifaunit (snd (apair (int 3) (aunit)))
                                                          (call (fun #f "" (int 0)) (aunit))
                                                          (call (fun #f "" (int 1)) (aunit)))))
                         (check-equal? (int 1)
                                       (eval-exp (ifaunit (fst (apair (int 3) (aunit)))
                                                          (call (fun #f "" (int 0)) (aunit))
                                                          (call (fun #f "" (int 1)) (aunit)))))
                         )

              (test-case "mlet*"
                         (check-equal? (int 10)
                                       (eval-exp (mlet* (["v1" (int 1)]
                                                         ["v2" (add (var "v1") (int 2))]
                                                         ["v3" (add (var "v2") (int 3))])
                                                        (add (add (var "v1") (var "v2"))
                                                             (var "v3"))))))
              )
  )
  

(run-tests MUPL-TESTS)