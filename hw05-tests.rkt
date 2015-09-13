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

              (test-case "eval on value"
                         (check-equal? (int 4) (eval-exp (int 4)))
                         (check-equal? (aunit) (eval-exp (aunit)))
                         (check-equal? (alist (int 4) (int 5)) (eval-exp (alist (int 4) (int 5))))
                         (check-equal? (alist (int 4) (eval-exp (fun "A" "k" (apair (var "k") (aunit)))))
                                       (eval-exp (alist (int 4) (fun "A" "k" (alist (var "k") )))))
                         )
              )
  )
  

(run-tests MUPL-TESTS)