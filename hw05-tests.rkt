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
                          (apair (apair 3
                                        (apair 4
                                               (apair (apair 5 (apair 9 (aunit)))
                                                      (aunit))))
                                 (apair 6
                                        (apair (apair 0
                                                      (apair (apair 2
                                                                    (apair (apair 3 (apair 8 (aunit)))
                                                                           (aunit)))
                                                             (aunit)))
                                               (aunit)
                                               )
                                        )
                                 )
                          (racketlist->mupllist (list (list 3 4 (list 5 9))
                                                      6
                                                      (list 0 (list 2 (list 3 8)))))
                          )
                         )

              (test-case "mupllist->racketlist"
                         (let ( (racklist (list (list 3 4 (list 5 9))
                                                6
                                                (list 0 (list 2 (list 3 8)))))
                                 )
                           (check-equal? racklist
                                         (mupllist->racketlist (racketlist->mupllist racklist)))
                           )
                         )
              )
  )
  

(run-tests MUPL-TESTS)