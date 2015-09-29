#lang racket

(require rackunit "main.rkt" "ast-struct.rkt" "type-struct.rkt")
(require rackunit/text-ui)

(define MUPL-Type-Inferencer-TESTS
  (test-suite "Tests For Extended MUPL Evaluator"
              (test-case "basic type"
                         (check-equal? (int-type) (type-of (int 1)))
                         (check-equal? (bool-type) (type-of (bool T)))
                         )
              ))

(run-tests MUPL-Type-Inferencer-TESTS)