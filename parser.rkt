#lang racket
(require rackunit "ast-struct.rkt")
(require compatibility/mlist)

(struct success (val rest) #:transparent)
(struct failure (rest) #:transparent)

(define (succeed val)
  (λ (str)
    (success val str)))

(define (string match)
  (λ (str)
    (let* ((len (min (string-length str) (string-length match)))
           (head (substring str 0 len))
           (tail (substring str len)))
      (if (equal? match head)
          (success match tail)
          (failure str)))))

(define (memo fn)
  (let ((reslist (mlist)))
    (λ args
      (match (massoc args reslist)
        [(mcons args result) result]
        [_ (let* ((result (apply fn args))
                  (entry (mcons args result)))
             (set! reslist (mcons entry reslist))
             result)]))))

(define (bind parser fn)
  (λ (str)
    (match (parser str)
      [(success val rest) ((fn val) rest)]
      [failure failure])))

(define alt
  (memo
   (lambda (left right)
     (memo
      (λ (str)
        (let ((lres (left str)))
          (match lres
            [(success val rest) lres]
            [failure (right str)])))))))

(define seq
  (memo
   (lambda (first last)
     (memo
      (bind first
            (λ (x) (bind last
                         (λ (y) (succeed (list x y))))))))))


(define-syntax-rule (delay-parser parser)
  (lambda args (apply parser args)))

(define-syntax-rule (define-parser parser body)
  (define parser (delay-parser body)))