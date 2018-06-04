#lang eopl

(require test-engine/racket-tests)

;Globally defined "registers"
(define nr 'uninitialized)
(define ar 'uninitialized)

;Purpose: takes in an integer and returns the factorial of that integer
;fact-iter: integer -> integer
(define fact-iter
(lambda (n)
    (set! nr n)
    (set! ar 1)
    (fact-iter-acc)))

;Purpose: helper to fact-iter to recursively subtract and multiply
         ;number and accum until factorial is returned
;fact-iter-acc: -> integer
(define (fact-iter-acc)
    (if (zero? nr) ar
        (begin
          (set! ar (* nr ar))
          (set! nr (- nr 1))
          (fact-iter-acc))))

(check-expect (fact-iter 0) 1)
(check-expect (fact-iter 1) 1)
(check-expect (fact-iter 2) 2)
(check-expect (fact-iter 3) 6)
(check-expect (fact-iter 4) 24)
(check-expect (fact-iter 5) 120)
(check-expect (fact-iter 10) 3628800)
(check-expect (fact-iter 20) 2432902008176640000)

(test)
