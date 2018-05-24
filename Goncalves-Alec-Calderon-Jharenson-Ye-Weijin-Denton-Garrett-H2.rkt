#lang eopl

(require test-engine/racket-tests)
;;;;;;;;;;;;;;;; grammatical specification ;;;;;;;;;;;;;;;;

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    
    (comment ("%" (arbno (not #\newline))) skip)
    
    (identifier
     (letter (arbno (or letter digit "_" "-" "?"))) symbol)
    
    (number (digit (arbno digit)) number)
    
    (number ("-" digit (arbno digit)) number)
    ))

(define the-grammar
  '((program (expression) a-program)
    
    (expression (number) const-exp)
    
    (expression("sub" "(" expression"," expression ")")diff-exp)
    
    (expression ("zero?" "(" expression ")") zero?-exp)

    (expression ("equal?" "(" expression"," expression ")") equal?-exp)

    (expression ("greater?" "(" expression"," expression ")") greater?-exp)

    (expression ("less?" "(" expression"," expression ")") less?-exp)
    
    (expression
     ("if" expression "then" expression "else" expression) if-exp)
    
    (expression (identifier) var-exp)

    (expression ("minus" "(" expression ")") minus-exp)

    (expression ("add" "(" expression"," expression ")") add-exp)

    (expression ("mult" "(" expression"," expression ")") mult-exp)

    (expression ("div" "(" expression"," expression ")") div-exp)
    
    (expression 
     ("let" identifier "=" expression "in" expression) let-exp)
    
    (expression
     ("letrec" identifier "(" (arbno identifier) ")" "=" expression 
               "in" expression) letrec-exp)
    
    (expression ("proc" "(" (separated-list identifier ",") ")" expression) proc-exp)
    
    (expression ("(" expression (arbno expression) ")") call-exp)

    (expression ("mt-list" "(" ")") mt-list-exp)

    (expression ("list" "(" (separated-list expression ",") ")") list-exp)

    (expression ("cons" "(" expression "," expression ")") cons-exp)

    (expression ("car" "(" expression ")") car-exp)

    (expression ("cdr" "(" expression ")") cdr-exp)

    (expression ("null?" "(" expression ")") null?-exp)

    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

;;;;;    ENVIRONMENT

(define-datatype environment environment?
  (empty-env)
  (extend-env 
   (bvar symbol?)
   (bval expval?)
   (saved-env environment?))
  (extend-env-rec
   (id symbol?)
   (bvars (list-of symbol?))
   (body expression?)
   (saved-env environment?)))

(define (apply-env env search-sym)
  (cases environment env
    (empty-env ()
               (eopl:error 'apply-env "No binding for ~s" search-sym))
    (extend-env (var val saved-env)
                (if (eqv? search-sym var)
                    val
                    (apply-env saved-env search-sym)))
    (extend-env-rec (p-name b-vars p-body saved-env)
                    (if (eqv? search-sym p-name)
                        (proc-val (procedure b-vars p-body env))          
                        (apply-env saved-env search-sym)))))

;Purpose: to extend the env with multiple bindings
;extend-env* : symbols exp-vals env -> env
;Assumtion: length of vars and vals is equal
(define (extend-env* vars vals env)
  (cond [(null? vars) env]
        [else (extend-env (car vars) (car vals) (extend-env* (cdr vars) (cdr vals) env))]))

(define (init-env)
  (extend-env 
   'i (num-val 1)
   (extend-env
    'v (num-val 5)
    (extend-env
     'x (num-val 10)
     (empty-env)))))

;;;;;;;;;;;;;;;; expressed values ;;;;;;;;;;;;;;;;

;;; an expressed value is either a number, a boolean or a procval.

(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val 
   (proc proc?))
  (mt-list-val )
  (cons-val 
   (car expval?)
   (cdr expval?)))

;;; extractors:

;; expval->num : ExpVal -> Int
(define expval->num
  (lambda (v)
    (cases expval v
      (num-val (num) num)
      (else (expval-extractor-error 'num v)))))

;; expval->bool : ExpVal -> Bool
(define expval->bool
  (lambda (v)
    (cases expval v
      (bool-val (bool) bool)
      (else (expval-extractor-error 'bool v)))))

;; expval->proc : ExpVal -> Proc
(define expval->proc
  (lambda (v)
    (cases expval v
      (proc-val (proc) proc)
      (else (expval-extractor-error 'proc v)))))

;; expval->car : ExpVal -> ExpVal
(define expval->car
  (lambda (v)
    (cases expval v
      (cons-val (car cdr) car)
      (else (expval-extractor-error 'car v)))))

;;expval->cdr : ExpVal -> ExpVal
(define expval->cdr
  (lambda (v)
    (cases expval v
      (cons-val (car cdr) cdr)
      (else (expval-extractor-error 'cdr v)))))

;;expval->null?: ExpVal-> boolean
(define expval->null?
  (lambda (v)
    (cases expval v
      (mt-list-val() #t)
      (cons-val (car cdr) #f)
      (else (expval-extractor-error 'mt-list-or-cons v)))))


(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
                variant value)))


;;;;;;;;;;;;;;;; procedures ;;;;;;;;;;;;;;;;

;; proc? : SchemeVal -> Bool
;; procedure : Vars * Exp * Env -> Proc
(define-datatype proc proc?
  (procedure
   (vars (list-of symbol?))
   (body expression?)
   (env environment?)))


;;;;;;;;;;;;;;;; the interpreter ;;;;;;;;;;;;;;;;

;; value-of-program : Program -> ExpVal
(define (value-of-program pgm)
  (cases program pgm
    (a-program (exp1)
               (value-of exp1 (init-env)))))

;; value-of : Exp * Env -> ExpVal
(define (value-of exp env)
  (cases expression exp
    
    (const-exp (num) (num-val num))
    
    (var-exp (var) (apply-env env var))
    
    (diff-exp (exp1 exp2)
              (let ((val1 (value-of exp1 env))
                    (val2 (value-of exp2 env)))
                (let ((num1 (expval->num val1))
                      (num2 (expval->num val2)))
                  (num-val (- num1 num2)))))
    
    (zero?-exp (exp1)
               (let ((val1 (value-of exp1 env)))
                 (let ((num1 (expval->num val1)))
                   (if (zero? num1)
                       (bool-val #t)
                       (bool-val #f)))))
    (equal?-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env)))
                  (let ((val2 (value-of exp2 env)))
                    (let ((num1 (expval->num val1)))
                      (let ((num2 (expval->num val2)))
                        (if (equal? num1 num2)
                            (bool-val #t)
                            (bool-val #f)))))))
    (greater?-exp (exp1 exp2)
                  (let ((val1 (value-of exp1 env)))
                    (let ((val2 (value-of exp2 env)))
                      (let ((num1 (expval->num val1)))
                        (let ((num2 (expval->num val2)))
                          (if (> num1 num2)
                              (bool-val #t)
                              (bool-val #f)))))))
    (less?-exp (exp1 exp2)
               (let ((val1 (value-of exp1 env)))
                 (let ((val2 (value-of exp2 env)))
                   (let ((num1 (expval->num val1)))
                     (let ((num2 (expval->num val2)))
                       (if (< num1 num2)
                           (bool-val #t)
                           (bool-val #f)))))))
    
    (add-exp (exp1 exp2)
             (let ((val1 (value-of exp1 env))
                   (val2 (value-of exp2 env)))
               (let ((num1 (expval->num val1))
                     (num2 (expval->num val2)))
                 (num-val (+ num1 num2)))))
    (mult-exp (exp1 exp2)
              (let ((val1 (value-of exp1 env))
                    (val2 (value-of exp2 env)))
                (let ((num1 (expval->num val1))
                      (num2 (expval->num val2)))
                  (num-val (* num1 num2)))))
    (div-exp (exp1 exp2)
             (let ((val1 (value-of exp1 env))
                   (val2 (value-of exp2 env)))
               (let ((num1 (expval->num val1))
                     (num2 (expval->num val2)))
                 (num-val (quotient num1 num2)))))

    (minus-exp (exp1)
               (let((val1 (value-of exp1 env)))
                 (let((num1 (expval->num val1)))
                   (num-val (- 0 num1)))))
    
    (if-exp (exp1 exp2 exp3)
            (let ((val1 (value-of exp1 env)))
              (if (expval->bool val1)
                  (value-of exp2 env)
                  (value-of exp3 env))))
    
    (let-exp (var exp1 body)       
             (let ((val1 (value-of exp1 env)))
               (value-of body
                         (extend-env var val1 env))))
    
    (letrec-exp (p-name params p-body letrec-body)
                (value-of letrec-body (extend-env-rec p-name
                                                      params
                                                      p-body
                                                      env)))
    
    (proc-exp (vars body)
              (proc-val (procedure vars body env)))
    
    (call-exp (rator rands)
              (let ((proc (expval->proc (value-of rator env)))
                    (args (map (lambda (rand) (value-of rand env)) rands)))
                (apply-procedure proc args)))
    
    (mt-list-exp() (mt-list-val))
    
    (list-exp (expressions)
              (cons-val (map
                         (lambda (expression) (value-of expression env))
                         expressions)))
    
    (cons-exp (exp1 exp2)
              (let ((var1 (value-of exp1 env))
                    (var2 (value-of exp2 env)))
                (cons-val var1 var2)))
    
    (car-exp (exp1)
             (expval->car (value-of exp1 env)))
    
    (cdr-exp (exp1)
             (expval->cdr (value-of exp1 env)))
    
    (null?-exp (exp1)
               (let ((var1 (expval->null? (value-of exp1 env))))
                 (bool-val var1)))

    ))

;; apply-procedure : Proc * ExpVals -> ExpVal
(define (apply-procedure proc1 vals)
  (cases proc proc1
    (procedure (vars body saved-env)
               (value-of body (extend-env* vars vals saved-env)))))

;;;;;;   EVALUATION WRAPPERS

;; parse: String -> a-program
(define (parse p) (scan&parse p))

;; eval : String -> ExpVal
(define (eval string)
  (value-of-program (parse string)))

;;;;; EXAMPLES OF EVALUATION


(check-expect (eval "if zero?(1) then 1 else 2") (num-val 2))
(check-expect (eval "sub(x, v)")(num-val 5))
(check-expect (eval "if zero?(sub(x, x)) then x else 2") (num-val 10))
(check-expect (eval "if zero?(sub(x, v)) then x else 2") (num-val 2))
(check-expect (eval "let decr = proc (a) sub(a, 1) in (decr 30)") (num-val 29))
(check-expect (eval "( proc (g) (g 30) proc (y) sub(y, 1))") (num-val 29))
(check-expect (eval "let x = 200 
         in let f = proc (z) sub(z, x) 
              in let x = 100 
                   in let g = proc (z) sub(z, x) 
                        in sub((f 1), (g 1))") (num-val -100))
(check-expect (eval "let sum = proc (x) proc (y) sub(x, sub(0, y)) in ((sum 3) 4)") (num-val 7))
(check-expect (eval "let x = 200 
         in let f = proc (z) sub(z, x) 
              in let x = 100 
                   in let g = proc (z) sub(z, x) 
                        in sub((f 1), (g 1))") (num-val -100))
(check-expect (eval "let f = proc (y, z) if zero? (z) then y else sub(sub(y, -1), sub(z, 1)) in (f 5 5)") (num-val 2))
(check-expect (eval "let f = proc (y, z, w) if equal?(y, z) then w else sub(add(y, 1), sub(z, 1)) in (f 5 5 3)") (num-val 3))
(check-expect (eval "let f = proc (y, z, w) if equal?(y, z) then w else sub(add(y, 1), sub(z, 1)) in (f 7 5 3)") (num-val 4))
(check-expect (eval "car(cons(3, mt-list()))") (num-val 3))
(check-expect (eval "cdr(cons(1, cons(3, mt-list())))") (cons-val (num-val 3) (mt-list-val)))
(check-expect (eval "null?(mt-list())") (bool-val #t))
(check-expect (eval "null?(cons(1, mt-list()))") (bool-val #f))

(test)
 