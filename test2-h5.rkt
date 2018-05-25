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
    
    (expression("-" "(" expression "," expression ")")diff-exp)
    
    (expression ("zero?" "(" expression ")") zero?-exp)
    
    (expression
     ("if" expression "then" expression "else" expression) if-exp)
    
    (expression (identifier) var-exp)
    
    (expression 
     ("let" identifier "=" expression "in" expression) let-exp)
    
    (expression
     ("letrec" identifier "(" identifier ")" "=" expression 
               "in" expression) letrec-exp)
    
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    
    (expression ("(" expression expression ")") call-exp)
    
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
   (bvar symbol?)
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
      (extend-env-rec (p-name b-var p-body saved-env)
                      (if (eqv? search-sym p-name)
                          (proc-val (procedure b-var p-body env))          
                          (apply-env saved-env search-sym)))))



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
   (proc proc?)))

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

(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
                variant value)))


;;;;;;;;;;;;;;;; procedures ;;;;;;;;;;;;;;;;

;; proc? : SchemeVal -> Bool
;; procedure : Var * Exp * Env -> Proc
(define-datatype proc proc?
  (procedure
   (var symbol?)
   (body expression?)
   (env environment?)))

;; occurs-free-v :
;; occurs-free-v : list-of-symbol expression -> list-of-symbol
(define (occurs-free-v bound body)
  (cases expression body
    (const-exp (num) '())
    (var-exp (id) (if
                   (member id bound)
                   '()
                   (list id)))
    (diff-exp (exp1 exp2) (append (occurs-free-v bound exp1) (occurs-free-v bound exp2)))
    (zero?-exp (exp) (occurs-free-v bound exp))
    (if-exp (exp1 exp2 exp3) (append (occurs-free-v bound exp1) (occurs-free-v bound exp2) (occurs-free-v bound exp3)))
    (let-exp (id exp1 exp2)
             (append (occurs-free-v (cons id bound) exp1) (occurs-free-v (cons id bound) exp2)))
    (letrec-exp (id1 id2 exp1 exp2)
                (append (occurs-free-v (cons id1 (cons id2 bound)) exp1) (occurs-free-v (cons id1 bound) exp2)))
    (proc-exp (id exp)
              (occurs-free-v (cons id bound) exp))
    (call-exp (exp1 exp2) (append (occurs-free-v bound exp1) (occurs-free-v bound exp2)))))


;; test-occurs-free-v : program -> 
;; Purpose : to take in a program containing an expression and call occurs free so that it can be scanned and parsed
(define (test-occurs-free-v prog)
  (cases program prog
    (a-program (prog)
               (occurs-free-v '() prog))))

;;scan&parse-occurs : program -> list
;; Purpose : scans and parses the program inside of test-occurs-free
(define (scan&parse-occurs prog)
  (test-occurs-free-v (scan&parse prog)))

;;free-env: list-of-symbols environment -> environment

(define (free-env var env)
  (let ((fvars (occurs-free-v var env)))
    (cond [(null? fvars) empty-env]
          [else (extend-env (car fvars) (apply-env (car fvars) env) (free-env (cdr fvars) env))])))


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
    
    (if-exp (exp1 exp2 exp3)
            (let ((val1 (value-of exp1 env)))
              (if (expval->bool val1)
                  (value-of exp2 env)
                  (value-of exp3 env))))
    
    (let-exp (var exp1 body)       
             (let ((val1 (value-of exp1 env)))
               (value-of body
                         (extend-env var val1 env))))
    
    (letrec-exp (p-name param p-body letrec-body)
                (value-of letrec-body (extend-env-rec p-name
                                                      param
                                                      p-body
                                                      env)))
    
    (proc-exp (var body)
              (proc-val (procedure var body env)))
    
    (call-exp (rator rand)
              (let ((proc (expval->proc (value-of rator env)))
                    (arg (value-of rand env)))
                (apply-procedure proc arg)))
    
    
    ))

;; apply-procedure : Proc * ExpVal -> ExpVal
(define (apply-procedure proc1 val)
  (cases proc proc1
    (procedure (var body saved-env)
               (value-of body (extend-env var val (free-env var saved-env))))))

;;;;;;   EVALUATION WRAPPERS

;; parse: String -> a-program
(define (parse p) (scan&parse p))

;; eval : String -> ExpVal
(define (eval string)
  (value-of-program (parse string)))

;;;;; EXAMPLES OF EVALUATION

(check-expect (scan&parse-occurs "5") '())
(check-expect (scan&parse-occurs "(x c)") '(x c))
(check-expect (scan&parse-occurs "proc (x) -(x, 5)") '())
(check-expect (scan&parse-occurs "proc (x) -(x, p)") '(p))
(check-expect (scan&parse-occurs "let x = 200 
         in let f = proc (z) -(z, x) 
              in let x = 100 
                   in let g = proc (z) -(z, x) 
                        in -((f 1), (g 1))") '())
(check-expect (scan&parse-occurs "letrec fact(n) = if zero?(n)then 1 else -(n, (fact -(n, 1))) in (fact 5)") '())

(test)
