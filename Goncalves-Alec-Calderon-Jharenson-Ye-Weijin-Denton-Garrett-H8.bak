#lang eopl

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

    (expression("+" "(" expression "," expression ")")sum-exp)
    
    (expression("*" "(" expression "," expression ")") mult-exp)
    
    (expression ("zero?" "(" expression ")") zero?-exp)
    
    (expression
     ("if" expression "then" expression "else" expression) if-exp)
    
    (expression (identifier) var-exp)
    
    (expression 
     ("let" (arbno identifier "=" expression) "in" expression) let-exp)
    
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

(define identifier? symbol?)

(define-datatype environment environment?
  (empty-env)
  (extend-env 
   (bvar identifier?)
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


;;;;;;;;;;;;;;;; continutations ;;;;;;;;;;;;;;;;
(define-datatype continuation continuation?
  (end-cont)
  (zero1-cont (cont continuation?))
  (let-exp-cont
   (vars (list-of symbol?))
   (exps (list-of expression?))
   (body expression?)
   (env environment?)
   (cont continuation?))
  (if-test-cont
   (exp2 expression?)
   (exp3 expression?)
   (env environment?)
   (cont continuation?))
  (diff1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?))
  (diff2-cont
   (val1 expval?)
   (cont continuation?))
  (sum1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?))
  (sum2-cont
   (val1 expval?)
   (cont continuation?))
  (rator-cont (rand expression?)
              (env environment?)
              (cont continuation?))
  (rand-cont (rator-val expval?)
             (cont continuation?))
  (mult1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?))
  (mult2-cont
   (val1 expval?)
   (cont continuation?))
  )


;;;;;;;;;;;;;;;; the interpreter ;;;;;;;;;;;;;;;;

;; value-of-program : Program -> ExpVal
(define (value-of-program pgm)
  (cases program pgm
    (a-program (exp1)
               (value-of/k exp1 (init-env) (end-cont)))))

;; value-of : Exp Env Cont -> FinalAnswer
(define (value-of/k exp env cont)
  (cases expression exp
    
    (const-exp (num) (apply-cont cont (num-val num)))
    
    (var-exp (var) (apply-cont cont (apply-env env var)))
    
    (diff-exp (exp1 exp2)
              (value-of/k exp1 env (diff1-cont exp2 env cont)))

    (sum-exp (exp1 exp2)
              (value-of/k exp1 env (sum1-cont exp2 env cont)))
    
    (mult-exp (exp1 exp2)
              (value-of/k exp1 env (mult1-cont exp2 env cont)))
    
    (zero?-exp (exp1)
               (value-of/k exp1 env (zero1-cont cont)))
    
    (if-exp (exp1 exp2 exp3)
            (value-of/k exp1 env (if-test-cont exp2 exp3 env cont)))
    
    (let-exp (vars exps body)       
             (value-of/k (car exps) env (let-exp-cont vars (cdr exps) body env cont)))
    
    (letrec-exp (p-name param p-body letrec-body)
                (value-of/k letrec-body 
                            (extend-env-rec p-name param p-body env)
                            cont))
    
    (proc-exp (var body)
              (apply-cont cont (proc-val (procedure var body env))))
    
    (call-exp (rator rand)
              (value-of/k rator env (rator-cont rand env cont)))
    
    ))

;; apply-procedure/k : Proc ExpVal Cont -> FinalAnswer
(define (apply-procedure/k proc1 val cont)
  (cases proc proc1
    (procedure (var body saved-env)
               (value-of/k body (extend-env var val saved-env) cont))))

;; apply-cont: Cont ExpVal --> FinalAnswer (ExpVal)
;; Purpose: To apply the given continuation to the given value and return the final answer
(define (apply-cont cont val)
  (cases continuation cont
    (end-cont ()
              (begin
                (display "End of computation.\n")
                val))
    (zero1-cont (saved-cont)
                (apply-cont saved-cont (bool-val (zero? (expval->num val)))))
    
    (let-exp-cont (vars exps body saved-env saved-cont)
                  (if (null? exps)
                  (value-of/k
                   body
                   (extend-env (car vars) val saved-env)
                   saved-cont)
                  
                  (value-of/k
                   (car exps)
                   saved-env
                   (let-exp-cont (cdr vars) (cdr exps) body (extend-env (car vars) val saved-env)
                                 saved-cont))))
                  
    (if-test-cont (exp2 exp3 saved-env saved-cont)
                  (if (expval->bool val)
                      (value-of/k exp2 saved-env saved-cont)
                      (value-of/k exp3 saved-env saved-cont)))
    (diff1-cont (exp2 saved-env saved-cont)
                (value-of/k exp2 saved-env (diff2-cont val saved-cont)))
    (diff2-cont (val1 saved-cont)
                (let ((num1 (expval->num val1))
                      (num2 (expval->num val)))
                  (apply-cont saved-cont (num-val (- num1 num2)))))
    (sum1-cont (exp2 saved-env saved-cont)
                (value-of/k exp2 saved-env (sum2-cont val saved-cont)))
    (sum2-cont (val1 saved-cont)
                (let ((num1 (expval->num val1))
                      (num2 (expval->num val)))
                  (apply-cont saved-cont (num-val (+ num1 num2)))))
    (rator-cont (rand saved-env saved-cont)
                (value-of/k rand saved-env (rand-cont val saved-cont)))
    (rand-cont (rator-val saved-cont)
               (let ((proc1 (expval->proc rator-val)))
                 (apply-procedure/k proc1 val saved-cont)))
    (mult1-cont (exp2 saved-env saved-cont)
                (value-of/k exp2 saved-env (mult2-cont val saved-cont)))
    (mult2-cont (val1 saved-cont)
                (let ((num1 (expval->num val1))
                      (num2 (expval->num val)))
                  (apply-cont saved-cont (num-val (* num1 num2)))))
    ))

;;;;;;   EVALUATION WRAPPERS

;; parse: String -> a-program
(define (parse p) (scan&parse p))

;; eval : String -> ExpVal
(define (eval string)
  (value-of-program (parse string)))

;;;;; EXAMPLES OF EVALUATION


(eval "if zero?(1) then 1 else 2")
(eval "-(x, v)")
(eval "if zero?(-(x, x)) then x else 2")
(eval "if zero?(-(x, v)) then x else 2")
(eval "let decr = proc (a) -(a, 1) in (decr 30)")
(eval "( proc (g) (g 30) proc (y) -(y, 1))")
(eval "let x = 200 
         in let f = proc (z) -(z, x) 
              in let x = 100 
                   in let g = proc (z) -(z, x) 
                        in -((f 1), (g 1))")
(eval "let x = 200 
         in let f = proc (z) -(z, x) 
              in let x = 100 
                   in let g = proc (z) -(z, x) 
                        in -((f 1), (g 1))")

(eval "letrec fact(n) = if zero?(n) then 1 else *(n, (fact -(n, 1)))
       in (fact 5)")

(eval "let x = 2 in *(2, 8)")

(eval "zero?(-(2, 1))")

(eval "if zero?(-(2, 1)) then x else 2")

(eval "letrec fact(n) = if zero?(n) then 1 else *(n, (fact -(n, 1)))
       in (fact 5)")

