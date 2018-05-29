#lang eopl
(require test-engine/racket-tests)


;;;;;;;;;;;;;;;; grammatical specification ;;;;;;;;;;;;;;;;

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)
    ))

(define the-grammar
  '((program (expression) a-program)
    
    (expression (number) const-exp)
    (expression
     ("-" "(" expression "," expression ")")
     diff-exp)
    
    (expression
     ("zero?" "(" expression ")")
     zero?-exp)
    
    (expression
     ("if" expression "then" expression "else" expression)
     if-exp)
    
    (expression (identifier) var-exp)
    
    (expression
     ("let" "("(separated-list identifier ",")")" "="
            "(" (separated-list expression ",")")" "in" expression)
     let-exp)   
    
    (expression
     ("proc" "(" (separated-list identifier ",") ")" expression)
     proc-exp)
    
    (expression
     ("(" expression (arbno expression) ")")
     call-exp)
    
    (expression ("%nameless-var" "(" (arbno number) ")") nameless-var-exp)
    
    (expression
     ("%let" (separated-list expression ",") "in" expression) nameless-let-exp)
    
    (expression ("%lexproc" expression) nameless-proc-exp)
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define (show-the-datatypes) 
  (sllgen:list-define-datatypes the-lexical-spec the-grammar))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))


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
(define (expval->num v)
  (cases expval v
    (num-val (num) num)
    (else (expval-extractor-error 'num v))))

;; expval->bool : ExpVal -> Bool
(define (expval->bool v)
  (cases expval v
    (bool-val (bool) bool)
    (else (expval-extractor-error 'bool v))))

;; expval->proc : ExpVal -> Proc
(define (expval->proc v)
  (cases expval v
    (proc-val (proc) proc)
    (else (expval-extractor-error 'proc v))))

(define (expval-extractor-error variant value)
  (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
              variant value))

;;;;;;;;;;;;;;;; procedures ;;;;;;;;;;;;;;;;


;; proc? : SchemeVal -> Bool
;; procedure : Exp * Nameless-env -> Proc
(define-datatype proc proc?
  (procedure
   ;; in LEXADDR, bound variables are replaced by %nameless-vars, so
   ;; there is no need to declare bound variables.
   ;; (bvar symbol?)
   (body expression?)
   ;; and the closure contains a nameless environment
   (env nameless-environment?)))

;;;;;;;;;;;;;;;; environment constructors and observers ;;;;;;;;;;;;;;;;

;; nameless-environment? : SchemeVal -> Bool
(define (nameless-environment? x) ((list-of (list-of expval?)) x))

;; empty-nameless-env : () -> Nameless-env
(define (empty-nameless-env) '())

;; empty-nameless-env? : Nameless-env -> Bool
(define (empty-nameless-env? x) (null? x))

;; extend-nameless-env : list of ExpVals * Nameless-env -> Nameless-env
(define (extend-nameless-env vals nameless-env) (cons vals nameless-env))

;; apply-nameless-env : Nameless-env * Lexaddrs -> ExpVal
(define (apply-nameless-env nameless-env address) (list-ref (list-ref nameless-env (car address)) (cadr address)))


(define (init-nameless-env)
  (extend-nameless-env 
   (list (num-val 1))			; was i
   (extend-nameless-env
    (list (num-val 5))			; was v
    (extend-nameless-env
     (list (num-val 10))			; was x
     (empty-nameless-env)))))


;;;;;;;;;;;;;;;; lexical address calculator ;;;;;;;;;;;;;;;;

;; translation-of-program : Program -> Nameless-program
(define (translation-of-program pgm)
  (cases program pgm
    (a-program (exp1)
               (a-program                    
                (translation-of exp1 (init-senv))))))

;; translation-of : Exp * Senv -> Nameless-exp
(define (translation-of exp senv)
  (cases expression exp
    (const-exp (num) exp)
    (diff-exp (exp1 exp2)
              (diff-exp
               (translation-of exp1 senv)
               (translation-of exp2 senv)))
    (zero?-exp (exp1)
               (zero?-exp
                (translation-of exp1 senv)))
    (if-exp (exp1 exp2 exp3)
            (if-exp
             (translation-of exp1 senv)
             (translation-of exp2 senv)
             (translation-of exp3 senv)))
    (var-exp (var)
             (nameless-var-exp 
              (apply-senv senv var)))
    (let-exp (vars exps body)
             (nameless-let-exp
              (map (lambda (x) (translation-of x senv)) exps)            
              (translation-of body
                              (extend-senv vars senv))))
    (proc-exp (vars body)
              (nameless-proc-exp
               (translation-of body
                               (extend-senv vars senv))))
    (call-exp (rator rands)
              (call-exp
               (translation-of rator senv)
               (map (lambda (x) (translation-of x senv)) rands)))
    (else (report-invalid-source-expression exp))))

(define (report-invalid-source-expression exp)
  (eopl:error 'value-of 
              "Illegal expression in source code: ~s" exp))

;;;;;;;;;;;;;;;; static environments ;;;;;;;;;;;;;;;;

;;; Senv = Listof(Listof Sym)
;;; Lexaddr = (n n)

;; empty-senv : () -> Senv
(define (empty-senv) '())

;; extend-senv : Vars * Senv -> Senv
(define (extend-senv vars senv)
  (cons vars senv))

;; apply-senv : senv * var -> Lexaddr
;;purpose: calls 2 auxillary fuctions to produce a list of 2 ints which is the lexical address of var
(define (apply-senv senv var)
  (list (apply-senv-aux1 senv var) (apply-senv-aux2 (list-ref senv (apply-senv-aux1 senv var)) var))
  )

;; apply-senv-aux1: senv * var --> number
;; Purpose: to find the first int of the lexical address pair which is the lexical depth of var
(define (apply-senv-aux1 senv var)
  (cond
    ((null? senv) (report-unbound-var var))
    ((member var (car senv))
     0)
    (else
     (+ 1 (apply-senv-aux1 (cdr senv) var)))))

;apply-senv-aux2: (listof var) * var --> number
;Purpose: to find the second int of the lexical address which is the position of var in the rib
(define (apply-senv-aux2 rib var)
  (cond
    [(eq? var (car rib)) 0]
    [else (+ 1 (apply-senv-aux2 (cdr rib) var))]
    ))

(define (report-unbound-var var)
  (eopl:error 'translation-of "unbound variable in code: ~s" var))

;; init-senv : () -> Senv
(define (init-senv)
  (extend-senv '(i)
               (extend-senv '(v)
                            (extend-senv '(x)
                                         (empty-senv)))))


;;; INTERPRETER

;; value-of-translation : Nameless-program -> ExpVal
(define (value-of-program pgm)
  (cases program pgm
    (a-program (exp1)
               (value-of exp1 (init-nameless-env)))))

;; value-of : Nameless-exp * Nameless-env -> ExpVal
(define (value-of exp nameless-env)
  (cases expression exp
    (const-exp (num) (num-val num))
      
    (diff-exp (exp1 exp2)
              (let ((val1
                     (expval->num
                      (value-of exp1 nameless-env)))
                    (val2
                     (expval->num
                      (value-of exp2 nameless-env))))
                (num-val
                 (- val1 val2))))
      
    (zero?-exp (exp1)
               (let ((val1 (expval->num (value-of exp1 nameless-env))))
                 (if (zero? val1)
                     (bool-val #t)
                     (bool-val #f))))
      
    (if-exp (exp0 exp1 exp2) 
            (if (expval->bool (value-of exp0 nameless-env))
                (value-of exp1 nameless-env)
                (value-of exp2 nameless-env)))
      
    (call-exp (rator rands)          
              (let ((proc (expval->proc (value-of rator nameless-env)))
                    (args (map (lambda (x) (value-of x nameless-env)) rands)))
                (apply-procedure proc args)))
      
    (nameless-var-exp (l)
                      (apply-nameless-env nameless-env l))
      
    (nameless-let-exp (exps body)
                      (let ((vals (map (lambda (x) (value-of x nameless-env)) exps)))
                        (value-of body
                                  (extend-nameless-env vals nameless-env))))
      
    (nameless-proc-exp (body)
                       (proc-val
                        (procedure body nameless-env)))
      
    (else
     (eopl:error 'value-of 
                 "Illegal expression in translated code: ~s" exp))
      
    ))


;; apply-procedure : Proc * ExpVals -> ExpVal

(define (apply-procedure proc1 args)
  (cases proc proc1
    (procedure (body saved-env)
               (value-of body (extend-nameless-env args saved-env)))))


;;; TOP LEVEL ;;;

;; eval : String -> ExpVal

(define (eval string)
  (value-of-program
   (translation-of-program
    (scan&parse string))))

;;; EXAMPLES

(check-expect (eval "if zero?(1) then 1 else 2") (num-val 2))
(check-expect (eval "-(x, v)")(num-val 5))
(check-expect (eval "if zero?(-(x, x)) then x else 2") (num-val 10))
(check-expect (eval "if zero?(-(x, v)) then x else 2") (num-val 2))
(check-expect (eval "let (decr) = (proc (a) -(a, 1)) in (decr 30)") (num-val 29))
(check-expect (eval "( proc (g) (g 30) proc (y) -(y, 1))") (num-val 29))
(check-expect (eval "let (x) = (200) 
         in let (f) = (proc (z) -(z, x)) 
              in let (x) = (100) 
                   in let (g) = (proc (z) -(z, x)) 
                        in -((f 1), (g 1))") (num-val -100))
(check-expect (eval "let (sum) = (proc (x) proc (y) -(x, -(0, y))) in ((sum 3) 4)") (num-val 7))
(check-expect (eval "let (x) = (200) 
         in let (f) = (proc (z) -(z, x)) 
              in let (x) = (100) 
                   in let (g) = (proc (z) -(z, x)) 
                        in -((f 1), (g 1))") (num-val -100))
(check-expect (eval "let (f) = (proc (y, z) if zero? (z) then y else -(-(y, -1), -(z, 1))) in (f 5 5)") (num-val 2))
(check-expect (eval "let (sum , x) = (proc (x) proc (y) -(x, -(0, y)),3) in ((sum x) 4)") (num-val 7))




(test)
