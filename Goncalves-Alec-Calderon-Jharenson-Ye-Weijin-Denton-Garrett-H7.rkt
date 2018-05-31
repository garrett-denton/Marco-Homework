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
     ("+" "(" expression "," expression ")")
     add-exp)
    
    (expression
     ("*" "(" expression "," expression ")")
     mult-exp)
    
    (expression
     ("zero?" "(" expression ")")
     zero?-exp)
    
    (expression
     ("if" expression "then" expression "else" expression)
     if-exp)
    
    (expression (identifier) var-exp)
    
    (expression
     ("let" identifier "=" expression "in" expression)
     let-exp)

    (expression
     ("lazylet" identifier "=" expression "in" expression)
     lazylet-exp)
    
    (expression
     ("proc" "(" identifier ")" expression)
     proc-exp)
    
    (expression
     ("(" expression expression ")")
     call-exp)
    
    (expression
     ("letrec"
      (arbno identifier "(" identifier ")" "=" expression)
      "in" expression)
     letrec-exp)
    
    (expression
     ("begin" expression (arbno ";" expression) "end")
     begin-exp)
    
    (expression
     ("set" identifier "=" expression)
     assign-exp)
    
    ;; new for mutable-pairs
    
    (expression
     ("newpair" "(" expression "," expression ")")
     newpair-exp)
    
    (expression
     ("left" "(" expression ")")
     left-exp)
    
    (expression
     ("setleft" expression "=" expression)
     setleft-exp)
    
    (expression
     ("right" "(" expression ")")
     right-exp)
    
    (expression
     ("setright" expression "=" expression)
     setright-exp)
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define (show-the-datatypes) 
  (sllgen:list-define-datatypes the-lexical-spec the-grammar))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))


;;;;;;;;;;;;;;;; expressed values ;;;;;;;;;;;;;;;;

(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val 
   (proc proc?))
  (mutpair-val
   (p mutpair?))
  )
;;; extractors:

(define (expval->num v)
  (cases expval v
    (num-val (num) num)
    (else (expval-extractor-error 'num v))))

(define (expval->bool v)
  (cases expval v
    (bool-val (bool) bool)
    (else (expval-extractor-error 'bool v))))

(define (expval->proc v)
  (cases expval v
    (proc-val (proc) proc)
    (else (expval-extractor-error 'proc v))))

(define expval->mutpair
  (lambda (v)
    (cases expval v
      (mutpair-val (ref) ref)
      (else (expval-extractor-error 'mutable-pair v)))))


(define (expval-extractor-error variant value)
  (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
              variant value))

;;;;;;;;;;;;;;;; procedures ;;;;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (bvar symbol?)
   (body expression?)
   (env environment?)))

(define-datatype environment environment?
  (empty-env)
  (extend-env 
   (bvar symbol?)
   (bval reference?)                 ; new for implicit-refs
   (saved-env environment?))
  (extend-env-rec*
   (proc-names (list-of symbol?))
   (b-vars (list-of symbol?))
   (proc-bodies (list-of expression?))
   (saved-env environment?)))

;; env->list : Env -> List
;; used for pretty-printing and debugging
(define (env->list env)
  (cases environment env
    (empty-env () '())
    (extend-env (sym val saved-env)
                (cons
                 (list sym (expval->printable val))
                 (env->list saved-env)))
    (extend-env-rec* (p-names b-vars p-bodies saved-env)
                     (cons
                      (list 'letrec p-names '...)
                      (env->list saved-env)))))

;; expval->printable : ExpVal -> List
;; returns a value like its argument, except procedures get cleaned
;; up with env->list 
(define (expval->printable val)
  (cases expval val
    (proc-val (p)
              (cases proc p
                (procedure (var body saved-env)
                           (list 'procedure var '... (env->list saved-env)))))
    (else val)))


;;;;;;;;;;;;;;;; initial environment ;;;;;;;;;;;;;;;;


;; init-env : () -> Env
(define init-env 
  (lambda ()
    (extend-env 
     'i (newref (num-val 1))
     (extend-env
      'v (newref (num-val 5))
      (extend-env
       'x (newref (num-val 10))
       (empty-env))))))

;;;;;;;;;;;;;;;; environment constructors and observers ;;;;;;;;;;;;;;;;

(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
                 (eopl:error 'apply-env "No binding for ~s" search-var))
      (extend-env (bvar bval saved-env)
                  (if (eqv? search-var bvar)
                      bval
                      (apply-env saved-env search-var)))
      (extend-env-rec* (p-names b-vars p-bodies saved-env)
                       (let ((n (location search-var p-names)))
                         ;; n : (maybe int)
                         (if n
                             (newref
                              (proc-val
                               (procedure 
                                (list-ref b-vars n)
                                (list-ref p-bodies n)
                                env)))
                             (apply-env saved-env search-var)))))))


;; location : Sym * Listof(Sym) -> Maybe(Int)
;; (location sym syms) returns the location of sym in syms or #f is
;; sym is not in syms.  We can specify this as follows:
;; if (memv sym syms)
;;   then (list-ref syms (location sym syms)) = sym
;;   else (location sym syms) = #f
(define (location sym syms)
  (cond
    ((null? syms) #f)
    ((eqv? sym (car syms)) 0)
    ((location sym (cdr syms))
     => (lambda (n) 
          (+ n 1)))
    (else #f)))


;;;;;;;;;;;;;;;; references and the store ;;;;;;;;;;;;;;;;

;;; world's dumbest model of the store:  the store is a list and a
;;; reference is number which denotes a position in the list.

;; the-store: a Scheme variable containing the current state of the
;; store.  Initially set to a dummy variable.
(define the-store 'uninitialized)

;; empty-store : () -> Sto
(define (empty-store) '())

;; initialize-store! : () -> Sto
;; usage: (initialize-store!) sets the-store to the empty-store
(define (initialize-store!)
  (set! the-store (empty-store)))

;; get-store : () -> Sto
;; This is obsolete.  Replaced by get-store-as-list below
(define (get-store) the-store)

;; reference? : SchemeVal -> Bool
(define (reference? v)
  (integer? v))

;; newref : ExpVal -> Ref
(define (newref val)
  (let ((next-ref (length the-store)))
    (set! the-store
          (append the-store (list val)))                    
    next-ref))                     

;; deref : Ref -> ExpVal
(define (deref ref)
  (list-ref the-store ref))

;; setref! : Ref * ExpVal -> Unspecified
(define (setref! ref val)
  (set! the-store
        (letrec
            ((setref-inner
              ;; returns a list like store1, except that position ref1
              ;; contains val. 
              (lambda (store1 ref1)
                (cond
                  ((null? store1)
                   (report-invalid-reference ref the-store))
                  ((zero? ref1)
                   (cons val (cdr store1)))
                  (else
                   (cons
                    (car store1)
                    (setref-inner
                     (cdr store1) (- ref1 1))))))))
          (setref-inner the-store ref))))

(define (report-invalid-reference ref the-store)
  (eopl:error 'setref
              "illegal reference ~s in store ~s"
              ref the-store))

;; get-store-as-list : () -> Listof(List(Ref,Expval))
;; Exports the current state of the store as a scheme list.
;; (get-store-as-list '(foo bar baz)) = ((0 foo)(1 bar) (2 baz))
;;   where foo, bar, and baz are expvals.
;; If the store were represented in a different way, this would be
;; replaced by something cleverer.
(define (get-store-as-list)
  (letrec
      ((inner-loop
        ;; convert sto to list as if its car was location n
        (lambda (sto n)
          (if (null? sto)
              '()
              (cons
               (list n (car sto))
               (inner-loop (cdr sto) (+ n 1)))))))
    (inner-loop the-store 0)))


;;;;;;;;;;;;;;;; mutable pairs ;;;;;;;;;;;;;;;;

;; mutpair? : SchemeVal -> Bool
(define (mutpair? v) (reference? v))

;; make-pair : ExpVal * ExpVal -> MutPair
(define (make-pair val1 val2)
  (let ((ref1 (newref val1)))
    (let ((ref2 (newref val2)))
      ref1)))

;; left : MutPair -> ExpVal
(define (left p) (deref p))

;; right : MutPair -> ExpVal 
(define (right p) (deref (+ 1 p)))

;; setleft : MutPair * ExpVal -> Unspecified 
(define (setleft p val) (setref! p val))

;; setright : MutPair * Expval -> Unspecified 
(define (setright p val) (setref! (+ 1 p) val))


;;;;;;;;;;;;;;;; thunks ;;;;;;;;;;;;;;;;

;; a-thunk : Exp * Env -> Thunk
;; thunk? : SchemeVal -> Bool
(define-datatype thunk thunk?
  (a-thunk
   (exp1 expression?)
   (env environment?)))



;;;; Interpreter


;; value-of-program : Program -> ExpVal
(define (value-of-program pgm)
  (initialize-store!)               ; new for explicit refs.
  (cases program pgm
    (a-program (exp1)
               (value-of exp1 (init-env)))))

;; value-of : Exp * Env -> ExpVal
(define (value-of exp env)
  (cases expression exp
    
    (const-exp (num) (num-val num))
    
    (var-exp (var) ; call-by-need
             (let ((ref1 (apply-env env var)))
               (let ((w (deref ref1)))  
                 (if (expval? w)
                     w
                     (let ((v1 (value-of-thunk w)))
                       (begin
                         (setref! ref1 v1)   
                         v1))))))
    
    (diff-exp (exp1 exp2)
              (let ((val1 (value-of exp1 env))
                    (val2 (value-of exp2 env)))
                (let ((num1 (expval->num val1))
                      (num2 (expval->num val2)))
                  (num-val
                   (- num1 num2)))))
    
    (add-exp (exp1 exp2)
             (let ((val1 (value-of exp1 env))
                   (val2 (value-of exp2 env)))
               (let ((num1 (expval->num val1))
                     (num2 (expval->num val2)))
                 (num-val
                  (+ num1 num2)))))
    
    (mult-exp (exp1 exp2)
              (let ((val1 (value-of exp1 env))
                    (val2 (value-of exp2 env)))
                (let ((num1 (expval->num val1))
                      (num2 (expval->num val2)))
                  (num-val
                   (* num1 num2)))))
    
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
             (let ((v1 (value-of exp1 env)))
               (value-of body
                         (extend-env var (newref v1) env))))
    
    (lazylet-exp (var exp1 body)       
             (let ((v1 (a-thunk exp1 env)))
               (value-of body
                         (extend-env var (newref v1) env))))
    
    (proc-exp (var body)
              (proc-val (procedure var body env)))
    
    (call-exp (rator rand)
              (let ((proc (expval->proc (value-of rator env)))
                    (arg (value-of-operand rand env)))
                (apply-procedure proc arg)))
    
    (letrec-exp (p-names b-vars p-bodies letrec-body)
                (value-of letrec-body
                          (extend-env-rec* p-names b-vars p-bodies env)))
    
    (begin-exp (exp1 exps)
               (letrec 
                   ((value-of-begins
                     (lambda (e1 es)
                       (let ((v1 (value-of e1 env)))
                         (if (null? es)
                             v1
                             (value-of-begins (car es) (cdr es)))))))
                 (value-of-begins exp1 exps)))
    
    (assign-exp (var exp1)
                (begin
                  (setref!
                   (apply-env env var)
                   (value-of exp1 env))
                  (num-val 27))) ;; this is a don't care value.
    
    (newpair-exp (exp1 exp2)
                 (let ((v1 (value-of exp1 env))
                       (v2 (value-of exp2 env)))
                   (mutpair-val (make-pair v1 v2))))
    
    (left-exp (exp1)
              (let ((v1 (value-of exp1 env)))
                (let ((p1 (expval->mutpair v1)))
                  (left p1))))
    
    (right-exp (exp1)
               (let ((v1 (value-of exp1 env)))
                 (let ((p1 (expval->mutpair v1)))
                   (right p1))))
    
    (setleft-exp (exp1 exp2)
                 (let ((v1 (value-of exp1 env))
                       (v2 (value-of exp2 env)))
                   (let ((p (expval->mutpair v1)))
                     (begin
                       (setleft p v2)
                       (num-val 82))))) ;; this is a don't care value.
    
    (setright-exp (exp1 exp2)
                  (let ((v1 (value-of exp1 env))
                        (v2 (value-of exp2 env)))
                    (let ((p (expval->mutpair v1)))
                      (begin
                        (setright p v2)
                        (num-val 83))))) ;; this is a don't care value.
    ))

;; apply-procedure : Proc * Ref -> ExpVal
(define (apply-procedure proc1 val)
  (cases proc proc1
    (procedure (var body saved-env)
               (let ((new-env (extend-env var val saved-env)))
                 (value-of body new-env)))))

;; value-of-operand : Exp * Env -> Ref
(define (value-of-operand exp env)
  (cases expression exp
    (var-exp (var) (apply-env env var))
    (const-exp (num) (newref (num-val num)))
    (proc-exp (var body) (newref (proc-val (procedure var body env))))
    (else
     (newref (a-thunk exp env)))))

;; value-of-thunk : Thunk -> ExpVal
(define (value-of-thunk th)
  (cases thunk th
    (a-thunk (exp1 saved-env)
             (value-of exp1 saved-env))))


;; store->readable : Listof(List(Ref,Expval)) 
;;                    -> Listof(List(Ref,Something-Readable))
(define (store->readable l)
  (map
   (lambda (p)
     (cons
      (car p)
      (expval->printable (cadr p))))
   l))


;;; TOP LEVEL ;;;

;; eval : String -> ExpVal

(define (eval string)
  (value-of-program
   (scan&parse string)))


(check-expect (eval "if zero?(1) then 1 else 2") (num-val 2))
(check-expect (eval "-(x, v)") (num-val 5))
(check-expect (eval "if zero?(-(x, x)) then x else 2") (num-val 10))
(check-expect (eval "if zero?(-(x, v)) then x else 2") (num-val 2))
(check-expect (eval "lazylet decr = proc (a) -(a, 1) in (decr 30)") (num-val 29))
(check-expect (eval "( proc (g) (g 30) proc (y) -(y, 1))") (num-val 29))
(check-expect (eval "lazylet x = 200 
         in lazylet f = proc (z) -(z, x) 
              in lazylet x = 100 
                   in lazylet g = proc (z) -(z, x) 
                        in -((f 1), (g 1))") (num-val -100))



(check-expect (eval "lazylet temp = 0
       in  lazylet x = 5
           in  lazylet mystery = proc (y) 
                               begin
                                 set temp = x;
                                 set x = y;
                                 set y = temp;
                                 x
                               end
               in (mystery 10)") (num-val 10))

(check-expect (eval "letrec fact(n) = if zero?(n) then 1 else *(n, (fact -(n, 1)))
       in (fact 5)") (num-val 120))

(check-expect (eval "lazylet res = 0
       in letrec sum(n) = if zero?(n) 
                          then res 
                          else
                            begin
                             set res = +(res, n);
                             (sum -(n, 1))
                            end
           in (sum 10)") (num-val 55))

(check-expect (eval "lazylet a = 3
       in lazylet p = proc (x) set x = 4
          in begin 
               (p a); 
               a 
             end") (num-val 4))

(check-expect (eval "lazylet p = newpair(4, 5)
       in right(p)") (num-val 5))

(check-expect (eval "lazylet p = newpair(4, 5)
       in left(p)") (num-val 4))

(check-expect (eval "lazylet p = newpair(4, 5)
       in begin
           setleft p = 15;
           setright p = 15;
           -(left(p), right(p))
          end") (num-val 0))


(check-expect (eval "lazylet swap = proc (a) 
                    proc (b)
                      let t = a
                      in begin
              		   set a = b;
                           set b = t
			 end
        in lazylet a = 33
	   in lazylet b = 44
	      in begin
		   ((swap a) b);
		   -(a, b)
		 end") (num-val 11))

(check-expect (eval "letrec compute-ints-from-n (n) = (compute-ints-from-n +(n, 1))
       in lazylet f = proc (k) 42
          in (f (compute-ints-from-n 100))") (num-val 42))


(check-expect (eval "lazylet g = lazylet counter = 10
               in proc (d) *(2, counter)
       in (proc (x) +(x, x) (g 0))") (num-val 40))

(check-expect (eval "lazylet g = lazylet count = 0
               in proc (dummy)
                    begin
                      set count = +(count, 1);
                      count
		    end
       in (proc (x) +(x, x) (g 0))") (num-val 2))

(test)
