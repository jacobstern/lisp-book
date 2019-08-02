#!/usr/bin/env gosh

;;; Code adapted from Chapter 3 of Lisp in Small Pieces by Christian Quiennec
;;; Requires Gauche Scheme http://practical-scheme.net/gauche/

(use scheme.base)

(define (wrong msg . irritants)
  (apply error (cons msg irritants)))

(define (atom? x) (not (list? x)))

(define (evaluate e r k)
  (if (atom? e)
    (cond
      ((symbol? e) (evaluate-variable e r k))
      (else (evaluate-quote e r k)))
    (case (car e)
      ((quote) (evaluate-quote (cadr e) r k))
      ((if) (evaluate-if (cadr e) (caddr e) (cadddr e) r k))
      ((begin) (evaluate-begin (cdr e) r k))
      ((set!) (evaluate-set! (cadr e) (caddr e) r k))
      ((lambda) (evaluate-lambda (cadr e) (cddr e) r k))
      ((catch) (evaluate-catch (cadr e) (cddr e) r k))
      ((throw) (evaluate-throw (cadr e) (caddr e) r k))
      ((unwind-protect) (evaluate-unwind-protect (cadr e) (cddr e) r k))
      (else (evaluate-application (car e) (cdr e) r k)))))

(define-class <value> () ())

(define-class <environment> () ())

(define-class <continuation> ()
  ((k :init-keyword :k :getter continuation-k)))

(define (evaluate-quote v r k)
  (resume k v))

(define-class <if-cont> (<continuation>)
  ((et :init-keyword :et :getter if-cont-et)
    (ef :init-keyword :ef :getter if-cont-ef)
    (r :init-keyword :r :getter if-cont-er)))


(define (make-if-cont k et ef r)
  (make <if-cont> :k k :et et :ef ef :r r))

(define (evaluate-if ec et ef r k)
  (evaluate ec r (make-if-cont k et ef r)))

(define-method resume ((k <if-cont>) v)
  (evaluate (if v (if-cont-et k) (if-cont-ef k))
    (if-cont-r k)
    (continuation-k k)))

(define-class <begin-cont> (<continuation>)
  ((e* :init-keyword :e* :getter begin-cont-e*)
    (r :init-keyword :r :getter begin-cont-r)))

(define (make-begin-cont k e* r)
  (make <begin-cont> :k k :e* e* :r r))

(define empty-begin-value 'void)

(define (evaluate-begin e* r k)
  (if (pair? e*)
    (if (pair? (cdr e*))
      (evaluate (car e*) r (make-begin-cont k e* r))
      (evaluate (car e*) r k))
    (resume k empty-begin-value)))

(define-method resume ((k <begin-cont>) v)
  (evaluate-begin
    (cdr (begin-cont-e* k))
    (begin-cont-r k)
    (continuation-k k)))

(define-class <null-env> (<environment>) ())

(define (make-null-env)
  (make <null-env>))

(define-class <full-env> (<environment>)
  ((others :init-keyword :others :getter full-env-others)
    (name :init-keyword :name :getter full-env-name)))

(define (make-full-env others name)
  (make <full-env> :others others :name name))

(define-class <variable-env> (<full-env>)
  ((value
     :init-keyword :value
     :getter variable-env-value
     :setter set-variable-env-value!)
    (name
      :init-keyword :name
      :getter variable-env-name)))

(define (make-variable-env others name value)
  (make <variable-env> :others others :name name :value value))

(define (evaluate-variable n r k)
  (lookup r n k))

(define-method lookup ((r <null-env>) n k)
  (wrong "Unknown variable" n r k))

(define-method lookup ((r <full-env>) n k)
  (lookup (full-env-others r) n k))

(define-method lookup ((r <variable-env>) n k)
  (if (eqv? n (variable-env-name r))
    (resume k (variable-env-value r))
    (lookup (full-env-others r) n k)))

(define-class <set!-cont> (<continuation>)
  ((n :init-keyword :n :getter set!-cont-n)
    (r :init-keyword :r :getter set!-cont-r)))

(define (make-set!-cont k n r)
  (make <set!-cont> :k k :n n :r r))

(define (evaluate-set! n e r k)
  (evaluate e r (make-set!-cont k n r)))

(define-method update! ((r <null-env>) n k v)
  (wrong "Unknown variable" n r k))

(define-method update! ((r <full-env>) n k v)
  (update! (full-env-others r) n k v))

(define-method update! ((r <variable-env>) n k v)
  (if (eqv? n (variable-env-name r))
    (begin
      (set-variable-env-value! r v)
      (resume k v))
    (update! (full-env-others r) n k v)))

(define-method resume ((k <set!-cont>) v)
  (update! (set!-cont-r k) (set!-cont-n k) (continuation-k k) v))

(define-class <function> (<value>)
  ((variables :init-keyword :variables :getter function-variables)
    (body :init-keyword :body :getter function-body)
    (env :init-keyword :env :getter function-env)))

(define (make-function variables body env)
  (make <function> :variables variables :body body :env env))

(define (evaluate-lambda n* e* r k)
  (resume k (make-function n* e* r)))

(define-method invoke ((f <function>) v* r k) ; r = current environment
  (let ((env (extend-env
               (function-env f)
               (function-variables f)
               v*)))
    (evaluate-begin (function-body f) env k)))

(define (extend-env env names values)
  (cond ((and (pair? names) (pair? values))
          (make-variable-env
            (extend-env env (cdr names) (cdr values))
            (car names)
            (car values)))
    ((and (null? names) (null? values)) env)
    ((symbol? names) (make-variable-env env names values))
    (else (wrong "Arity mismatch"))))

(define-class <evfun-cont> (<continuation>)
  ((e* :init-keyword :e* :getter evfun-cont-e*)
    (r :init-keyword :r :getter evfun-cont-r)))

(define (make-evfun-cont k e* r)
  (make <evfun-cont> :k k :e* e* :r r))

(define-class <apply-cont> (<continuation>)
  ((f :init-keyword :f :getter apply-cont-f)
    (r :init-keyword :r :getter apply-cont-r)))

(define (make-apply-cont k f r)
  (make <apply-cont> :k k :f f :r r))

(define-class <argument-cont> (<continuation>)
  ((e* :init-keyword :e* :getter argument-cont-e*)
    (r :init-keyword :r :getter argument-cont-r)))

(define (make-argument-cont k e* r)
  (make <argument-cont> :k k :e* e* :r r))

(define-class <gather-cont> (<continuation>)
  ((v :init-keyword :v :getter gather-cont-v)))

(define (make-gather-cont k v)
  (make <gather-cont> :k k :v v))

(define (evaluate-application e e* r k)
  (evaluate e r (make-evfun-cont k e* r)))

(define-method resume ((k <evfun-cont>) f)
  (evaluate-arguments
    (evfun-cont-e* k)
    (evfun-cont-r k)
    (make-apply-cont (continuation-k k)
      f
      (evfun-cont-r k))))

(define-class <no-more-argument-cont> (<continuation>)
  ())

(define (make-no-more-argument-cont k)
  (make <no-more-argument-cont> :k k))

(define (evaluate-arguments e* r k)
  (if (pair? e*)
    (if (pair? (cdr e*))
      (evaluate (car e*) r (make-argument-cont k e* r))
      (evaluate (car e*) r (make-no-more-argument-cont k)))
    (resume k no-more-arguments)))

(define no-more-arguments '())

(define-method resume ((k <argument-cont>) v)
  (evaluate-arguments
    (cdr (argument-cont-e* k))
    (argument-cont-r k)
    (make-gather-cont (continuation-k k) v)))

(define-method resume ((k <gather-cont>) v*)
  (resume (continuation-k k) (cons (gather-cont-v k) v*)))

(define-method resume ((k <apply-cont>) v)
  (invoke (apply-cont-f k)
    v
    (apply-cont-r k)
    (continuation-k k)))

(define-method resume ((k <no-more-argument-cont>) v)
  (resume (continuation-k k) (list v)))

(define-syntax definitial
  (syntax-rules ()
    ((definitial name)
      (definitial name 'void))
    ((definitial name value)
      (begin (set! r.init (make-variable-env r.init 'name value))
        'name))))

(define-class <primitive> (<value>)
  ((name :init-keyword :name :getter primitive-name)
    (address :init-keyword :address :getter primitive-address)))

(define (make-primitive name address)
  (make <primitive> :name name :address address))

(define-syntax defprimitive
  (syntax-rules ()
    ((defprimitive name value arity)
      (definitial name
        (make-primitive
          'name (lambda (v* r k)
                  (if (= arity (length v*))
                    (resume k (apply value v*))
                    (wrong "Incorrect arity" 'name v*))))))))

(define r.init (make-null-env))

(defprimitive cons cons 2)

(defprimitive car car 1)

(defprimitive + + 2)

(defprimitive * * 2)

(define-method invoke ((f <primitive>) v* r k)
  ((primitive-address f) v* r k))

(define-class <bottom-cont> (<continuation>)
  ((f :init-keyword :f :getter bottom-cont-f)))

(define (make-bottom-cont k f)
  (make <bottom-cont> :k k :f f))

(define-method resume ((k <bottom-cont>) v)
  ((bottom-cont-f k) v))

(define (chapter3-interpreter)
  (define (toplevel)
    (evaluate (read)
      r.init
      (make-bottom-cont 'void display))
    (toplevel))
  (toplevel))

(definitial call/cc
  (make-primitive
    'call/cc
    (lambda (v* r k)
      (if (= 1 (length v*))
        (invoke (car v*) (list k) r k)
        (wrong "Incorrect arity" 'call/cc v*)))))

(define-method invoke ((f <continuation>) v* r k)
  (if (= 1 (length v*))
    (resume f (car v*))
    (wrong "Continuations expect one argument" v* r k)))

(define-class <catch-cont> (<continuation>)
  ((body :init-keyword :body :getter catch-cont-body)
    (r :init-keyword :r :getter catch-cont-r)))

(define (make-catch-cont k body r)
  (make <catch-cont> :k k :body body :r r))

(define-class <labeled-cont> (<continuation>)
  ((tag :init-keyword :tag :getter labeled-cont-tag)))

(define (make-labeled-cont k tag)
  (make <labeled-cont> :k k :tag tag))

;; Not printed in book, I might have missed something here
(define-method resume ((k <labeled-cont>) v)
  (resume (continuation-k k) v))

(define (evaluate-catch tag body r k)
  (evaluate tag r (make-catch-cont k body r)))

(define-method resume ((k <catch-cont>) v)
  (evaluate-begin (catch-cont-body k)
    (catch-cont-r k)
    (make-labeled-cont (continuation-k k) v)))

(define-class <throw-cont> (<continuation>)
  ((form :init-keyword :form :getter throw-cont-form)
    (r :init-keyword :r :getter throw-cont-r)))

(define (make-throw-cont k form r)
  (make <throw-cont> :k k :form form :r r))

(define-class <throwing-cont> (<continuation>)
  ((tag :init-keyword :tag :getter throwing-cont-tag)
    (cont :init-keyword :cont :getter throwing-cont-cont)))

(define (make-throwing-cont k tag cont)
  (make <throwing-cont> :k k :tag tag :cont cont))

(define (evaluate-throw tag form r k)
  (evaluate tag r (make-throw-cont k form r)))

(define-method resume ((k <throw-cont>) tag)
  (catch-lookup k tag k))

(define-method catch-lookup ((k <continuation>) tag kk)
  (catch-lookup (continuation-k k) tag kk))

(define-method catch-lookup ((k <bottom-cont>) tag kk)
  (wrong "No associated catch" k tag kk))

(define-method catch-lookup ((k <labeled-cont>) tag kk)
  (if (eqv? tag (labeled-cont-tag k))   ; comparator
    (evaluate (throw-cont-form kk)
      (throw-cont-r kk)
      (make-throwing-cont kk tag k))
    (catch-lookup (continuation-k k) tag kk)))

(define-method resume ((k <throwing-cont>) v)
  (unwind (continuation-k k) v (throwing-cont-cont k)))

(define-class <unwind-protect-cont> (<continuation>)
  ((cleanup :init-keyword :cleanup :getter unwind-protect-cont-cleanup)
    (r :init-keyword :r :getter unwind-protect-cont-r)))

(define (make-unwind-protect-cont k cleanup r)
  (make <unwind-protect-cont> :k k :cleanup cleanup :r r))

(define-class <protect-return-cont> (<continuation>)
  ((value :init-keyword :value :getter protect-return-cont-value)))

(define (make-protect-return-cont k value)
  (make <protect-return-cont> :k k :value value))

(define (evaluate-unwind-protect form cleanup r k)
  (evaluate form
    r
    (make-unwind-protect-cont k cleanup r)))

(define-method resume ((k <unwind-protect-cont>) v)
  (evaluate-begin (unwind-protect-cont-cleanup k)
    (unwind-protect-cont-r k)
    (make-protect-return-cont (continuation-k k) v)))

(define-method resume ((k <protect-return-cont>) v)
  (resume (continuation-k k) (protect-return-cont-value k)))

(define-class <unwind-cont> (<continuation>)
  ((value :init-keyword :value :getter unwind-cont-value)
    (target :init-keyword :target :getter unwind-cont-target)))

(define (make-unwind-cont k value target)
  (make <unwind-cont> :k k :value value :target target))

(define-method unwind ((k <continuation>) v ktarget)
  (if (eq? k ktarget) (resume k v)
    (unwind (continuation-k k) v ktarget)))

(define-method unwind ((k <bottom-cont>) v ktarget)
  (wrong "Obsolete continuation v"))

(define-method unwind ((k <unwind-protect-cont>) v target)
  (evaluate-begin
    (unwind-protect-cont-cleanup k)
    (unwind-protect-cont-r k)
    (make-unwind-cont
      (continuation-k k) v target)))

(define-method resume ((k <unwind-cont>) v)
  (unwind
    (continuation-k k)
    (unwind-cont-value k)
    (unwind-cont-target k)))

