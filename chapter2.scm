(import (scheme base) (scheme read) (scheme write) (scheme process-context))

(define (atom? x)
  (not (or (pair? x) (null? x))))

(define the-uninitialized-marker '$$uninitialized)

(define (evaluate e env)
  (if (atom? e)
    (cond
      ((eof-object? e) (interp-exit))
      ((symbol? e) (lookup e env))
      ((or (number? e) (string? e) (char? e) (boolean? e) (vector? e))
        e)
      (else (wrong "Cannot evaluate" e)))
    (case (car e)
      ((let)
        (eprogn
          (cddr e)
          ;; Page 61, special form version of let that allows
          ;; uninitialized binding
          (extend env
            (map (lambda (binding)
                   (if (symbol? binding) binding
                     (car binding)))
              (cadr e))
            (map (lambda (binding)
                   (if (symbol? binding) the-uninitialized-marker
                     (evaluate (cadr binding) env)))
              (cadr e)))))
      ((quote) (cadr e))
      ((if) (if (evaluate (cadr e) env)
              (evaluate (caddr e) env)
              (evaluate (cadddr e) env)))
      ((begin) (eprogn (cdr e) env))
      ((set!) (update! (cadr e) env (evaluate (caddr e) env)))
      ((lambda) (make-function (cadr e) (cddr e) env))
      (else (invoke
              (evaluate (car e) env)
              (evlis (cdr e) env))))))

(define empty-begin #f)

(define (eprogn exps env)
  (if (pair? exps)
    (if (pair? (cdr exps))
      (begin
        (evaluate (car exps) env)
        (eprogn (cdr exps) env))
      (evaluate (car exps) env))
    empty-begin))

(define (evlis exps env)
  (if (pair? exps)
    (cons
      (evaluate (car exps) env)
      (evlis (cdr exps) env))
    '()))

(define (lookup id env)
  (if (pair? env)
    (if (eq? (caar env) id)
      (let ((value (cdar env)))
        (if (eq? value the-uninitialized-marker)
          (wrong "Uninitialized binding" id)
          value))
      (lookup id (cdr env)))
    (wrong "No such binding" id)))

(define (update! id env value)
  (if (pair? env)
    (if (eq? (caar env) id)
      (begin
        (set-cdr! (car env) value)
        value)
      (update! id (cdr env) value))
    (wrong "No such binding" id)))

(define env.init '())

(define (extend env variables values)
  (cond
    ((pair? variables)
      (if (pair? values)
        (cons
          (cons (car variables) (car values))
          (extend env (cdr variables) (cdr values)))
        (wrong "Too less values")))
    ((null? variables)
      (if (null? values)
        env
        (wrong "Too much values")))
    ((symbol? variables)
      (cons (cons variables values) env))))

(define (invoke fn args)
  (if (procedure? fn)
    (fn args)
    (wrong "Not a function" fn)))

(define (make-function variables body env)
  (lambda (values)
    (eprogn body (extend env variables values))))

(define env.global env.init)

(define-syntax definitial
  (syntax-rules ()
    ((definitial name)
      (begin
        (set! env.global (cons (cons 'name 'void) env.global))
        'name))
    ((definitial name value)
      (begin
        (set! env.global (cons (cons 'name value) env.global))
        'name))))

(define-syntax defprimitive
  (syntax-rules ()
    ((defprimitive name value arity)
      (definitial name
        (lambda (values)
          (if (= arity (length values))
            (apply value values)
            (wrong
              "Incorrect arity"
              (list 'name values))))))))

(defprimitive car car 1)
(defprimitive set-cdr! set-cdr! 2)
(defprimitive + + 2)
(defprimitive eq? eq? 2)
(defprimitive < < 2)

(define (make-exit-exception) 'exit)

(define (exit-exception? x) (eqv? x 'exit))

(define (interp-exit)
  (raise (make-exit-exception)))

(defprimitive exit interp-exit 0)

(define (chapter1-scheme)
  (define (toplevel)
    (write-string "> ")
    (let ((res (with-exception-handler
                 (lambda (e)
                   (if (exit-exception? e)
                     (begin
                       (display "Bye!")
                       (exit))))
                 (lambda ()
                   (evaluate (read) env.global)))))
      (display res)
      (newline)
      (toplevel)))
  (toplevel))

(define (wrong msg . irritants)
  (apply error (cons msg irritants)))

(chapter1-scheme)
