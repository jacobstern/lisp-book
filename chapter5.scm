#!/usr/bin/env gosh

;;; Code adapted from Chapter 5 of Lisp in Small Pieces by Christian Quiennec
;;; Requires Gauche Scheme http://practical-scheme.net/gauche/

;;; This interpreter isn't complete, I only added the code from the
;;; text of the book

(use scheme.base)

(define (wrong msg . irritants)
  (apply error (cons msg irritants)))

(define ((meaning-abstraction n* e+) r k s)
  (k (inValue (lambda (v* k1 s1)
                (if (= (length v*) (length n*))
                  (allocate s1 (length n*)
                    (lambda (s2 a*)
                      ((meaning*-sequence e+)
                        (extend* r n* a*)
                        k1
                        (extend* s2 a* v*))))
                  (wrong "Incorrect arity"))))
    s))

(define (meaning e)
  (if (list? e)
    (case (car e)
      ((quote) (meaning-quotation (cadr e)))
      ((lambda) (meaning-abstraction (cadr e) (cddr e)))
      ((if) (meaning-alternative (cadr e) (caddr e) (cadddr e)))
      ((begin) (meaning-sequence (cdr e)))
      ((set!) (meaning-assignment (cadr e) (caddr e)))
      (else (meaning-application (car e) (cdr e))))
    (if (symbol? e) (meaning-reference e)
      (meaning-quotation e))))

(define-syntax memo-delay
  (syntax-rules ()
    ((memo-delay expression)
      (let ((already-computed? #f)
             (value 'wait))
        (lambda ()
          (if (not already-computed?)
            (begin
              (set! value expression)
              (set! already-computed? #t)))
          value)))))

(define (cps e)
  (if (list? e)
    (case (car e)
      ((quote) (cps-quote (cadr e)))
      ((if) (cps-if (cadr e) (caddr e) (cadddr e)))
      ((begin) (cps begin (cdr e)))
      ((set!) (cps-set! (cadr e) (caddr e)))
      ((lambda) (cps-abstraction (cadr e) (caddr e)))
      (else (cps-application e)))
    (lambda (k) (k e))))

(define (cps-quote data)
  (lambda (k)
    (k `(quote ,data))))

(define (cps-set! variable form)
  (lambda (k)
    ((cps form)
      (lambda (a)
        (k `(set! ,variable ,a))))))

(define (cps-if bool form1 form2)
  (lambda (k)
    ((cps bool)
      (lambda (b)
        `(if ,b ,((cps form1) k)
           ,((cps form2) k))))))

(define (cps-begin e)
  (if (pair? e)
    (if (pair? (cdr e))
      (let ((void (gensym "void")))
        (lambda (k)
          ((cps-begin (cdr e))
            (lambda (b)
              ((cps (car e))
                (lambda (a)
                  (k `((lambda (,void) ,b) ,a))))))))
      (cps (car e)))
    (cps '())))

(define (cps-application e)
  (lambda (k)
    (if (memq (car e) primitives)
      ((cps-terms (cdr e))
        (lambda (t*)
          (k `(,(car e) ,@t*))))
      ((cps-terms e)
        (lambda (t*)
          (let ((d (gensym)))
            `(,(car t*) (lambda (,d) ,(k d))
               . ,(cdr t*))))))))

(define primitives '(cons car cdr list * + - = pair? eq?))

(define (cps-terms e*)
  (if (pair? e*)
    (lambda (k)
      ((cps (car e*))
        (lambda (a)
          ((cps-terms (cdr e*))
            (lambda (a*)
              (k (cons a a*)))))))
    (lambda (k) (k '()))))

(define (cps-abstraction variables body)
  (lambda (k)
    (k (let ((c (gensym "cont")))
         `(lambda (,c . ,variables)
            ,((cps body)
               (lambda (a) `(,c ,a))))))))
