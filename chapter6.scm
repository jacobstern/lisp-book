#!/usr/bin/env gosh

;;; Code adapted from Chapter 6 of Lisp in Small Pieces by Christian Quiennec
;;; Requires Gauche Scheme http://practical-scheme.net/gauche/

(use scheme.base)

(define (wrong msg . culprits)
  (apply error (cons msg culprits)))

(define-class <environment> ()
  ((next :init-keyword :next :accessor next-of)))

(define-class <activation-frame> (<environment>)
  ((size :init-keyword :size :getter size-of)
    (arguments :getter arguments-of)))

(define-method initialize ((self <activation-frame>) initargs)
  (let ((ret (next-method)))
    (if (number? (size-of self))
      (begin
        (set! (ref self 'arguments) (make-vector (size-of self)))
        ret)
      (error "Must initialize <activation-frame> with a size"))))

(define (set-activation-frame-argument! x n v)
  (set! (vector-ref (arguments-of x) n) v))

(define activation-frame-argument
  (getter-with-setter (lambda (x n)
                        (vector-ref (arguments-of x) n))
    set-activation-frame-argument!))

(define (activation-frame-argument-length x)
  (vector-length (ref x 'arguments)))

(define (sr-extend* sr v*)
  (set! (next-of sr) v*)
  v*)

(define (deep-fetch sr i j)
  (if (= i 0)
    (activation-frame-argument sr j)
    (deep-fetch (next-of sr) (- i 1) j)))

(define (deep-update! sr i j v)
  (if (= i 0)
    (set! (activation-frame-argument! sr j) v)
    (deep-update! (next-of sr) (- i 1) j v)))

(define (r-extend* r n*)
  (cons n* r))

(define (local-variable? r i n)
  (and (pair? r)
    (let scan ((names (car r))
                (j 0))
      (cond ((pair? names)
              (if (eq? n (car names))
                `(local ,i . ,j)
                (scan (cdr names) (+ 1 j))))
        ((null? names)
          (local-variable? (cdr r) (+ i 1) n))
        ((eq? n names) `(local ,i . ,j))))))

(define (meaning e )
  (if (list? e)
    (case (car e)
      ((quote) (meaning-quotation (cadr e) r))
      ((lambda) (meaning-abstraction (cadr e) (cddr e) r))
      ((if) (meaning-alternative (cadr e) (caddr e) (cadddr e) r))
      ((begin) (meaning-sequence (cdr e) r))
      ((set!) (meaning-assignment (cadr e) (caddr e) r))
      (else (meaning-application (car e) (cdr e) r)))
    (if (symbol? e) (meaning-reference e r)
      (meaning-quotation e r))))

(define (meaning-quoteation v r)
  (lambda (sr k)
    (k v)))

(define (meaning-alternative e1 e2 e3 r)
  (let ((m1 (meaning e1 r))
         (m2 (meaning e2 r))
         (m3 (meaning e3 r)))
    (lambda (sr k)
      (m1 sr (lambda (v)
               ((if v m2 m3) sr k))))))

(define (meaning-sequence e+ r)
  (if (pair? e+)
    (if (pair? (cdr e+))
      (meaning*-multiple-sequence (car e+) (cdr e+) r)
      (meaning*-single-sequence (car e+) r))
    (static-wrong "Illegal syntax: (begin)")))

(define (meaning*-single-sequence e r)
  (meaning e r))

(define (meaning*-multiple-sequence e e+ r)
  (let ((m1 (meaning e r))
         (m+ (meaning-sequence e+ r)))
    (lambda (sr k)
      (m1 sr (lambda (v)
               (m+ sr k))))))

(define (meaning-regular-application e e* r)
  (let* ((m (meaning e r))              ; Is the let* necessary here?
          (m* (meaning* e* r (length e*))))
    (lambda (sr k)
      (m sr (lambda (f)
              (if (procedure? f)
                (m* sr (lambda (v*)
                         (f v* k)))
                (wrong "Not a function" f)))))))

(define (meaning* e* r size)            ; ((list term) env) -> activation-frame
  (if (pair? e*)
    (meaning-some-arguments (car e*) (cdr e*) r size)
    (meaning-no-argument r size)))

(define (meaning-no-argument r size)
  (let ((size+1 (+ size 1)))
    (lambda (sr k)
      (let ((v* (make <activation-frame> :size size+1)))
        (k v*)))))

(define (meaning-some-arguments e e* r size)
  (let ((m (meaning e r))
         (m* (meaning* e* size))
         (rank (- size (+ (length e*) 1))))
    (lambda (sr k)
      (m sr (lambda (v)
              (m* sr (lambda (v*)
                       (set! (activation-frame-argument v* rank) v)
                       (k v*))))))))

(define (meaning-fix-abstraction n* e+ r)
  (let* ((arity (length n*))
          (arity+1 (+ arity 1))
          (r2 (r-extend* r n*))
          (m+ (meaning-sequence e+ r2)))
    (lambda (sr k)
      (k (lambda (v* k1)
           (if (= (activation-frame-argument-length v*) arity+1)
             (m+ (sr-extend* sr v*) k1)
             (wrong "Incorrect arity")))))))

(define (compute-kind r n)
  (or (local-variable? r 0 n)
    (global-variable? g.current n)
    (global-variable? g.init n)))

(define (global-variable? g n)
  (let ((var (assq n g)))
    (and (pair? var) (cdr var))))

(define (g.current-extend! n)
  (let ((level (length g.current)))
    (set! g.current (cons (cons n `(global . ,level)) g.current))
    level))

(define (g.init-extend! n)
  (let ((level (length g.init)))
    (set! g.init (cons (cons n `(predefined . ,level)) g.init))
    level))

(define sg.current (make-vector 100))

(define sg.init (make-vector 100))

(define (global-fetch i)
  (vector-ref sg.current i))

(define (global-update! i v)
  (vector-set! sg.current i v))

(define (predefined-fetch i)
  (vector-ref sg.init i))

(define (g.current-initialize! name)
  (let ((kind (compute-kind r.init name)))
    (if kind
      (case (car kind)
        ((global)
          (vector-set! sg.current (cdr kind) undefined-value))
        (else (static-wrong "Wrong redefinition" name)))
      (let ((index (g.current-extend! name)))
        (vector-set! sg.current index undefined-value))))
  name)

(define (g.init-initialize! name value)
  (let ((kind (compute-kind r.init name)))
    (if kind
      (case (car kind)
        ((predefined)
          (vector-set! sg.init (cdr kind) value))
        (else (static-wrong "Wrong redefinition" name)))
      (let ((index (g.init-extend! name)))
        (vector-set! sg.init index value))))
  name)

(define (meaning-reference n r)
  (let ((kind (compute-kind r n)))
    (if kind
      (case (car kind)
        ((local)
          (let ((i (cadr kind))
                 (j (cddr kind)))
            (if (= i 0)
              (lambda (sr k)
                (k (activation-frame-argument sr j)))
              (lambda (sr k)
                (k (deep-fetch sr i j))))))
        ((global)
          (let ((i (cdr kind)))
            (if (eq? (global-fetch i) undefined-value)
              (lambda (sr k)
                (let ((v (global-fetch i)))
                  (if (eq? v undefined-value)
                    (wrong "Uninitialized variable" n)
                    (k v))))
              (lambda (sr k)
                (k (global-fetch i))))))
        ((predefined)
          (let* ((i (cdr kind))
                  (value (predefined-fetch i)))
            (lambda (sr k)
              (k value)))))
      (static-wrong "No such variable" n))))

(define (static-wrong message . culprits)
  (display `(*static-error* ,message . ,culprits)) (newline)
  (lambda (sr k)
    (apply wrong message culprits)))

(define r.init '())

(define sr.init '())

(define (chapter61-interpreter)
  (define (compile e) (meaning e r.init))
  (define (run c) (c sr.init display))
  (define (toplevel)
    (run (compile (read)))
    (toplevel))
  (toplevel))

(definitial t #t)

(definitial f #f)

(definitial nil '())

(defprimitive cons cons 2)

(defprimitive car car 1)

(definitial call/cc
  (let* ((arity 1)
          (arity+1 (+ arity 1)))
    (lambda (v* k)
      (if (= arity+1 (activation-frame-argument-length v*))
        ((activation-frame-argument v* 0)
          (let ((frame (allocate-activation-frame (+ 1 1))))
            (set-activation-frame-argument!
              frame 0
              (lambda (values kk)
                (if (= (activation-frame-argument-length values)
                      arity+1)
                  (k (activation-frame-argument values 0))
                  (wrong "Incorrect arity" 'continuation))))
            frame)
          k)
        (wrong "Incorrect arity" 'call/cc)))))
