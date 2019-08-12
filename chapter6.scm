#!/usr/bin/env gosh

;;; Code adapted from Chapter 6 of Lisp in Small Pieces by Christian Quiennec
;;; Requires Gauche Scheme http://practical-scheme.net/gauche/

(use scheme.base)
(load "./prelude.scm")

(define-class environment Object
  (next))

(define-class activation-frame environment
  ((* argument)))

(define (sr-extend* sr v*)
  (set-environment-next! v* sr)
  v*)

(define (deep-fetch sr i j)
  (if (= i 0)
    (activation-frame-argument sr j)
    (deep-fetch (environment-next sr) (- i 1) j)))

(define (deep-update! sr i j v)
  (if (= i 0)
    (set-activation-frame-argument! sr j v)
    (deep-update! (environment-next sr) (- i 1) j v)))

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

(define (meaning e r)
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

(define (meaning-quotation v r)
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
      (let ((v* (allocate-activation-frame size+1)))
        (k v*)))))

(define (meaning-some-arguments e e* r size)
  (let ((m (meaning e r))
         (m* (meaning* e* r size))
         (rank (- size (+ (length e*) 1))))
    (lambda (sr k)
      (m sr (lambda (v)
              (m* sr (lambda (v*)
                       (set-activation-frame-argument! v* rank v)
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

(define g.current '())

(define g.init '())

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

(define (meaning-assignment n e r)
  (let ((m (meaning e r))
         (kind (compute-kind r n)))
    (if kind
      (case (car kind)
        ((local)
          (let ((i (cadr kind))
                 (j (cddr kind)))
            (if (= i 0)
              (lambda (sr k)
                (m sr (lambda (v)
                        (k (set-activation-frame-argument! sr j v)))))
              (lambda (sr k)
                (m sr (lambda (v)
                        (k (deep-update! sr i j v))))))))
        ((global)
          (let ((i (cdr kind)))
            (lambda (sr k)
              (m sr (lambda (v)
                      (k (global-update! i f)))))))
        ((predefined)
          (static-wrong "Immutable predefined variable" n)))
      (static-wrong "No such variable" n))))

(define (static-wrong message . culprits)
  (display `(*static-error* ,message . ,culprits)) (newline)
  (lambda (sr k)
    (apply wrong message culprits)))

(define r.init '())

(define sr.init '())

(define (meaning-dotted-abstraction n* n e+ r)
  (let* ((arity (length n*))
          (arity+1 (+ arity 1))
          (r2 (r-extend* r (append n* (list n))))
          (m+ (meaning-sequence e+ r2)))
    (lambda (sr k)
      (k (lambda (v* k1)
           (if (>= (activation-frame-argument-length v*) arity+1)
             (begin (listify! v* arity)
               (m+ (sr-extend* sr v* k1)))
             (wrong "Incorrect arity")))))))

(define (listify! v* arity)
  (let loop ((index (- (activation-frame-argument-length v*) 1))
              (result '()))
    (if (= arity index)
      (set-activation-frame-argument! v* arity result)
      (loop (- index 1)
        (cons (activation-frame-argument v* (- index 1))
          result)))))

(define (meaning-abstraction nn* e+ r)
  (let parse ((n* nn*)
               (regular '()))
    (cond
      ((pair? n*) (parse (cdr n*) (cons (car n*) regular)))
      ((null? n*) (meaning-fix-abstraction nn* e+ r))
      (else (meaning-dotted-abstraction (reverse regular) n* e+ r)))))

(define (meaning-closed-application e ee* r)
  (let ((nn* (cadr e)))
    (let parse ((n* nn*)
                 (e* ee*)
                 (regular '()))
      (cond ((pair? n*)
              (if (pair? e*)
                (parse (cdr n*) (cdr e*) (cons (car n*) regular))
                (static-wrong "Too less arguments" e ee*)))
        ((null? n*)
          (if (null? e*)
            (meaning-fix-closed-application
              nn* (cddr e) ee* r)
            (static-wrong "Too much arguments" e ee*)))
        (else (meaning-dotted-closed-application
                (reverse regular) n* (cddr e) ee* r))))))

(define (meaning-fix-closed-application n* body e* r)
  (let* ((m* (meaning* e* r (length e*)))
          (r2 (r-extend* r n*))
          (m+ (meaning-sequence body r2)))
    (lambda (sr k)
      (m* sr (lambda (v*)
               (m+ (sr-extend* sr v*) k))))))

(define (meaning-dotted-closed-application n* n body e* r)
  (let* ((m* (meaning-dotted* e* r (length e*) (length n*)))
          (r2 (r-extend* r (append n* (list n))))
          (m+ (meaning-sequence body r2)))
    (lambda (sr k)
      (m* sr (lambda (v*)
               (m+ (sr-extend* sr v*) k))))))

(define (meaning-dotted* e* r size arity)
  (if (pair? e*)
    (meaning-some-dotted-arguments (car e*) (cdr e*) r size arity)
    (meaning-no-dotted-argument r size arity)))

(define (meaning-some-dotted-arguments e e* r size arity)
  (let ((m (meaning e r))
         (m* (meaning-dotted* e* r size arity))
         (rank (- size (+ (length e*) 1))))
    (if (< rank arity)
      (lambda (sr k)
        (m sr (lambda (v)
                (m* sr (lambda (v*)
                         (set-activation-frame-argument! v* rank v)
                         (k v*))))))
      (lambda (sr k)
        (m sr (lambda (v)
                (m* sr (lambda (v*)
                         (set-activation-frame-argument!
                           v* arity
                           (cons v (activation-frame-argument
                                     v* arity)))
                         (k v*)))))))))

(define (meaning-no-dotted-argument r size arity)
  (let ((arity+1 (+ arity 1)))
    (lambda (sr k)
      (let ((v* (allocate-activation-frame arity+1)))
        (set-activation-frame-argument! v* arity '())
        (k v*)))))

(define-syntax definitial
  (syntax-rules ()
    ((definitial name value)
      (g.init-initialize! 'name value))))

(define-syntax defprimitive
  (syntax-rules ()
    ((defprimitive name value 0) (defprimitive0 name value))
    ((defprimitive name value 1) (defprimitive1 name value))
    ((defprimitive name value 2) (defprimitive2 name value))
    ((defprimitive name value 3) (defprimitive3 name value))))

(define-syntax defprimitive0
  (syntax-rules ()
    ((defprimitive0 name value)
      (definitial name
        (letrec ((arity+1 (+ 0 1))
                  (behavior
                    (lambda (v* k)
                      (if (= (activation-frame-argument-length v*)
                            arity+1)
                        (k (value))
                        `(,wrong "Incorrect arity" name)))))
          `(,description-extend!
             name (function ,value a b c))
          behavior)))))

(define-syntax defprimitive1
  (syntax-rules ()
    ((defprimitive1 name value)
      (definitial name
        (letrec ((arity+1 (+ 1 1))
                  (behavior
                    (lambda (v* k)
                      (if (= (activation-frame-argument-length v*)
                            arity+1)
                        (k (value (activation-frame-argument v* 0)))
                        `(,wrong "Incorrect arity" name)))))
          `(,description-extend!
             name (function ,value a b c))
          behavior)))))

(define-syntax defprimitive2
  (syntax-rules ()
    ((defprimitive2 name value)
      (definitial name
        (letrec ((arity+1 (+ 2 1))
                  (behavior
                    (lambda (v* k)
                      (if (= (activation-frame-argument-length v*)
                            arity+1)
                        (k (value (activation-frame-argument v* 0)
                             (activation-frame-argument v* 1)))
                        `(,wrong "Incorrect arity" name)))))
          `(,description-extend!
             name (function ,value a b c))
          behavior)))))

(define-syntax defprimitive3
  (syntax-rules ()
    ((defprimitive3 name value)
      (definitial name
        (letrec ((arity+1 (+ 3 1))
                  (behavior
                    (lambda (v* k)
                      (if (= (activation-frame-argument-length v*)
                            arity+1)
                        (k (value (activation-frame-argument v* 0)
                             (activation-frame-argument v* 1)
                             (activation-frame-argument v* 2)))
                        `(,wrong "Incorrect arity" name)))))
          `(,description-extend!
             name (function ,value a b c))
          behavior)))))

(define desc.init '())

(define (description-extend! name description)
  (set! desc.init (cons (cons name description) desc.init))
  name)

(define (get-description name)
  (let ((p (assq name desc.init)))
    (and (pair? p) (cdr p))))

(define (meaning-application e e* r)
  (cond
    ((and (symbol? e)
       (let ((kind (compute-kind r e)))
         (and (pair? kind)
           (eq? 'predefined (car kind))
           (let ((desc (get-description e)))
             (and desc
               (eq? 'function (car desc))
               (if (= (length (cddr desc)) (length e*))
                 (meaning-primitive-application e e* r)
                 (static-wrong "Incorrect arity for" e))))))))
    ((and (pair? e)
       (eq? 'lambda (car e)))
      (meaning-closed-application e e* r))
    (else (meaning-regular-application e e* r))))

(define (meaning-primitive-application e e* r)
  (let* ((desc (get-description e))     ; desc = (function address . variables-list)
          (address (cadr desc))
          (size (length e*)))
    (case size
      ((0) (lambda (sr k) (k (address))))
      ((1)
        (let ((m1 (meaning (car e*) r)))
          (lambda (sr k)
            (m1 sr (lambda (v)
                     (k (address v)))))))
      ((2)
        (let ((m1 (meaning (car e*) r))
               (m2 (meaning (cadr e*) r)))
          (lambda (sr k)
            (m1 sr (lambda (v1)
                     (m2 sr (lambda (v2)
                              (k (address v1 v2)))))))))
      ((3)
        (let ((m1 (meaning (car e*) r))
               (m2 (meaning (cadr e*) r))
               (m3 (meaning (caddr e*) r)))
          (lambda (sr k)
            (m1 sr (lambda (v1)
                     (m2 sr (lambda (v2)
                              (m3 sr (lambda (v3)
                                       (k (address v1 v2 v3)))))))))))
      (else (meaning-regular-application e e* r)))))

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

