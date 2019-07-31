(use gauche.test)

(test-start "chapter3")
(load "./chapter3.scm")

(define (test-evaluate expr)
  (call/cc (lambda (cont)
             (evaluate expr r.init (make-bottom-cont 'void cont)))))

(test-section "basic interpreter")

(test "pair construction" '(42)
  (lambda () (test-evaluate '(cons 42 '()))))

(test "function application" 3
  (lambda () (test-evaluate '((lambda (x) x) 3))))

(test-section "side effects")

(test "can set! a function parameter"
  5
  (lambda () (test-evaluate
               '((lambda (x) (set! x 5) x) 3))))

(test-section "call/cc")

(test "basic use of continuation"
  2
  (lambda () (test-evaluate '(call/cc (lambda (k) (k 2))))))

(test-section "unwind-protect")

(test "cleanup form is evaluated"
  2
  (lambda () (test-evaluate '((lambda (c)
                                (unwind-protect 'void (set! c 2))
                                c)
                               0))))

(test "cleanup form is evaluated with throw/catch"
  5
  (lambda () (test-evaluate
               '((lambda (x y)
                   (catch 'x (unwind-protect
                               (begin
                                 (throw 'x 'something)
                                 (set! y 3))
                               (set! x 4)))
                   (+ x y)) 3 1))))

(test-end :exit-on-failure #t)
