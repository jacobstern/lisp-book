(use gauche.test)

(test-start "chapter4")
(load "./chapter4.scm")

(define (test-evaluate expr)
  (call/cc (lambda (cont)
             (evaluate expr
               r.global
               s.global
               (lambda (v ss)
                 (cont (transcode-back v ss)))))))

(test-section "basic interpreter")

(test "single multiplication expression"
  6
  (lambda () (test-evaluate '(* 2 3))))

(test "list constructor"
  '(#t #f)
  (lambda () (test-evaluate '(cons t (cons f nil)))))

(test "empty list"
  '()
  (lambda () (test-evaluate 'nil)))

(test "basic use of (car ...)"
  #t
  (lambda () (test-evaluate '(car (cons t nil)))))

(test-section "side effects")

(test "set! function argument"
  #t
  (lambda () (test-evaluate '((lambda (x) (set! x t) x) nil))))

(test "conditional set!"
  '(2 . 4)
  (lambda () (test-evaluate '((lambda (fn) (cons (fn 2 t) (fn 2 f)))
                               (lambda (x b)
                                 (if b x (begin (set! x (* x 2)) x)))))))

(test-end :exit-on-failure #t)
