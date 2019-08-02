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

(test-end :exit-on-failure #t)
