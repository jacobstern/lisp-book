(use gauche.test)

(test-start "chapter6")
(load "./chapter6.scm")

(define (test-evaluate expr)
  (define (compile e) (meanint e r.init))
  (define (run c k) (c sr.init k))
  (call/cc (lambda (k) (run (compile expr) k))))

(test-section "chapter 6.1 interpreter")

(test* "list construction"
  '(1 2)
  (test-evaluate '(cons 1 (cons 2 nil))))
