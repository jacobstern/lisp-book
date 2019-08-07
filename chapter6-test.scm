(use gauche.test)

(test-start "chapter6")
(load "./chapter6.scm")

(define (test-evaluate expr)
  (define (compile e) (meaning e r.init))
  (define (run c k) (c sr.init k))
  (call/cc (lambda (k) (run (compile expr) k))))

(test-section "chapter 6.1 interpreter")

(test* "pair construction"
  '(1 . 2)
  (test-evaluate '(cons 1 2)))

(test* "lambda with closed application"
  '(1 . 2)
  (test-evaluate '((lambda (x) (cons x 2)) 1)))

(test* "lambda without closed application"
  '(1 . 2)
  (test-evaluate '((lambda (f x) (f x)) (lambda (x) (cons x 2)) 1)))

(test* "conditional"
  '(1 . 2)
  (test-evaluate '((lambda (f l r) (cons (f l) (f r)))
                    (lambda (x) (if x 1 2))
                    t f)))

(test* "set! function argument"
  '(1 . 2)
  (test-evaluate '((lambda (x y) (set! x 1) (cons x y)) 2 2)))

(test* "sequence"
  '(1 . 2)
  (test-evaluate '((lambda (b x y)
                     (if b (begin (set! x 1) (cons x y)) (cons x y)))
                    t 2 2)))
