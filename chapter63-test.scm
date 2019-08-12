(use gauche.test)

(test-start "chapter63")
(load "./chapter63.scm")

(define (test-evaluate expr)
  (define (compile e) (meaning e r.init #t))
  (define (run thunk)
    (set! *env* sr.init)
    (thunk))
  (run (compile expr)))

(test-section "chapter 6.3 interpreter")

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

(test* "call/cc"
  24
  (test-evaluate '((lambda (n)
                     ((lambda (r k)
                        (call/cc (lambda (c) (set! k c) #f))
                        (set! r (* r n))
                        (set! n (- n 1))
                        (if (= n 1) r (k #f)))
                       1 #f)) 4)))
