(use gauche.test)

(test-start "chapter5")
(load "./chapter5.scm")

(test-section "cps")

(define (fuzzy-expr-compare l r)
  (cond
    ((and (pair? l) (pair? r))
      (and
        (fuzzy-expr-compare (car l) (car r))
        (fuzzy-expr-compare (cdr l) (cdr r))))
    ((and (eqv? l '_sym) (symbol? r)) #t)
    (else (eqv? l r))))

(test* "cps a complex expression"
  '(set! fact
     (lambda (_sym n)
       (if (= n 1)
         (_sym 1)
         (fact (lambda (_sym) (_sym (* n _sym)))
           (- n 1)))))
  (call/cc (cps '(set! fact (lambda (n)
                              (if (= n 1) 1
                                (* n (fact (- n 1))))))))
  fuzzy-expr-compare)

(test-end :exit-on-failure #t)
