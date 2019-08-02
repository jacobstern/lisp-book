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

(test "multiplication builtin"
  6
  (lambda () (test-evaluate '(* 2 3))))

(test "list constructor"
  '(1 2)
  (lambda () (test-evaluate '(cons 1 (cons 2 nil)))))

(test-end :exit-on-failure #t)
