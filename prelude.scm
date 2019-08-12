;;; Common prelude for compatibility with code from the book

(load "./meroonet.scm")

(define wrong error)

(define (atom? x) (not (list? x)))
