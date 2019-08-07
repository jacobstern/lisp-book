;;; Adapted from https://github.com/appleby/Lisp-In-Small-Pieces

(define-macro (define-meroonet-macro call . body)
  `(define-macro ,call . ,body) )

(define meroonet-error error)

(load "./meroonet/meroonet.scm")
