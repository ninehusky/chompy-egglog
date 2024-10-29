#lang rosette

(require rosette/lib/synthax)

(define-grammar (pred-sketch p q)
  [expr
   (choose ((conj) (expr) (expr))
           ((bop) (val) (val)))]
  [conj (choose && ||)]
  [bop
   (choose >= < =)]
  [val
   (choose (?? integer?) p q)])

(define good-envs
  (list
   (make-hash
    (list (cons 'p 1)
          (cons 'q 2)))
   (make-hash
    (list (cons 'p 1)
          (cons 'q 3)))))

(define bad-envs
  (list
   (make-hash
    (list (cons 'p 1)
          (cons 'q 6)))
   (make-hash
    (list (cons 'p 1)
          (cons 'q 7)))))


;;; gulp
(define (good-pred p q)
  (pred-sketch p q #:depth 2))

(define mod (synthesize
             #:forall (list)
             #:guarantee (begin
                           (for ([good-env good-envs])
                             (assert (good-pred (hash-ref good-env 'p) (hash-ref good-env 'q))))
                           (for ([bad-env bad-envs])
                             (assert (not (good-pred (hash-ref bad-env 'p) (hash-ref bad-env 'q))))))))

(print-forms mod)

(evaluate (good-pred 1 2) mod)

