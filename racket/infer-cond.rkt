#lang rosette

(require rosette/lib/synthax)
(require rosette/lib/destruct)
(require json)

(define env-filepath (make-parameter #f))

(command-line
 #:program "infer condition"
 #:once-each  ["--env-filepath"
               v
               "File containing modules with good/bad examples."
               (begin
                 ; Error if file doesn't exist.
                 (when (not (file-exists? v))
                   (error (format "File ~a does not exist." v)))
                 (env-filepath v))])

(unless (env-filepath)
  (error "No environment file provided."))

(define envs (call-with-input-file (env-filepath) read-json))

(unless (jsexpr? envs)
  (error (format "~a is not a valid JSON." (env-filepath))))

(define-grammar (pred-sketch-arity-1 p)
  [expr
   (choose ((conj) (expr) (expr))
           ((bop) (val) (val)))]
  [conj (choose && ||)]
  [bop
   (choose >= < =)]
  [val
   (choose (?? integer?) p)])

(define-grammar (pred-sketch-arity-2 p q)
  [expr
   (choose ((conj) (expr) (expr))
           ((bop) (val) (val)))]
  [conj (choose && ||)]
  [bop
   (choose >= < =)]
  [val
   (choose (?? integer?) p q)])

(define-grammar (pred-sketch-arity-3 p q r)
  [expr
   (choose ((conj) (expr) (expr))
           ((bop) (val) (val)))]
  [conj (choose && ||)]
  [bop
   (choose >= < =)]
  [val
   (choose (?? integer?) p q r)])

(define good-envs (hash-ref envs 'good_envs))
(define bad-envs (hash-ref envs 'bad_envs))
(define bitwidths (hash-ref envs 'bitwidths))

(define (condition1 p) (pred-sketch-arity-1 p #:depth 2))
(define (condition2 p q) (pred-sketch-arity-2 p q #:depth 2))
(define (condition3 p q r) (pred-sketch-arity-3 p q r #:depth 2))
(define (find-1-arg-condition)
  (solve
   (begin
     (for ([good-env good-envs])
       (assert (condition1 (hash-ref good-env (string->symbol (first bitwidths))))))
     (for ([bad-env bad-envs])
       (assert (not (condition1 (hash-ref bad-env (string->symbol (first bitwidths)))))))

     (for ([symbolic (symbolics (condition1 (hash-ref (first good-envs) (string->symbol (first bitwidths)))))])
       (when (integer? symbolic) (assert (not (negative? symbolic))))))))

(define (find-2-arg-condition)
  (solve
   (begin
     (for ([good-env good-envs])
       (assert (condition2 (hash-ref good-env (string->symbol (first bitwidths)))
                           (hash-ref good-env (string->symbol (second bitwidths))))))
     (for ([bad-env bad-envs])
       (assert (not (condition2 (hash-ref bad-env (string->symbol (first bitwidths)))
                                (hash-ref bad-env (string->symbol (second bitwidths)))))))
     (for ([symbolic (symbolics (condition2 (hash-ref (first good-envs) (string->symbol (first bitwidths)))
                                            (hash-ref (first good-envs) (string->symbol (second bitwidths)))))])
       (when (integer? symbolic) (assert (not (negative? symbolic))))))))

(define (find-3-arg-condition)
  (synthesize
   #:forall (list)
   #:guarantee (begin
                 (for ([good-env good-envs])
                   (assert (condition3 (hash-ref good-env (string->symbol (first bitwidths)))
                                       (hash-ref good-env (string->symbol (second bitwidths)))
                                       (hash-ref good-env (string->symbol (third bitwidths))))))
                 (for ([bad-env bad-envs])
                   (assert (not (condition3 (hash-ref bad-env (string->symbol (first bitwidths)))
                                            (hash-ref bad-env (string->symbol (second bitwidths)))))))

                 (for ([symbolic (symbolics (condition3 (hash-ref (first good-envs) (string->symbol (first bitwidths)))
                                                        (hash-ref (first good-envs) (string->symbol (second bitwidths)))
                                                        (hash-ref (first good-envs) (string->symbol (third bitwidths)))))])
                   (when (integer? symbolic) (assert (not (negative? symbolic))))))))

(print-forms (match (length bitwidths)
               [1 (find-1-arg-condition)]
               [2 (find-2-arg-condition)]
               [3 (find-3-arg-condition)]
               [_ (error "Invalid number of bitwidths.")]))
