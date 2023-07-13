#lang racket/base

(require "./core.rkt"
         "./sugar.rkt"
         "./first-order-logic.rkt"
         racket/match
         racket/set
         racket/struct)
(module+ test (require rackunit))
(provide)

; operators

(define-operator (in e s))

; axioms/rules

; equality on sets is determined by membership
(define extensionality
  (forall (x y) (=> (forall z (<=> (in z x) (in z y)))
                    (= x y))))

; this breaks if you do (forall x (null-set? x))
(define (null-set? e) (forall x (neg (in x e))))

; every non-empty set x contains a member y such that x and y are disjoint sets
(define regularity
  (forall x (=> (exists a (in a x))
                (exists y (conj (in y x)
                               (neg (exists z (conj (in z y) (in z x)))))))))

; {x in superset : predicate}
; x is bound in predicate
(struct specification^ [x superset predicate] #:transparent
  #:methods gen:formula
  [(define (gen-subst p target replacement)
     (match p
       [(specification^ x superset predicate)
        (specification^ x
                        (subst superset target replacement)
                        (if (occurs-free? x target)
                            predicate
                            (subst predicate target replacement)))]))
   (define (gen-free-vars p)
     (match p
       [(specification^ x superset predicate)
        (set-union (free-vars superset)
                   (set-subtract (free-vars predicate) (list x)))]))
   (define (gen-bound-vars p)
     (match p
       [(specification^ x superset predicate)
        (set-union (list x) (bound-vars superset) (bound-vars predicate))]))
   (define (gen-alpha-normalize p count vars)
     (define v (normal-name count))
     (define count^ (add1 count))
     (match p
       [(specification^ x superset predicate)
        (define vars^ (hash-set vars x v))
        (specification^ v
                        (alpha-normalize superset count vars)
                        (alpha-normalize predicate count^ vars^))]))]
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (_) 'specification)
      (lambda (p) (match p [(specification^ x superset predicate) (list x superset predicate)]))))])
(define-match-expander specification
  (syntax-rules ()
    [(_ x superset predicate)
     (specification^ x superset predicate)])
  (syntax-rules ()
    [(_ x superset predicate)
     (fresh (x) (specification^ x superset predicate))]))

(define-syntax-rule (is-specification? s member superset predicate)
  (forall (member) (<=> (in member s)
                        (conj (in member superset) predicate))))

(define (spec-definition spec)
  (match spec
    [(specification x superset predicate)
     (forall e (<=> (in e spec)
                    (conj (in e superset)
                          (subst predicate x e))))]))

; ctx, forall e (<=> (in e (specification x super pred)) (conj (in e super) pred[e/x]))
(define-rule ((Specification^ (and spec (specification x superset predicate))) ctx p)
  (list (/- (extend-context ctx (spec-definition spec)) p)))

; ctx, (in e spec) => (conj (in e super) pred[e/x]), (conj (in e super) pred[e/x]) => (in e spec)
; e is a term
(define-syntax-rule (Specification (e spec) body ...)
  (Sequence
   (Specification^ spec)
   (ForallL (spec-definition spec)
            (e)
            <=>L
            body ...)))

(define pairing
  (forall (x y) (exists (z) (conj (in x z) (in y z)))))

(define axiom-of-union
  ; A = UF
  (forall F (exists A (forall Y (forall x (=> (conj (in x Y)
                                                   (in Y F))
                                              (in x A)))))))

(define-operator (self-union F))
(define (is-self-union? F uF)
  (forall (Y x) (<=> (in x uF) (conj (in x Y) (in Y F)))))
; TODO unique existence theorem
; TODO axiom
; TODO operator

; TODO replacement

(define-operator (singleton x))
(define (is-singleton? x sx) (forall e (<=> (in e sx) (= e x))))
(define axiom-for-singleton (forall x (is-singleton? x (singleton x))))

(define-operator (U x y))
(define (is-binary-union? x y u)
  (forall e (<=> (in e u) (or (in e x) (in e y)))))
; TODO unique existence theorem
; TODO axiom
; TODO operator
(define-operator (S x))
(define (is-successor? x sx) (= sx (U x (singleton x))))
; TODO unique existence theorem
; TODO axiom
; TODO operator

(define axiom-of-infinity
  (exists X (conj (exists e (conj (null-set? e) (in e X)))
                 (forall y (=> (in y X) (in (S y) X))))))

(define (is-subset? x y)
  (forall e (=> (in e x) (in e y))))

(define axiom-of-power-set
  (forall x (exists px (forall z (=> (is-subset? z x) (in z px))))))

(define-operator (P x))
(define (is-power-set? x px)
  (forall z (<=> (is-subset? z x) (in z px))))
; TODO unique existence theorem
; TODO axiom
; TODO operator

; TODO well-ordering axiom

(define zfc-axioms
  (list extensionality
        regularity
        pairing
        axiom-of-union
        axiom-of-infinity
        axiom-of-power-set
        axiom-for-singleton))

(define zfc (theory zfc-axioms))

; ctx |- (forall z (in z x) <=> (in z y))
; --------------------------------------- Extensionality
; ctx |- (= x y)
(define-rule (Extensionality ctx (= x y))
  (assert-in-context extensionality)
  (check-proof/defer
   ctx (= x y)
   (Sequence
    (ForallL
     extensionality (x y)
     (Branch
      (=>L (=> (forall z (<=> (in z x) (in z y)))
               (= x y)))
      Defer
      I)))))

(module+ test
  (check-not-exn
   (lambda ()
     (fresh
      (x y)
      (check-proof
       (context-union (context (forall z (<=> (in z x) (in z y))))
                      (theory->context zfc))
       (= x y)
       (Sequence
        Extensionality
        I))))))

(define-theorem singleton-unique-existence-theorem
  zfc (forall x (exists! sx (is-singleton? x sx)))
  (ForallR
   (x)
   (QuantL
    pairing
    ([forall x]
     [forall x]
     [exists xx])
    AndL
    (Exists!R ((specification e xx (= e x)) sx)
              (Sequence
               Extensionality
               (ForallR
                (z)
                (Branch
                 <=>R
                 ; spec subset sx
                 (Specification
                  (z (specification e xx (= e x)))
                  (Branch
                   (=>L (=> (in z (specification e xx (= e x)))
                            (conj (in z xx) (= z x))))
                   I
                   (Sequence
                    AndL
                    (=L z x)
                    ; now to prove x in sx
                    (ForallL (forall e (<=> (in e sx) (= e x)))
                             (x)
                             <=>L
                             (Branch
                              (=>L (=> (= x x) (in x sx)))
                              =R
                              I)))))
                 ; sx subset spec
                 ; z = x
                 (ForallL (forall e (<=> (in e sx) (= e x)))
                          (z)
                          <=>L
                          (Branch
                           (=>L (=> (in z sx) (= z x)))
                           I
                           (Sequence
                            (=L z x)
                            (Specification (x (specification e xx (= e x)))
                                           (Branch
                                            (=>L (=> (conj (in x xx) (= x x))
                                                     (in x (specification e xx (= e x)))))
                                            (Branch AndR I =R)
                                            I))))))))
              (ForallR
               (z)
               (=L sx (specification e xx (= e x)))
               (Specification (z (specification e xx (= e x)))
                              (Branch
                               <=>R
                               (Branch
                                (=>L (=> (in z (specification e xx (= e x)))
                                         (conj (in z xx) (= z x))))
                                I
                                (Sequence AndL I))
                               (Sequence
                                (=L z x)
                                (Specification (x (specification e xx (= e x)))
                                           (Branch
                                            (=>L (=> (conj (in x xx) (= x x))
                                                     (in x (specification e xx (= e x)))))
                                            (Branch AndR I =R)
                                            I))))))))))
