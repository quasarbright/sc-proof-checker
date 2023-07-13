#lang racket/base

(require "./core.rkt"
         "./sugar.rkt"
         "./first-order-logic.rkt"
         racket/match
         racket/set
         racket/struct)
(module+ test (require rackunit))
(provide (all-defined-out))

; operators

(define-operator (in e s))

; axioms/rules

; equality on sets is determined by membership
(define axiom-of-extensionality
  (forall (x y) (=> (forall z (<=> (in z x) (in z y)))
                    (= x y))))

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

(define axiom-of-pairing
  (forall (x y) (exists (z) (conj (in x z) (in y z)))))

(define axiom-of-union
  ; A = UF
  (forall F (exists A (forall Y (forall x (=> (conj (in x Y)
                                                   (in Y F))
                                              (in x A)))))))

(define-operator (self-union F))
(define (is-self-union? F uF)
  (forall (Y x) (<=> (in x uF) (conj (in x Y) (in Y F)))))
(define self-union-definition
  (forall (F) (is-self-union? F (self-union F))))

; TODO replacement

(define-operator (U x y))
(define (is-binary-union? x y u)
  (forall e (<=> (in e u) (disj (in e x) (in e y)))))
(define binary-union-definition
  (forall (x y) (is-binary-union? x y (U x y))))

(define-operator (self-intersection F))
(define (is-self-intersection? F iF)
  (forall (x) (<=> (in x iF) (forall (Y) (=> (in Y F) (in x Y))))))
(define self-intersection-definition
  (forall (F) (is-self-intersection? F (self-intersection F))))

(define-operator (binary-intersection x y))
(define (is-binary-intersection? x y i)
  (forall (e) (<=> (in e i) (conj (in e x) (in e y)))))
(define binary-intersection-definition
  (forall (x y) (is-binary-intersection? x y (binary-intersection x y))))

#;#;#;
(define-operator (singleton x))
(define (is-singleton? x sx) (forall e (<=> (in e sx) (= e x))))
(define axiom-for-singleton (forall x (is-singleton? x (singleton x))))

(define empty-set 'empty-set)
(define empty-set-definition
  (forall (x) (neg (in x empty-set))))

(define (disjoint? x y)
  (= empty-set (binary-intersection x y)))

; every non-empty set x contains a member y such that x and y are disjoint sets
(define axiom-of-regularity
  (forall x (=> (exists a (in a x))
                (exists y (conj (in y x)
                                (disjoint? x y))))))

(define-variadic-operator make-set elements)

; ctx,x in {x,y,...}, y in {x,y,...},..., (forall z (z in {x,y,...}) => z = x or z = y or ...)
(define-rule ((MakeSet (and ms (make-set xs ...))) ctx p)
  (define memberships
    (for/list ([x xs])
      (in x ms)))
  (define converse
    (match xs
      ['() (= ms empty-set)]
      [(list x) (forall (z) (<=> (in z ms) (= z x)))]
      [_ (forall (z) (<=> (in z ms) (apply disj (for/list ([x xs]) (= z x)))))]))
  (list (/- (context-union (apply context converse memberships) ctx) p)))

(define-operator (S x))
(define (is-successor? x sx) (= sx (U x (make-set x))))
(define successor-definition
  (forall (x) (is-successor? x (S x))))

(define axiom-of-infinity
  (exists X (conj (in empty-set X)
                  (forall y (=> (in y X) (in (S y) X))))))

; no need for an operator
(define (is-subset? x y)
  (forall e (=> (in e x) (in e y))))

(define axiom-of-power-set
  (forall x (exists px (forall z (=> (is-subset? z x) (in z px))))))

(define-operator (P x))
(define (is-power-set? x px)
  (forall z (<=> (is-subset? z x) (in z px))))
(define powerset-definition
  (forall (x) (is-power-set? x (P x))))

; TODO well-ordering axiom/choice

(define zfc-axioms
  (list axiom-of-extensionality
        axiom-of-regularity
        axiom-of-pairing
        axiom-of-union
        axiom-of-infinity
        axiom-of-power-set

        self-union-definition
        binary-union-definition
        self-intersection-definition
        binary-intersection-definition
        successor-definition
        empty-set-definition
        powerset-definition))

(define zfc (theory zfc-axioms))

; ctx |- (forall z (in z x) <=> (in z y))
; --------------------------------------- Extensionality
; ctx |- (= x y)
(define-rule (Extensionality ctx (= x y))
  (assert-in-context axiom-of-extensionality)
  (check-proof/defer
   ctx (= x y)
   (Sequence
    (ForallL
     axiom-of-extensionality (x y)
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

(define-theorem no-self-containing-sets
  zfc (forall x (neg (in x x)))
  (ForallR (x)
           (MakeSet (make-set x))
           NotR
           (ForallL axiom-of-regularity ((make-set x))
                    (Branch (=>L (=> (exists a (in a (make-set x)))
                                     (exists y (conj (in y (make-set x)) (disjoint? (make-set x) y)))))
                            (ExistsR (x)
                                     I)
                            (Sequence
                             (QuantL (exists y (conj (in y (make-set x)) (disjoint? (make-set x) y))) ([exists y])
                                     AndL
                                     (Cuts ([(= y x)
                                             (QuantL (forall z (<=> (in z (make-set x)) (= z x)))
                                                     ([forall y])
                                                     <=>L
                                                     (Branch
                                                      (=>L (=> (in y (make-set x)) (= y x)))
                                                      I
                                                      I))])
                                           ; use def of empty set and the definition of binary intersection
                                           (=LL (= empty-set (binary-intersection (make-set x) y)) y x)
                                           (QuantL binary-intersection-definition ([forall (make-set x)] [forall x] [forall x])
                                                   <=>L
                                                   (QuantL empty-set-definition ([forall x])
                                                           (=LL (neg (in x empty-set)) empty-set (binary-intersection (make-set x) x))
                                                           (NotL (in x (binary-intersection (make-set x) x)))
                                                           (Branch
                                                            (=>L (=> (conj (in x (make-set x)) (in x x))
                                                                     (in x (binary-intersection (make-set x) x))))
                                                            (Branch AndR I I)
                                                            I))))))))))

#;
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
