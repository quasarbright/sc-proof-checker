#lang racket/base

(require "./core.rkt"
         "./sugar.rkt"
         "./first-order-logic.rkt")
(module+ test (require rackunit))
(provide)

; operators

(define (in e s) (list 'in e s))

(define zfc-operators (list (operator 'in 2)))

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

(define-syntax-rule (is-specification? s member superset predicate)
  (forall (member) (<=> (in member s)
                        (conj (in member superset) predicate))))

; --------------------------------------------------------------- Specification
; ctx |- (exists y (forall x (<=> (in x y) (and (in x z) pred))))
; You can specify a set by specifying a superset and a predicate
(define-rule (Specification ctx `(exists ,y (forall ,x (and (=> (in ,x ,y) (and (in ,x ,z) ,pred))
                                                            (=> (and (in ,x ,z) ,pred) (in ,x ,y))))))
  '())

(define pairing
  (forall (x y) (exists (z) (conj (in x z) (in y z)))))

(define axiom-of-union
  (forall F (exists A (forall Y (forall x (=> (conj (in x Y)
                                                   (in Y F))
                                              (in x A)))))))

(define (self-union F) `(self-union ,F))
(define (is-self-union? F uF)
  (forall (Y x) (<=> (in x uF) (conj (in x Y) (in Y F)))))
; TODO unique existence theorem
; TODO axiom
; TODO operator

; TODO replacement

(define (singleton x) `(singleton ,x))
(define (is-singleton? x sx) (forall e (<=> (in e sx) (= e x))))
(define axiom-for-singleton (forall x (is-singleton? x (singleton x))))
; TODO unique existence theorem
; TODO operator
(define (U x y) `(U ,x ,y))
(define (is-binary-union? x y u)
  (forall e (<=> (in e u) (or (in e x) (in e y)))))
; TODO unique existence theorem
; TODO axiom
; TODO operator
(define (S x) `(S ,x))
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

(define (P x) `(P ,x))
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

(define zfc (theory zfc-axioms zfc-operators))

; ctx |- (forall z (in z x) <=> (in z y))
; --------------------------------------- Extensionality
; ctx |- (= x y)
(define-rule (Extensionality ctx `(= ,x ,y))
  (assert-in-context extensionality)
  (check-proof/defer
   ctx `(= ,x ,y)
   (Sequence
    (ForallL extensionality x)
    (ForallL (forall (y) (=> (forall z (<=> (in z x) (in z y)))
                             (= x y)))
             y)
    (Branch
     (=>L (=> (forall z (<=> (in z x) (in z y)))
              (= x y)))
     Defer
     I))))

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

(define-theorem! singleton-unique-existence-theorem
  zfc (forall x (exists! sx (is-singleton? x sx)))
  (ForallR
   (x)
   (Cuts
    ([(exists xx (conj (in x xx) (in x xx)))
      ; actually, use pairing
      (Sequence
       (ForallL pairing x)
       (ForallL (forall y (exists z (conj (in x z) (in y z)))) x)
       I)])
    (Sequence
     (ExistsL
      ([(exists xx (conj (in x xx) (in x xx))) xx])
      (Cuts
       ([(exists sx (is-specification? sx e xx (= x e))) Specification])
       (ExistsL
        ([(exists sx (is-specification? sx e xx (= x e))) sx])
        (Sequence
         (ExistsR sx)
         (ForallR (y) ; same as sx
                  (Branch
                   AndR
                   (Sequence
                    =>R
                    Debug)
                   (Sequence
                    =>R
                    (=L y sx)
                    Debug)))
         )))
              #;
              Specification)))))

#;#;
(let ([x:31 'x:31])
 (exists
  sx:28
  (forall
   y:29
   (and (=> (is-singleton? x:31 y:29)
            (= sx:28 y:29))
        (=> (= sx:28 y:29)
            (is-singleton? x:31 y:29))))))

(forall e:41 (and (=> (in e:41 sx:39) (and (in e:41 xx:35) (= x:31 e:41)))
                  (=> (and (in e:41 xx:35) (= x:31 e:41)) (in e:41 sx:39))))
#;
(forall y:29 (and (=> (forall
                       e:30
                       (and (=> (in e:30 y:29) (= e:30 x:31))
                            (=> (= e:30 x:31) (in e:30 y:29))))
                      (= sx:39 y:29))
                  (=> (= sx:39 y:29)
                      (forall
                       e:30
                       (and (=> (in e:30 y:29) (= e:30 x:31))
                            (=> (= e:30 x:31) (in e:30 y:29)))))))
