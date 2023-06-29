#lang racket/base

; peano arithmetic (not in terms of set theory for now)

(require "./core.rkt"
         "./sugar.rkt"
         "./first-order-logic.rkt"
         racket/match
         (for-syntax racket/base))
(module+ test (require rackunit))
(provide)

; operators
(define zero 'zero)
(define (S n) `(S ,n))
(define (nat? n) `(nat? ,n))
(define (add a b) `(add ,a ,b))
(define (mul a b) `(mul ,a ,b))

; axioms

(define succ-equal-axiom
  (forall
   (n m)
   (=> (= (S n) (S m))
       (= n m))))

; other equality axioms are implied by =L =R

(define zero-is-nat-axiom (nat? zero))
(define succ-is-nat-axiom (forall n (=> (nat? n) (nat? (S n)))))

(define-syntax forall-nat
  (syntax-rules ()
    [(_ () body) body]
    [(_ (n) body) (forall (n) (=> (nat? n) body))]
    [(_ (n0 n ...) body)
     (forall (n0 n ...) (=> (conj (nat? n0) (nat? n) ...)
                            body))]
    [(_ n body) (forall (n) (=> (nat? n) body))]))

; ctx |- p[zero/x]   ctx |- (forall n p[n/x] => p[(succ n)/x])
; ------------------------------------------------------- NatInduction
; ctx |- (forall x (=> (nat? x) p))
(define-rule (NatInduction ctx `(forall ,x (=> (nat? ,x) ,p)))
  (list (/- ctx (subst p x zero))
        (/- ctx (forall n (=> (subst p x n)
                              (subst p x (S n)))))))

(define add-zero-axiom
  (forall-nat a (= (add a zero) zero)))
(define add-succ-axiom
  (forall-nat (a b) (= (add a (S b))
                       (S (add a b)))))

(define mul-zero-axiom
  (forall-nat a (= (mul a zero)
                   zero)))

(define mul-succ-axiom
  (forall-nat (a b) (= (mul a (S b))
                       (add a (mul a b)))))

(define peano-axioms (list zero-is-nat-axiom
                           succ-is-nat-axiom
                           add-zero-axiom
                           add-succ-axiom
                           mul-zero-axiom
                           mul-succ-axiom))
(define peano (theory peano-axioms '()))

(module+ test
  (check-not-exn
   (lambda ()
     (check-proof
      (theory->context peano)
      (forall-nat n (nat? n))
      (Branch
       NatInduction
       ; zero-is-nat-axiom
       I
       ; succ-is-nat-axiom
       I)))))
(define-theorem! multiplicative-identity
  peano (forall-nat a (= (mul a (S zero)) a))
  (Branch
   NatInduction
   (Sequence
    (ForallL mul-zero-axiom (S zero))
    (Branch
     (=>L (=> (nat? (S zero)) (= (mul (S zero) zero) zero)))
     Debug
     Debug))
   Debug))
