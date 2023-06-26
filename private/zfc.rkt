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

(define zfc-axioms (list extensionality))


(define zfc (theory zfc-axioms zfc-operators))

; ctx |- (forall z (in z x) <=> (in z y))
; --------------------------------------- Extensionality
; ctx |- (= x y)
(define-rule (Extensionality ctx `(= ,x ,y))
  (assert-context-has-theory zfc)
  (check-proof/defer
   ctx `(= ,x ,y)
   Debug)
  #;
  (list (/- ctx (forall z (<=> (in z x) (in z y))))))

(module+ test
  (check-not-exn
   (lambda ()
     (fresh
      (x y)
      (check-proof
       (theory->context zfc)
       (= x y)
       (Sequence
        Extensionality
        ))))))
