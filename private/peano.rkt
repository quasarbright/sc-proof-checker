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

; ctx |- (nat? n)
; ------------------- SuccNat
; ctx |- (nat? (S n))
(define-rule (SuccNat ctx (and p `(nat? (S ,n))))
  (assert-in-context succ-is-nat-axiom)
  (check-proof/defer
   ctx p
   (Sequence
    (ForallL
     succ-is-nat-axiom
     (n)
     (Branch
      (=>L (inst succ-is-nat-axiom n))
      Defer
      I)))))

; used for inductive theorems
(define-syntax forall-nat
  (syntax-rules ()
    [(_ () body) body]
    [(_ (n0 n ...) body)
     (forall (n0) (=> (nat? n0)
                      (forall-nat (n ...) body)))]
    [(_ n body) (forall-nat (n) body)]))

; ctx |- p[zero/x]   ctx |- (forall n ((nat? n) and p[n/x]) => p[(succ n)/x])
; --------------------------------------------------------------------------- NatInduction
; ctx |- (forall x (=> (nat? x) p))
(define-rule (NatInduction ctx `(forall ,x (=> (nat? ,x) ,p)))
  (list (/- ctx (subst p x zero))
        (/- ctx (forall n (=> (conj (nat? n) (subst p x n))
                              (subst p x (S n)))))))

(define add-zero-axiom
  (forall a (= (add a zero) a)))
(define add-succ-axiom
  (forall (a b) (= (add a (S b))
                       (S (add a b)))))

; (add n 0) ~> n
(define-rule ((AddZero n) ctx p)
  (assert-in-context add-zero-axiom)
  (check-proof/defer
   ctx p
   (ForallL
    add-zero-axiom
    (n)
    (Sequence
     (=L (add n zero) n)
     Defer))))

; (add a (S b)) ~> (S (add a b))
(define-rule ((AddSucc a b) ctx p)
  (assert-in-context add-succ-axiom)
  (check-proof/defer
   ctx p

   (ForallL add-succ-axiom (a b)
            (Sequence
             (=L (add a (S b)) (S (add a b)))
             Defer))))

(define mul-zero-axiom
  (forall a (= (mul a zero)
                   zero)))
(define mul-succ-axiom
  (forall (a b) (= (mul a (S b))
                       (add a (mul a b)))))

; (mul n 0) ~> 0
(define-rule ((MulZero n) ctx p)
  (assert-in-context mul-zero-axiom)
  (check-proof/defer
   ctx p
   (ForallL
    mul-zero-axiom
    (n)
    (Sequence
     (=L (mul n zero) zero)
     Defer))))

; (mul a (S b)) ~> (add a (mul a b))
(define-rule ((MulSucc a b) ctx p)
  (assert-in-context mul-succ-axiom)
  (check-proof/defer
   ctx p
   (Sequence
    (ForallL
     mul-succ-axiom
     (a b)
     (Sequence
      (=L (mul a (S b)) (add a (mul a b)))
      Defer)))))

(define peano-axioms (list zero-is-nat-axiom
                           succ-is-nat-axiom
                           add-zero-axiom
                           add-succ-axiom
                           mul-zero-axiom
                           mul-succ-axiom))

(define peano (theory peano-axioms (list)))

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
       (Sequence
        (ForallR
         (n)
         (Sequence
          =>R
          AndL
          (ForallL succ-is-nat-axiom (n)
                   (Branch
                    (=>L (=> (nat? n) (nat? (S n))))
                    I
                    I))))))))))

(define-theorem! additive-closure
  peano (forall-nat (a b) (nat? (add a b)))
  (ForallNatR
   (a)
   (Branch
    NatInduction
    (Sequence
     (AddZero a)
     I)
    (ForallR
     (n)
     (Sequence
      =>R
      AndL
      (Sequence
       (AddSucc a n)
       SuccNat
       I))))))

; ctx |- (nat? a)   ctx |- (nat? b)
; --------------------------------- AddNat
; ctx |- (nat? (add a b))
(define-rule (AddNat ctx (and p `(nat? (add ,a ,b))))
  (assert-in-context additive-closure)
  (check-proof/defer
   ctx p
   (ForallL
    additive-closure
    (a)
    (Branch
     (=>L (inst additive-closure a))
     Defer
     (ForallL
      (forall-nat b (nat? (add a b)))
      (b)
      (Branch
       (=>L (=> (nat? b) (nat? (add a b))))
       Defer
       I))))))

(define-theorem! multiplicative-closure
  peano (forall-nat (a b) (nat? (mul a b)))
  (ForallNatR
   (a)
   (Branch
    NatInduction
    (Sequence
     (MulZero a)
     I)
    (ForallR
     (n)
     (Sequence
      =>R
      AndL
      (Sequence
       (MulSucc a n)
       (Branch
        AddNat
        I
        I)))))))

; ctx |- (nat? a)   ctx |- (nat? b)
; --------------------------------- MulNat
; ctx |- (nat? (mul a b))
(define-rule (MulNat ctx (and p `(nat? (mul ,a ,b))))
  (assert-in-context multiplicative-closure)
  (check-proof/defer
   ctx p
   (ForallL
    multiplicative-closure
    (a)
    (Branch
     (=>L (inst multiplicative-closure a))
     Defer
     (ForallL
      (forall-nat b (nat? (mul a b)))
      (b)
      (Branch
       (=>L (=> (nat? b) (nat? (mul a b))))
       Defer
       I))))))

; checked auto rule for proving a natural
; pretty cool
(define-rule (NatR ctx (and p `(nat? ,n)))
  (match n
    [(== zero alpha-eqv?)
     (assert-in-context zero-is-nat-axiom)
     (check-proof/defer ctx p I)]
    [`(S ,_)
     (assert-in-context succ-is-nat-axiom)
     (check-proof/defer
      ctx p
      (Sequence SuccNat NatR))]
    [`(mul ,_ ,_)
     (assert-in-context multiplicative-closure)
     (check-proof/defer
      ctx p
      (Branch MulNat NatR NatR))]
    [`(add ,_ ,_)
     (assert-in-context additive-closure)
     (check-proof/defer
      ctx p
      (Branch AddNat NatR NatR))]
    [_ (check-proof/defer
        ctx p
        (if (in-context? (nat? n))
            I
            Defer))]))

; (nat? t) obvious in ctx   ctx, p[t/n] |- q
; ------------------------------------------ ForallNatL^
; ctx,(forall n (=> (nat? n) p)) |- q
(define-rule ((ForallNatL^ (and p-forall-nat `(forall ,n (=> (nat? ,n) ,_))) t) ctx p)
  (check-proof/defer
   ctx p
   (ForallL p-forall-nat (t)
            (Branch
             (=>L (inst p-forall-nat t))
             (NoSubproofs! NatR)
             Defer))))

(define-syntax ForallNatL
  (syntax-rules ()
    [(ForallNatL _ () proof) proof]
    [(ForallNatL p (t0 t ...) proof)
     (let ([pv p]
           [tv t0])
       (Sequence
        (ForallNatL^ pv tv)
        (ForallNatL (inst/nat pv tv) (t ...) proof)))]))

; for when you don't need to use induction
(define-syntax ForallNatR
  (syntax-rules ()
    [(_ () proof) proof]
    [(_ (x0 x ...) proof)
     (ForallR (x0) (Sequence =>R (ForallNatR (x ...) proof)))]))

; like inst, but gets rid of the nat impl and only for foralls
(define (inst/nat p replacement)
  (match p
    [`(forall ,n (=> (nat? ,n) ,p))
     (subst p n replacement)]
    [_ (error 'inst/nat "formula not a forall-nat: ~a" p)]))

(define-theorem! additive-commutativity
  peano (forall-nat a (forall-nat b (= (add a b) (add b a))))
  (Branch
   NatInduction
   (Branch
    NatInduction
    =R
    (ForallR
     (n)
     (Sequence
      =>R
      (Cuts
       ([(= (add zero (S n)) (S n))
         (Sequence
          (AddSucc zero n)
          (=L (add zero n) (add n zero))
          (AddZero n)
          =R)]
        [(= (add (S n) zero) (S n))
         (Sequence
          (AddZero (S n))
          =R)])
       (Sequence
        (=L (add zero (S n)) (S n))
        (=L (add (S n) zero) (S n))
        =R)))))
   (ForallR
    (n)
    (Sequence
     =>R
     AndL
     (Branch
      NatInduction
      ; duplicated proof kind of
      (Cuts
       ([(= (add (S n) zero) (S n))
         (Sequence
          (AddZero (S n))
          =R)]
        [(= (add zero (S n)) (S n))
         (Sequence
          (AddSucc zero n)
          (ForallNatL (forall-nat b (= (add n b) (add b n)))
                      (zero)
                      (Sequence
                       (=L (add zero n) (add n zero))
                       (AddZero n)
                       =R)))])
       (Sequence
        (=L (add (S n) zero) (S n))
        (=L (add zero (S n)) (S n))
        =R))
      (ForallR
       (m)
       (Sequence
        =>R
        AndL
        ; get left side to (S (S (m + n)))
        (AddSucc (S n) m)
        (=L (add (S n) m) (add m (S n)))
        (AddSucc m n)
        ; get right side to (S (S (m + n)))
        (AddSucc (S m) n)
        (ForallNatL (forall-nat b (= (add n b) (add b n)))
                    ((S m))
                    (Sequence
                     (=L (add (S m) n) (add n (S m)))
                     (ForallL add-succ-axiom (n m)
                              (Sequence
                               (=L (add n (S m)) (S (add n m)))
                               (ForallNatL (forall-nat b (= (add n b) (add b n))) (m)
                                           (Sequence
                                            (=L (add n m) (add m n))
                                            =R)))))))))))))

; ctx |- p[(add b a)/(add a b)]
; ----------------------------- AddCommute
; ctx |- p
; NOTE (nat? a) and (nat? b) must be obvious in ctx
(define-rule ((AddCommute a b) ctx p)
  (assert-in-context additive-commutativity)
  (check-proof/defer
   ctx p
   (Sequence
    (ForallNatL additive-commutativity (a b)
                (Sequence
                 (=L (add a b) (add b a))
                 Defer)))))

(define-theorem! additive-associativity
  peano (forall-nat a (forall-nat b (forall-nat c (= (add a (add b c))
                                                     (add (add a b) c)))))
  (Branch
   NatInduction
   (Sequence
    (ForallR
     (b)
     (Sequence
      =>R
      (ForallR
       (c)
       (Sequence
        =>R
        (AddCommute zero (add b c))
        (AddZero (add b c))
        (AddCommute zero b)
        (AddZero b)
        =R)))))
   (ForallR
    (n)
    (Sequence
     =>R
     AndL
     (ForallNatR
      (b c)
      (Sequence
       (AddCommute (S n) (add b c))
       (AddSucc (add b c) n)
       (AddCommute (S n) b)
       (AddSucc b n)
       (AddCommute (S (add b n)) c)
       (AddSucc c (add b n))
       (AddCommute (add b c) n)
       (AddCommute c (add b n))
       (AddCommute b n)
       (ForallNatL (forall-nat b (forall-nat c (= (add n (add b c))
                                                  (add (add n b) c))))
                   (b c)
                   (Sequence
                    (=L (add n (add b c))
                        (add (add n b) c))
                    =R))))))))

; (add (add a b) c) ~> (add a (add b c))
; here the R suffix just means associate to the right
(define-rule ((AddAssocR a b c) ctx p)
  (assert-in-context additive-associativity)
  (check-proof/defer
   ctx p
   (Sequence
    (ForallNatL additive-associativity (a b c)
                (Sequence
                 (=L (add (add a b) c)
                     (add a (add b c)))
                 Defer)))))

; (add a (add b c)) ~> (add (add a b) c)
; here the L suffix just means associate to the left
(define-rule ((AddAssocL a b c) ctx p)
  (assert-in-context additive-associativity)
  (check-proof/defer
   ctx p
   (Sequence
    (ForallNatL additive-associativity (a b c)
                (Sequence
                 (=L (add a (add b c))
                     (add (add a b) c))
                 Defer)))))

(define-theorem! multiplicative-commutativity
  peano (forall-nat a (forall-nat b (= (mul a b) (mul b a))))
  (Branch
   NatInduction
   (Sequence
    (Branch
     NatInduction
     =R
     (ForallR
      (n)
      ; prove 0n = n0 => 0(S n) = (S n)0
      (Sequence
       =>R
       AndL
       ; assume 0n = n0
       (Cuts
        ([(= (mul zero (S n)) zero)
          (Sequence
           (MulSucc zero n)
           (=L (mul zero n) (mul n zero))
           (MulZero n)
           (AddZero zero)
           =R)]
         [(= (mul (S n) zero) zero)
          (Sequence (MulZero (S n)) =R)])
        (Sequence
         (=L (mul zero (S n)) zero)
         (=L (mul (S n) zero) zero)
         =R))))))
   (Sequence
    (ForallR
     (n)
     (Sequence
      =>R
      AndL
      (Branch
       NatInduction
       ; prove (S n)0 = 0(S n)
       (Cuts
        ([(= (mul (S n) zero) zero)
          (Sequence
           (MulZero (S n))
           =R)]
         [(= (mul zero (S n)) zero)
          ; get it to (add zero (mul zero n)), then use inductive assumption
          (Sequence
           (MulSucc zero n)
           (AddCommute zero (mul zero n))
           (AddZero (mul zero n))
           (ForallNatL (forall-nat b (= (mul n b) (mul b n)))
                       (zero)
                       (Sequence
                        (=L (mul zero n) (mul n zero))
                        (MulZero n)
                        =R)))])
        (Sequence
         (=L (mul (S n) zero) zero)
         (=L (mul zero (S n)) zero)
         =R))
       (ForallR
        (m)
        (Sequence
         =>R
         AndL
         ; get succs out of mul on both sides
         (MulSucc (S n) m)
         (=L (mul (S n) m) (mul m (S n)))
         (AddCommute (S n) (mul m (S n)))
         (MulSucc m n)
         (AddSucc (add m (mul m n)) n)
         ; now right side
         (MulSucc (S m) n)
         (ForallNatL (forall-nat b (= (mul n b) (mul b n)))
                     ((S m))
                     (Sequence
                      (=L (mul (S m) n) (mul n (S m)))
                      (MulSucc n m)
                      (AddCommute (S m) (add n (mul n m)))
                      (AddSucc (add n (mul n m)) m)
                      (AddCommute m (mul m n))
                      (AddAssocR (mul m n) m n)

                      (AddCommute n (mul n m))
                      (AddAssocR (mul n m) n m)

                      (AddCommute m n)

                      (ForallNatL (forall-nat b (= (mul n b) (mul b n)))
                                  (m)
                                  (Sequence
                                   (=L (mul m n) (mul n m))
                                   =R))))))))))))

; (mul a b) ~> (mul b a)
(define-rule ((MulCommute a b) ctx p)
  (assert-in-context multiplicative-commutativity)
  (check-proof/defer
   ctx p
   (Sequence
    (ForallNatL multiplicative-commutativity (a b)
                (Sequence
                 (=L (mul a b) (mul b a))
                 Defer)))))

(define-theorem! multiplicative-identity
  peano (forall-nat a (= (mul a (S zero)) a))
  (ForallNatR
   (a)
   (Sequence
    (MulSucc a zero)
    (MulZero a)
    (AddZero a)
    =R)))

; (mul n 1) ~> n
(define-rule ((MulOne n) ctx p)
  (assert-in-context multiplicative-identity)
  (check-proof/defer
   ctx p
   (Sequence
    (ForallNatL multiplicative-identity (n)
                (Sequence
                 (=L (mul n (S zero))
                     n)
                 Defer)))))

; now we know for sure
(define-theorem! one-plus-one-is-two
  peano (= (add (S zero) (S zero))
           (S (S zero)))
  (Sequence
   (AddSucc (S zero) zero)
   (AddCommute (S zero) zero)
   (AddSucc zero zero)
   (AddZero zero)
   =R))
