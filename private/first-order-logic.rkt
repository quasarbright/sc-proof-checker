#lang racket/base

; provides operators and rules for first order logic

(require racket/contract/base
         racket/match
         "./core.rkt"
         "./sugar.rkt")

(module+ test (require rackunit))

(provide
 ; core operators
 (contract-out
  [=> (-> formula? formula? formula?)]
  [= (-> formula? formula? formula?)]
  [disj (->* (formula?) #:rest (listof formula?) formula?)]
  [conj (->* (formula?) #:rest (listof formula?) formula?)]
  [first-order-logic-theory theory/c])
 ; derived operators/formulae
 exists!
 bottom
 top
 (contract-out
  [<=> (-> formula? formula? formula?)]
  [neg (-> formula? formula?)])
 (contract-out
  ; rules
  ; intro and elim
  ; core
  [=>L (-> formula? rule/c)]
  [=>R rule/c]
  [=L (-> formula? formula? rule/c)]
  [=R rule/c]
  [OrL (-> formula? rule/c)]
  [OrR1 rule/c]
  [OrR2 rule/c]
  [OrR (-> formula? rule/c)]
  [AndL rule/c]
  [AndR rule/c]
  ; derived
  [BottomL rule/c]
  [TopR rule/c]
  [NotL (-> formula? rule/c)]
  [NotR rule/c]
  [<=>L rule/c]
  [<=>R rule/c]
  ; structural
  [CR rule/c]
  ; useful checked rules
  [ModusPonens (-> formula? rule/c)]))

; core operators

(define (=> p q) (list '=> p q))
; shadows number =, but whatever
(define (= t1 t2) (list '= t1 t2))

; these really aren't necessary, but they're worth including
(define (disj p . ps) (list* 'or p ps))
(define (conj p . ps) (list* 'and p ps))

(define first-order-logic-theory
  (theory (list)
          (list (operator '=> 2)
                (operator '= 2)
                (operator 'and (arity-at-least 1))
                (operator 'or (arity-at-least 1)))))

; derived operators/formulae

; bidirectional implication
(define (<=> p q) (conj (=> p q) (=> q p)))
; unique existence
(define-syntax-rule (exists! x p)
  ; it's guaranteed that y is not free in p because exists uses fresh
  (exists x (forall y (<=> (subst p x y) (= x y)))))
; can be used to prove anything, impossible to prove (without itself or equivalent)
(define bottom (forall a a))
; logical negation
(define (neg p) (=> p bottom))
; useless as an assumption (except to prove itself kind of), can always be proven
(define top (exists a a))

; rules

; intro and elim

; ctx |- (or p r)   ctx, q |- s
; ----------------------------- =>L^
; ctx, p=>q |- r or s
; included for completeness. Annoying to use
(define-rule ((=>L^ (and impl `(=> ,p ,q))) ctx `(or ,r ,s))
  (assert-in-context impl)
  (list (/- ctx `(or ,p ,r))
        (/- (extend-context ctx q) s)))

; ctx |- p    ctx, p, q |- r
; ----------------------- =>L
; ctx, p=>q |- r
; to use an implication, prove the antecedent, then use the consequent
(define-rule ((=>L (and impl `(=> ,p ,q))) ctx r)
  (assert-in-context impl)
  (check-proof/defer
   ctx r
   (Sequence
    CR
    (Branch
     (=>L^ (=> p q))
     (Sequence OrR1 Defer)
     Defer))))

; ctx,p |- q
; ------------- =>R
; ctx |- p => q
(define-rule (=>R ctx `(=> ,p ,q))
  (list (/- (extend-context ctx p) q)))

; ctx |- p[t2/t1]
; --------------- =L
; ctx,t1=t2 |- p
; handles symmetry automatically
(define-rule ((=L target replacement) ctx p)
  (unless (or (in-context? (= target replacement) ctx)
              (in-context? (= replacement target) ctx))
    (error '=L "couldn't find equality in context ~a" (= target replacement)))
  (list (/- ctx (subst p target replacement))))

; ------------ =R
; ctx |- t = t
(define-rule (=R ctx `(= ,p ,q))
  (unless (alpha-eqv? p q)
    (error '=R "terms are not equal: ~v vs ~v" p q))
  '())

; ctx,p |- r   ctx,q |- r ...
; --------------------------- OrL
; ctx,p or q or ... |- r
(define-rule ((OrL `(or ,ps ...)) ctx r)
  (for/list ([p ps])
    (/- (extend-context ctx p) r)))

; ctx |- p
; ------------- OrR1
; ctx |- p or q
(define-rule (OrR1 ctx `(or ,p ,_))
  (list (/- ctx p)))

; ctx |- q
; ------------- OrR2
; ctx |- p or q
(define-rule (OrR2 ctx `(or ,_ ,q))
  (list (/- ctx q)))

; ctx |- p
; ---------------------------------- OrR
; ctx |- p1 or ... or p or ... or pn
(define-rule ((OrR p) ctx `(or ,ps ...))
  (unless (member p ps alpha-eqv?)
    (error 'OrR "Rule not applicable. Formula not found in conjunction: ~v vs ~v" p (cons 'or ps)))
  (list (/- ctx p)))

; ctx,a,b |- p
; ------------- AndL
; ctx, a^b |- p
; unfolds all ands automatically
; There should never be an and in the ctx.
(define-rule (AndL ctx p)
  (define ctx^ (foldr (lambda (p ctx)
                        (match p
                          [`(and . ,ps)
                           (context-union (apply context (flatten-and ps))
                                           ctx)]
                          [_ (extend-context ctx p)]))
                      '()
                      ctx))
  (list (/- ctx^ p)))

; ctx |- p1   ctx |- p2
; ---------------------
; ctx |- p1 and p2
(define-rule (AndR ctx `(and ,ps ...))
  (for/list ([p ps])
    (/- ctx p)))

; --------------- BottomL
; ctx,bottom |- p
(define-rule (BottomL ctx p)
  (check-proof/defer
   ctx p
   (Sequence
    (ForallL bottom (p) I))))

; ---------- TopR
; ctx |- top
; ctx must not be empty
(define-rule (TopR ctx p)
  (when (null? ctx)
    (error 'TopR "contex is empty"))
  (check-proof/defer
   ctx p
   (Sequence
    (ExistsR ((car ctx)) I))))

; ctx, (not p) |- p
; ----------------- NotL
; ctx, (not p) |- q
; proof by contradiction
(define-rule ((NotL p) ctx q)
  ; TODO make this take in neg p once we have pattern expanders
  (assert-in-context (neg p))
  (check-proof/defer
   ctx q
   (Cuts
    ([p Defer])
    (Branch
     (=>L (neg p))
     I
     BottomL))))

; ctx p |- bottom
; --------------- NotR
; ctx |- (not p)
(define-rule (NotR ctx p) (=>R ctx p))

; ---------------- <=>L
; ctx,p <=> q |- r
(define-rule (<=>L ctx p) (AndL ctx p))

; ctx |- p => q and q => p
; ------------------------ <=>R
; ctx |- p <=> q
(define-rule (<=>R ctx p) (AndR ctx p))

; not doing exists!L/R

; structural

; ctx |- p or p
; ------------- CR
; ctx |- p
(define-rule (CR ctx p)
  (list (/- ctx `(or ,p ,p))))

; useful checked rules

; --------------- ModusPonens
; ctx,p,p=>q |- q
(define-rule ((ModusPonens p) ctx q)
  (assert-in-context `(=> ,p ,q))
  (assert-in-context p)
  (check-proof/defer
   ctx q
   (Branch
    (=>L (=> p q))
    I
    I)))

(module+ test
  ; modus ponens using checked =>L
  (check-not-exn
   (lambda ()
     (fresh
      (p q)
      (check-proof
       (context p (=> p q)) q
       (Branch
        (=>L (=> p q))
        I
        I)))))
  ; proof by contradiction
  (check-not-exn
   (lambda ()
     (check-proof
      ; there does not exists something that is not equal to itself
      '() (neg (exists x (neg (= x x))))
      (Sequence
       =>R
       ; assume there does exist such a thing
       (ExistsL
        ([(exists x (neg (= x x))) x])
        (Branch
         (=>L (neg (= x x)))
         =R
         BottomL))))))
  ; dual of proof by contradiction just for fun
  (check-not-exn
   (lambda ()
     (check-proof
      ; there does not exists something that is not equal to itself
      '() (forall x (= x x))
      (ForallR
       (x)
       =R))))
  ; proof by contradiction with NotR
  ; Pretty much the same thing with two nots!
  (check-not-exn
   (lambda ()
     (check-proof
      ; there does not exists something that is not equal to itself
      '() (neg (exists x (neg (= x x))))
      (Sequence
       NotR
       (ExistsL
        ([(exists x (neg (= x x))) x])
        (Sequence
         (NotL (= x x))
         =R))))))
  ; contradiction theorem
  (check-not-exn
   (lambda ()
     (check-proof
      '() (forall (p q) (=> (conj p (neg p))
                            q))
      (ForallR
       (p q)
       (Sequence
        =>R
        AndL
        (Branch
         (=>L (neg p))
         I
         BottomL))))))
  ; absurd
  (check-not-exn
   (lambda ()
     (check-proof
      '() (forall p (=> bottom p))
      (ForallR
       (p)
       (Sequence
        =>R
        (ForallL bottom (p) I))))))
  ; dual of absurd, idk what you'd call it
  (check-not-exn
   (lambda ()
     (check-proof
      '() (forall p (=> p top))
      (ForallR
       (p)
       (Sequence
        =>R
        (ExistsR (p) I))))))
  ; transitive property of equality
  (check-not-exn
   (lambda ()
     (check-proof
      '() (forall (a b c) (=> (conj (= a b) (= b c))
                              (= a c)))
      (ForallR
       (a b c)
       (Sequence
        =>R
        AndL
        (=L a b)
        (=L b c)
        =R)))))
  ; modus ponens theorem
  (check-not-exn
   (lambda ()
     (check-proof
      '() (forall (p q) (=> (conj p (=> p q)) q))
      (ForallR
       (p q)
       (Sequence
        =>R
        AndL
        CR
        (Branch
         (=>L^ (=> p q))
         (Sequence
          OrR1
          I)
         I))))))
  ; (p => q) => ((exists x p) => (exists y q))
  (check-not-exn
   (lambda ()
     (check-proof
      (context (exists (x y) (conj x y))) (exists z z)
      (ExistsL
       ([(exists (x y) (conj x y)) w]
        ; notice how you have access to w here
        [(exists y (conj w y)) w])
       (Sequence
        AndL
        (ExistsR (w) I))))))
  ; modus ponens theorem
  (check-not-exn
   (lambda ()
     (check-proof
      '() (forall p (forall q (=> (conj p (=> p q)) q)))
      (fresh
       (p q)
       (Sequence
        (ForallR
         (p q)
         (Sequence
          =>R
          AndL
          CR
          (Branch
           (=>L^ (=> p q))
           (Sequence
            OrR1
            I)
           I))))))))
  ; absurd
  (check-not-exn
   (lambda ()
     (fresh
      (a)
      (check-proof
       (context (forall x x)) a
       (Sequence
        (ForallL (forall x x) (a) I)))))))
