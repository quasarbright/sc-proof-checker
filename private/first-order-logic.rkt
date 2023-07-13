#lang racket/base

; provides operators and rules for first order logic

(require racket/contract/base
         racket/match
         "./core.rkt"
         "./sugar.rkt")

(module+ test (require rackunit))

(provide
 ; core operators
 disj
 conj
 inst
 forall
 ForallL
 ForallR
 exists
 ExistsL
 ExistsR
 exists!
 Exists!L
 Exists!R
 QuantL
 QuantR
 =>
 =
 (contract-out
  [first-order-logic-theory theory/c])
 ; derived operators/formulae
 <=>
 neg
 exists!
 bottom
 top
 (contract-out
  ; rules
  ; intro and elim
  ; core
  [=>L (-> formula? rule/c)]
  [=>R rule/c]
  [=L (-> formula? formula? rule/c)]
  [=LL (-> formula? formula? formula? rule/c)]
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
  [ModusPonens (-> formula? formula? rule/c)]))

(define-quantifier (forall x p))
(define-quantifier (exists x p))
(define-operator (=> p q))
(define-operator (= p q))
(define-variadic-operator disj ps)
(define-variadic-operator conj ps)
; bidirectional implication
(define-operator (<=> p q))
; unique existence
(define-quantifier (exists! x p))
; can be used to prove anything, impossible to prove (without itself or equivalent)
(define bottom 'bottom)
; logical negation
(define-operator (neg p))
; useless as an assumption (except to prove itself kind of), can always be proven
(define top 'top)

(define first-order-logic-theory
  (theory (list)))

; rewrites

(define (rewrite-<=> p q) (conj (=> p q) (=> q p)))
(define (rewrite-exists! x p)
  (exists^ x (forall y (<=> (subst p x y) (= x y)))))
(define (rewrite-exists!/whole p)
  (match p
    [(exists! x p) (rewrite-exists! x p)]
    [_ (error 'rewrite-exists!/whole "not an exists!: ~v" p)]))

(define (rewrite-neg p) (=> p bottom))
(define (rewrite-bottom) (forall a a))
(define (rewrite-top) (exists a a))

(define (inst p q)
  (match p
    [(forall x p) (subst p x q)]
    [(exists x p) (subst p x q)]
    [(exists! x p) (inst (rewrite-exists! x p) q)]
    [_ (error 'inst "cannot instantiate ~v" p)]))

; rules

; intro and elim

; ctx |- (or p r)   ctx, q |- s
; ----------------------------- =>L^
; ctx, p=>q |- r or s
; included for completeness. Annoying to use
(define-rule ((=>L^ (and impl (=> p q))) ctx (disj r s))
  (assert-in-context impl)
  (list (/- ctx (disj p r))
        (/- (extend-context ctx q) s)))

; ctx |- p    ctx, p, q |- r
; ----------------------- =>L
; ctx, p=>q |- r
; to use an implication, prove the antecedent, then use the consequent
(define-rule ((=>L (and impl (=> p q))) ctx r)
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
(define-rule (=>R ctx (=> p q))
  (list (/- (extend-context ctx p) q)))

; ctx |- p[t2/t1]
; --------------- =L
; ctx,t1=t2 |- p
; handles symmetry automatically
(define-rule ((=L target replacement) ctx p)
  (unless (or (in-context? (= target replacement) ctx)
              (in-context? (= replacement target) ctx))
    (error '=L "couldn't find equality in context ~v" (= target replacement)))
  (list (/- ctx (subst p target replacement))))

; Like =L, but operates on an assumption instead of the statement being proven
(define-rule ((=LL p target replacement) ctx q)
  (unless (or (in-context? (= target replacement) ctx)
              (in-context? (= replacement target) ctx))
    (error '=L "couldn't find equality in context ~v" (= target replacement)))
  (assert-in-context p)
  (list (/- (extend-context ctx (subst p target replacement)) q)))

; ------------ =R
; ctx |- t = t
(define-rule (=R ctx (= p q))
  (unless (alpha-eqv? p q)
    (error '=R "terms are not equal: ~v vs ~v" p q))
  '())

; ctx,p |- r   ctx,q |- r ...
; --------------------------- OrL
; ctx,p or q or ... |- r
(define-rule ((OrL (disj ps ...)) ctx r)
  (for/list ([p ps])
    (/- (extend-context ctx p) r)))

; ctx |- p
; ------------- OrR1
; ctx |- p or q
(define-rule (OrR1 ctx (disj p _))
  (list (/- ctx p)))

; ctx |- q
; ------------- OrR2
; ctx |- p or q
(define-rule (OrR2 ctx (disj _ q))
  (list (/- ctx q)))

; ctx |- p
; ---------------------------------- OrR
; ctx |- p1 or ... or p or ... or pn
(define-rule ((OrR p) ctx (disj ps ...))
  (unless (member p ps alpha-eqv?)
    (error 'OrR "Rule not applicable. Formula not found in conjunction: ~v vs ~v" p (cons 'or ps)))
  (list (/- ctx p)))

; ctx,a,b |- p
; ------------- AndL
; ctx, a^b |- p
; unfolds all ands automatically (shallowly)
; TODO deep
(define-rule (AndL ctx p)
  (define ctx^ (foldr (lambda (p ctx)
                        (match p
                          [(conj ps ...)
                           (context-union ps ctx)]
                          [_ (extend-context ctx p)]))
                      '()
                      ctx))
  (list (/- ctx^ p)))

; ctx |- p1   ctx |- p2
; ---------------------
; ctx |- p1 and p2
(define-rule (AndR ctx (conj ps ...))
  (for/list ([p ps])
    (/- ctx p)))


; built-in rules

; ctx |- p-body[y/x]
; ------------------------ ForallR
; ctx |- (forall x p-body)
(define-rule ((ForallR^ y) ctx (and p (forall x p-body)))
  ; important to use p. x = y can be ok
  (when (or (occurs-free? y p) (occurs-free?/context y ctx))
    (error "cannot instantiate forall with a variable that occurs free in lower sequents"))
  (list (/- ctx (subst p-body x y))))

; use to instantiate nested conclusion foralls
(define-syntax ForallR
  (syntax-rules ()
    [(_ () body ...) (Sequence body ...)]
    [(_ (x0 x ...) body ...)
     (fresh
      (x0)
      (Sequence
       (ForallR^ x0)
       (ForallR (x ...) body ...)))]))

; ctx, p-body[y/x] |- p
; --------------------------- ExistsL
; ctx, (exists x p-body) |- p
(define-rule ((ExistsL^ (exists x p-body) y) ctx p)
  (when (or (occurs-free? y p) (occurs-free?/context y ctx))
    (error 'ExistsL "cannot instantiate existential with a variable that occurs free in lower sequents"))
  (list (/- (extend-context ctx (subst p-body x y)) p)))

; use to instantiate nested assumption exists
; TODO use inst like foralll
(define-syntax ExistsL
  (syntax-rules ()
    [(_ () body ...) (Sequence body ...)]
    [(_ ([x p-exists] pair ...) body ...)
     (fresh
      (x)
      (Sequence
       (ExistsL^ p-exists x)
       (ExistsL (pair ...) body ...)))]))

; (forall x p-body) in ctx    ctx,p-body[t/x] |- p
; ------------------------------------------------ ForallL
; ctx |- p
(define-rule ((ForallL^ (and p-forall (forall x p-body)) t) ctx p)
  (assert-in-context p-forall)
  (list (/- (extend-context ctx (subst p-body x t)) p)))

; Used to instantiate nested assumption foralls
(define-syntax ForallL
  (syntax-rules ()
    [(_ _ () body ...) (Sequence body ...)]
    [(_ p (t0 t ...) body ...)
     (let ([pv p]
           [tv t0])
       (Sequence
        (ForallL^ pv tv)
        (ForallL (inst pv tv) (t ...) body ...)))]))

; Used to instantiate nested assumption quantifications
(define-syntax QuantL
  (syntax-rules (exists! exists forall)
    [(_ _ () body ...) (Sequence body ...)]
    [(_ p ([exists x] pair ...) body ...)
     (let ([pv p])
       (Sequence
        (ExistsL
         ([x pv])
         (QuantL (inst pv x) (pair ...) body ...))))]
    [(_ p ([forall t] pair ...) body ...)
     (let ([pv p]
           [tv t])
       (ForallL pv (tv)
                (QuantL (inst pv tv) (pair ...) body ...)))]
    [(_ p ([exists! x t]) body ...)
     (Exists!L p (x t) body ...)]))

; ctx |- p[t/x]
; ------------------- ExistsR
; ctx |- (exists x p)
; if you can prove that a t satisfies p,
; t is something that exists that satisfied p!
(define-rule ((ExistsR^ t) ctx (exists x p))
  (list (/- ctx (subst p x t))))

; used for proving nested existentials
(define-syntax ExistsR
  (syntax-rules ()
    [(_ () body ...) (Sequence body ...)]
    [(_ (t0 t ...) body ...)
     (Sequence
      (ExistsR^ t0)
      (ExistsR (t ...) body ...))]))

; used for proving nested quantifications
(define-syntax QuantR
  (syntax-rules (exists! exists forall)
    [(_ () body ...) (Sequence body ...)]
    [(_ ([exists t] pair ...) body ...)
     (ExistsR (t) (QuantR (pair ...) body ...))]
    [(_ ([forall x] pair ...) body ...)
     (ForallR (x) (QuantR (pair ...) body ...))]
    [(_ ([exists! t y]) proof1 proof2)
     (Exists!R (t y) proof1 proof2)]))

; (bottom) ~> (forall a a) in ctx
(define-rule (BottomL^ ctx p)
  (assert-in-context 'bottom)
  (list (/- (extend-context ctx (rewrite-bottom)) p)))

; --------------- BottomL
; ctx,bottom |- p
(define-rule (BottomL ctx p)
  (check-proof/defer
   ctx p
   (Sequence
    BottomL^
    (ForallL (rewrite-bottom) (p) I))))

(define-rule (BottomR ctx 'bottom)
  (list (/- ctx (rewrite-bottom))))

; (top) ~> (exists a a)
(define-rule (TopR^ ctx 'top)
  (list (/- ctx (rewrite-top))))

; ---------- TopR
; ctx |- top
; ctx must not be empty
(define-rule (TopR ctx 'top)
  (when (null? ctx)
    (error 'TopR "contex is empty"))
  (check-proof/defer
   ctx 'top
   (Sequence
    TopR^
    (ExistsR ((car ctx)) I))))

; (neg p) ~> (=> p bottom) in ctx
(define-rule ((NotL^ p) ctx q)
  (assert-in-context (neg p))
  (list (/- (extend-context ctx (rewrite-neg p)) q)))

; ctx, (not p) |- p
; ----------------- NotL
; ctx, (not p) |- q
; proof by contradiction
(define-rule ((NotL p) ctx q)
  (assert-in-context (neg p))
  (check-proof/defer
   ctx q
   (Cuts
    ([p Defer])
    (NotL^ p)
    (Branch
     (=>L (rewrite-neg p))
     I
     BottomL))))

; (neg p) ~> (=> p bottom)
(define-rule (NotR^ ctx (neg p))
  (list (/- ctx (rewrite-neg p))))

; ctx p |- bottom
; --------------- NotR
; ctx |- (not p)
(define-rule (NotR ctx (neg p))
  (check-proof/defer
   ctx (neg p)
   (Sequence
    NotR^
    =>R
    Defer)))

; (<=> p q) ~> (conj (=> p q) (=> q p)) in ctx, apply to all
(define-rule (<=>L^ ctx p)
  (list (/- (for/list ([p ctx])
              (match p
                [(<=> p q) (conj (=> p q) (=> q p))]
                [p p]))
            p)))


; <=> rewrite and AndL
(define-rule (<=>L ctx p)
  (check-proof/defer
   ctx p
   (Sequence
    <=>L^
    AndL
    Defer)))

(define-rule (<=>R^ ctx (<=> p q))
  (list (/- ctx (rewrite-<=> p q))))

; ctx,p |- q   ctx,q |- p
; ----------------------------- <=>R
; ctx |- p <=> q
(define-rule (<=>R ctx (<=> p q))
  (check-proof/defer
   ctx (<=> p q)
   (Sequence <=>R^
             (Branch AndR (Sequence =>R Defer) (Sequence =>R Defer)))))

; (exists! x p) ~> (exists x (forall y (<=> p[y/x] (= x y))))
(define-rule (Exists!R^ ctx (exists! x p))
  (list (/- ctx (rewrite-exists! x p))))

; ctx,p[y/x] |- (= t y)   ctx,(= t y) |- p[y/x]
; ctx |- (exists! x p)
; t is the thing, p(y) <=> y = t
(define-syntax-rule
  (Exists!R (t y) proof1 proof2)
  (Sequence
   Exists!R^
   (QuantR ([exists t]
            [forall y])
           (Branch <=>R proof1 proof2))))

; ctx,(exists! x p) ~> ctx,(exists x (forall y (<=> p[y/x] (= x y))))
(define-rule ((Exists!L^ (and p-exists (exists! x p))) ctx q)
  (assert-in-context p-exists)
  (list (/- (extend-context ctx (rewrite-exists! x p)) q)))

; ctx,(exists! x p) ~> ctx,(p[y/x] => y=t),(y=t => p[y/x])
(define-syntax-rule
  (Exists!L p (y t) body ...)
  (let ([pv p])
    (Sequence
     (Exists!L^ pv)
     (QuantL (rewrite-exists!/whole pv)
             ([exists y] [forall t])
             <=>L
             body
             ...))))

(module+ test
  (check-not-exn
   (lambda ()
     (check-proof
      (theory->context first-order-logic-theory)
      (forall a (exists! b (= a b)))
      (Sequence
       (ForallR (a)
                (Exists!R (a y)
                          I I))))))
  ; TODO test with exists! in ctx, can't think of anything not stupid
  )

; structural

; ctx |- p or p
; ------------- CR
; ctx |- p
(define-rule (CR ctx p)
  (list (/- ctx (disj p p))))

; useful checked rules

; ctx,q |- r
; --------------- ModusPonens
; ctx,p,p=>q |- r
(define-rule ((ModusPonens p q) ctx r)
  (assert-in-context (=> p q))
  (assert-in-context p)
  (check-proof/defer
   ctx q
   (Branch
    (=>L (=> p q))
    I
    Defer)))

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
       NotR^
       =>R
       ; assume there does exist such a thing
       (ExistsL
        ([x (exists x (neg (= x x)))])
        (NotL^ (= x x))
        (Branch
         (=>L (rewrite-neg (= x x)))
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
        ([x (exists x (neg (= x x)))])
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
        (NotL^ p)
        (Branch
         (=>L (rewrite-neg p))
         I
         BottomL))))))
  ; absurd
  (check-not-exn
   (lambda ()
     (check-proof
      '() (forall p (=> (rewrite-bottom) p))
      (ForallR
       (p)
       (Sequence
        =>R
        (ForallL (rewrite-bottom) (p) I))))))
  ; dual of absurd, idk what you'd call it
  (check-not-exn
   (lambda ()
     (check-proof
      '() (forall p (=> p (rewrite-top)))
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
       ([w (exists (x y) (conj x y))]
        ; notice how you have access to w here
        [w (exists y (conj w y))])
       (Sequence
        AndL
        (ExistsR (w) I))))))
  ; modus ponens theorem
  (check-not-exn
   (lambda ()
     (check-proof
      '() (forall p (forall q (=> (conj p (=> p q)) q)))
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
  ; absurd
  (check-not-exn
   (lambda ()
     (fresh
      (a)
      (check-proof
       (context (forall x x)) a
       (Sequence
        (ForallL (forall x x) (a) I)))))))
