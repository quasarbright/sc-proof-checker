#lang racket/base

; macros and utilities on top of core to facilitate use

(require (for-syntax racket/base
                     syntax/parse)
         racket/contract/base
         racket/match
         racket/syntax
         "./core.rkt")

(provide
 ; utilities for defining rules
 define-rule
 match-formula
 match*-formula
 ; checked rules
 Defer
 (contract-out
  [check-proof/defer (-> context? formula? proof-tree? (listof judgement?))])
 ; utilities for constructing proofs
 Sequence
 Branch
 Cuts
 ; utilities for constructing formulae
 ; core formulae
 fresh
 forall
 exists
 ; built-in rules
 (contract-out
  [Debug rule/c]
  [TrustMe rule/c]
  [ForallL (-> formula? formula? rule?)]
  [ExistsR (-> formula? rule?)])
 (rename-out
  [ForallR* ForallR]
  [ExistsL* ExistsL])
 define-theorem!)

; utilities for defining rules

(define-syntax define-rule
  (syntax-parser
    [(_ ((name pat ...) ctx p) body ...)
     (define/syntax-parse (arg ...) (generate-temporaries (attribute pat)))
     #'(define (name arg ...)
         (define rul
           (rule (lambda (ctx pv)
                   (parameterize ([current-context ctx]
                                  [current-conclusion pv]
                                  [current-rule rul])
                     ; this match* could happen outside of the lambda,
                     ; but then we couldn't set current-rule for the error message
                     (match*-formula (arg ...)
                                     [(pat ...)
                                      (match-formula pv
                                                     [p
                                                      body
                                                      ...])])))
                 'name))
         rul
         )]
    [(_ (name ctx p) body ...)
     #'(define name
         (rule (lambda (ctx pv)
                 (parameterize ([current-context ctx]
                                [current-conclusion pv]
                                [current-rule name])
                   (match-formula pv
                                  [p
                                   body
                                   ...])))
               'name))]))

(define-syntax match*-formula
  (syntax-parser
    [(_ (p:id ...) [(pat ...) body ...])
     (define/syntax-parse (underscore ...) (for/list ([_ (attribute pat)]) #'_))
     #'(match* (p ...)
         [(pat ...) body ...]
         [(underscore ...) (formula-shapes-error (p ...) (pat ...))])]))

(define-syntax-rule (match-formula p [pat body ...] ...)
  ; assume p is a variable
  (match p
    [pat body ...]
    ...
    [_ (formula-shape-error p pat ...)]))

(define-syntax-rule (formula-shape-error p pat ...)
  (error (object-name (current-rule)) "Rule is not applicable. Expected a formula looking like one of ~v, but got ~v" (list 'pat ...) p))

(define-syntax-rule (formula-shapes-error (p ...) (pat ...))
  (error (object-name (current-rule)) "Rule is not applicable. Expected formulas looking like ~v, but got ~v" (list 'pat ...) (list p ...)))

; checked rules

; For a "shortcut" rule like ModusPonens in terms of other rules,
; it's safe to add a rule for it if you accompany the rule with an equivalent proof.
; Checked rules allow you to define a rule like ModusPonens USING a proof.
; This way, rules are either axiomatic
; or verified shortcuts for proofs in terms of other rules.

(define currently-deferring? (make-parameter #f))
; Fake rule used in checked rules to defer subproofs to the user of the checked rule.
; Don't use this in regular proofs
(define-rule (Defer ctx p)
  (unless (currently-deferring?)
    (error 'Defer "can only be used during a checked rule proof"))
  '())

; Context Formula ProofTree -> (listof Judgement)
; like check-proof, but accumulates deferred subproofs
; Useful for defining checked rules.
; TODO what is the equivalent to this across the curry howard isomorphism?
(define (check-proof/defer ctx p tree)
  (define inference-tree (parameterize ([currently-deferring? #t])
                           (check-proof ctx p tree)))
  (get-deferred-judgements inference-tree))

; InferenceTree
(define (get-deferred-judgements tree)
  (match tree
    [(list j (== Defer eq?) '())
     (list j)]
    [(list _ _ subtrees)
     (apply append (map get-deferred-judgements subtrees))]))

; macros for building proofs

; (Sequence Rule1 Rule2 ... proof)
; proof
; ---------- RuleN
; ...
; ---------- Rule2
; ctx2 |- p2
; ---------- Rule1
; ctx1 |- p1
; where the last argument is the final subproof
; useful for sequencing suproofs. Ex:
(define-syntax Sequence
  ; TODO make this a procedure lol
  (syntax-rules ()
    [(_ proof) proof]
    [(_ rule0 rule ...) (list rule0 (Sequence rule ...))]))

; (Branch Rule subproof ...)
; subproof ...
; ------------ Rule
; ctx |- p
; useful for branching for multiple subproofs of one rule application
(define Branch list)

; (Cuts ([lemma lemma-proof] ...) proof)
; useful for sequencing cuts
(define-syntax Cuts
  (syntax-rules ()
    [(_ () proof)
     proof]
    [(_ ([lemma lemma-proof] pairs ...) proof)
     (Branch
      (Cut lemma)
      lemma-proof
      (Cuts (pairs ...) proof))]))

; macros for formulae

(define-syntax-rule
  (fresh (x ...) body ...)
  (let ([x (mk-fresh-var 'x)] ...) body ...))
(define fresh-counter 0)
; {symbol?} -> symbol?
; generate a fresh variable name.
; different calls to this procedure will never be equal? to each other.
; can optionally pass in base name.
(define (mk-fresh-var [base-name '_])
  (set! fresh-counter (add1 fresh-counter))
  (mk-var base-name fresh-counter))
; symbol? natural? -> symbol?
(define (mk-var x n) (format-symbol "~a:~a" x n))

(define-syntax forall
  (syntax-rules ()
    [(_ () p) p]
    [(_ (x0 x ...) p)
     (fresh (x0) (list 'forall x0 (forall (x ...) p)))]
    [(_ x p) (forall (x) p)]))
(define-syntax exists
  (syntax-rules ()
    [(_ () p) p]
    [(_ (x0 x ...) p)
     (fresh (x0) (list 'exists x0 (exists (x ...) p)))]
    [(_ x p) (exists (x) p)]))

; built-in rules

; ctx |- p-body[y/x]
; ------------------------ ForallR
; ctx |- (forall x p-body)
(define-rule ((ForallR y) ctx (and p `(forall ,x ,p-body)))
  ; important to use p. x = y can be ok
  (when (or (occurs-free? y p) (occurs-free?/context y ctx))
    (error "cannot instantiate forall with a variable that occurs free in lower sequents"))
  (list (/- ctx (subst p-body x y))))

; use to instantiate nested conclusion foralls
(define-syntax ForallR*
  (syntax-rules ()
    [(_ () proof) proof]
    [(_ (x0 x ...) proof)
     (fresh
      (x0)
      (Sequence
       (ForallR x0)
       (ForallR* (x ...) proof)))]))

; ctx, p-body[y/x] |- p
; --------------------------- ExistsL
; ctx, (exists x p-body) |- p
(define-rule ((ExistsL `(exists ,x ,p-body) y) ctx p)
  (when (or (occurs-free? y p) (occurs-free?/context y ctx))
    (error 'ExistsL "cannot instantiate existential with a variable that occurs free in lower sequents"))
  (list (/- (extend-context ctx (subst p-body x y)) p)))

; use to instantiate nested assumption exists
(define-syntax ExistsL*
  (syntax-rules ()
    [(_ () proof) proof]
    [(_ ([p-exists x] pair ...) proof)
     (fresh
      (x)
      (Sequence
       (ExistsL p-exists x)
       (ExistsL* (pair ...) proof)))]))

; left off here
#;
(define-syntax ForallL*
  (syntax-rules ()
    [(_ p-forall (t) proof) (Sequence (ForallL p-forall t) proof)]
    [(_ p-forall (t0 t ...) proof)
     (let ([p p-forall])
       (Sequence
        (ForallL p t0)
        (match-formula p
          [`()])))]))

; (forall x p-body) in ctx    ctx,p-body[t/x] |- p
; ------------------------------------------------
; ctx |- p
(define-rule ((ForallL (and p-forall `(forall ,x ,p-body)) t) ctx p)
  (assert-in-context p-forall)
  (list (/- (extend-context ctx (subst p-body x t)) p)))

; ctx |- p[t/x]
; ------------------- ExistsR
; ctx |- (exists x p)
; if you can prove that a t satisfies p,
; t is something that exists that satisfied p!
(define-rule ((ExistsR t) ctx `(exists ,x ,p))
  (list (/- ctx (subst p x t))))

; -------- Debug
; ctx |- p
; Used to view the context and formula to prove.
; Can be used for an interactive experience.
(define-rule (Debug ctx p)
  (displayln "given")
  (for ([p ctx]) (displayln p))
  (displayln "prove")
  (displayln p)
  '())

; -------- TrustMe
; ctx |- p
; Used when you're lazy!
(define-rule (TrustMe ctx p)
  '())

; theories

(define-syntax-rule (define-theorem! name thry p proof-tree)
  (define name
    (begin
      (theory-add-theorem! thry (list (/- (theory->context thry) p) proof-tree))
      p)))
