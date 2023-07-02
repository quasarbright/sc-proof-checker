#lang racket/base

; macros and utilities on top of core to facilitate use

(module+ test (require rackunit))
(require (for-syntax racket/base
                     syntax/parse
                     racket/syntax
                     racket/match)
         racket/contract/base
         racket/match
         racket/syntax
         racket/struct
         racket/set
         "./core.rkt")

(provide
 ; utilities for defining rules
 define-rule
 match-formula
 match*-formula
 ; checked rules
 (contract-out
  [check-proof/defer (-> context? formula? proof-tree? (listof judgement?))])
 ; utilities for constructing proofs
 Sequence
 Branch
 Cuts
 ; macros for operators
 define-operator
 define-variadic-operator
 define-quantifier
 ; utilities for constructing formulae
 ; core formulae
 fresh
 ; built-in rules
 ; don't put a contract bc you need to eq it lol
 Defer
 (contract-out
  [Debug rule/c]
  [TrustMe rule/c]
  [NoSubproofs! (-> rule/c rule/c)])
 (rename-out)
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
    [(_ () body ...)
     (Sequence body ...)]
    [(_ ([lemma lemma-proof] pairs ...) body ...)
     (Branch
      (Cut lemma)
      lemma-proof
      (Cuts (pairs ...) body ...))]))

; macros for operators

(define-syntax-rule (define-operator (name field ...))
  (struct name [field ...] #:transparent
    #:methods gen:formula
    [(define (gen-subst p target replacement)
       (match p
         [(name field ...)
          (name (subst field target replacement)
                ...)]))
     (define (gen-free-vars p)
       (match p
         [(name field ...)
          (set-union '() (free-vars field) ...)]))
     (define (gen-bound-vars p)
       (match p
         [(name field ...)
          (set-union '() (bound-vars field) ...)]))
     (define (gen-alpha-normalize p count vars)
       (match p
         [(name field ...)
          (name (alpha-normalize field count vars) ...)]))]))

(define-syntax define-variadic-operator
  (syntax-parser
    [(_ name:id ps:id)
     (define/syntax-parse struct-name (format-id #'name "~a^" (syntax-e #'name)))
     #'(begin
         (struct struct-name [ps] #:transparent
           #:methods gen:formula
           [(define (gen-subst p target replacement)
              (match p
                [(struct-name ps)
                 (struct-name (for/list ([p ps])
                                (subst p target replacement)))]))
            (define (gen-free-vars p)
              (match p
                [(struct-name ps)
                 (apply set-union '() (map free-vars ps))]))
            (define (gen-bound-vars p)
              (match p
                [(struct-name ps)
                 (apply set-union '() (map bound-vars ps))]))
            (define (gen-alpha-normalize p count vars)
              (match p
                [(struct-name ps)
                 (struct-name (for/list ([p ps]) (alpha-normalize p count vars)))]))]
           #:methods gen:custom-write
           [(define write-proc (make-constructor-style-printer
                                (lambda (_) 'name)
                                (lambda (p) (match p [(struct-name ps) ps]))))])
         (define-match-expander name
           (syntax-rules ()
             [(_ . pat)
              (struct-name (list . pat))])
           (syntax-rules ()
             [(_ p (... ...)) (struct-name (list p (... ...)))])))]))

(define-syntax define-quantifier
  (syntax-parser
    [(_ (name x p))
     (define/syntax-parse struct-name (format-id #'name "~a^" (syntax-e #'name)))
     #'(begin
         (struct struct-name [x p] #:transparent
           #:methods gen:formula
           [(define (gen-subst p target replacement)
              (match p
                [(struct-name x body)
                 (if (occurs-free? x target)
                     p
                     (struct-name x (subst body target replacement)))]))
            (define (gen-free-vars p)
              (match p
                [(struct-name x p)
                 (set-subtract (free-vars p) (list x))]))
            (define (gen-bound-vars p)
              (match p
                [(struct-name x p)
                 (cons x (bound-vars p))]))
            (define (gen-alpha-normalize p count vars)
              (define v (normal-name count))
              (match p
                [(struct-name x p)
                 (struct-name v (alpha-normalize p (add1 count) (hash-set vars x v)))]))]
           #:methods gen:custom-write
           [(define write-proc (make-constructor-style-printer
                                (lambda (_) 'name)
                                (lambda (p) (match p [(struct-name x p) (list x p)]))))])
         (define-match-expander name
           (syntax-rules ()
             [(_ () p) p]
             [(_ (x0 x (... ...)) p) (struct-name x0 (name (x (... ...)) p))]
             [(_ x p) (name (x) p)])
           (syntax-rules ()
             [(_ () p) p]
             [(_ (x0 x (... ...)) p)
              (fresh (x0) (struct-name x0 (name (x (... ...)) p)))]
             [(_ x p) (name (x) p)])))]))

(module+ test
  (define-operator (conj2 a b))
  (check-equal?
   (match (conj2 'a 'b)
     [(conj2 a b) a])
   'a)
  (check-equal? (free-vars (conj2 'a 'b))
                '(b a))

  (define-variadic-operator conj ps)
  (check-equal?
   (match (conj 'a 'b 'c)
     [(conj a b c)
      a])
   'a)
  (check-equal? (free-vars (conj 'a 'b 'c))
                '(c b a))

  (define-quantifier (forall x p))
  (define-quantifier (exists x p))
  (check-true
   (match (match (forall (x y) x)
            [(forall (x y) z) (list x y z)])
     [(list a b a) #t]
     [_ #f]))
  (check-true
   (alpha-eqv? (subst (forall q (conj2 (conj 'p 'p) q))
                      'p
                      'r)
               (forall q (conj2 (conj 'r 'r) q))))
  (check-equal? (alpha-normalize (forall (x y) x))
                (forall^ '_.0 (forall^ '_.1 '_.0)))

  (check-true (alpha-eqv? 'a 'a))
  (check-false (alpha-eqv? 'a 'b))
  (check-true (alpha-eqv? (forall a a) (forall b b)))
  (check-false (alpha-eqv? (forall a a) (exists b b)))
  (check-true (alpha-eqv? (forall a (forall b (conj a b)))
                          (forall b (forall c (conj b c)))))
  (check-false (alpha-eqv? (forall a (forall b (conj a b)))
                           (forall b (forall c (conj2 b c)))))
  (check-false (alpha-eqv? (forall a (forall b (conj a b)))
                           (forall b (forall b (conj b b)))))
  (check-false (alpha-eqv? (forall b (forall b (conj b b)))
                           (forall a (forall b (conj a b)))))
  (check-false (alpha-eqv? (forall a (forall b (conj a b)))
                           (forall a (forall b (conj b a))))))

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

; -------- Debug
; ctx |- p
; Used to view the context and formula to prove.
; Can be used for an interactive experience.
(define-rule (Debug ctx p)
  (displayln "given")
  ; assumes ctx is a list
  (for ([p (reverse ctx)]) (println p))
  (displayln "prove")
  (println p)
  '())

; -------- TrustMe
; ctx |- p
; Used when you're lazy!
(define-rule (TrustMe ctx p)
  '())

; Assert that an application of a "dynamic" rule requires no subproofs.
; Useful for asserting that an automatic rule fully succeeds.
(define-rule ((NoSubproofs! rul) ctx p)
  (define subs (rul ctx p))
  (if (null? subs)
      subs
      (error 'NoSubproofs! "Rule ~v was unable to automatically prove ~v" rul p)))

; theories

(define-syntax-rule (define-theorem! name thry p proof-tree)
  (define name
    (begin
      (theory-add-theorem! thry (list (/- (theory->context thry) p) proof-tree))
      p)))
