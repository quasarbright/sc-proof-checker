#lang racket/base

; runtime core

(module+ test (require rackunit))
(require racket/contract/base)
(provide
 formula?
 context?
 judgement?
 rule?
 rule/c
 proof?
 proof-tree?
 inference-tree?
 operator?
 (struct-out operator)
 theory/c
 (except-out (struct-out theory) theory set-theory-theorems!)
 (struct-out rule)
 (contract-out
  ; constructors
  [context (->* () #:rest (listof formula?) context?)]
  [/- (-> context? formula? judgement?)]
  ; built-in rules
  [I rule/c]
  [Cut (-> formula? rule/c)]
  ; proof-checking
  [current-rule (parameter/c (or/c #f rule/c))]
  [current-context (parameter/c context?)]
  [current-conclusion (parameter/c (or/c #f formula?))]
  [check-proof (-> context? formula? proof-tree? inference-tree?)]
  ; context operations
  [assert-in-context (->* (formula?) (context? symbol?) void?)]
  [assert-context-has-theory (->* (theory/c) (context? symbol?) void?)]
  [in-context? (->* (formula?) (context?) any/c)]
  [find-in-context (->* ((-> formula? any/c)) (context?) (or/c #f formula?))]
  [extend-context (->* (context?) #:rest (listof formula?) context?)]
  [flatten-and (-> (listof formula?) (listof formula?))]
  [context-union (->* () #:rest (listof context?) context?)]
  [subcontext? (-> context? context? any/c)]
  ; formula operations
  ; (subst p target replacement) is p[replacement/target]
  [subst (-> formula? formula? formula? formula?)]
  [context-bound? (-> context? any/c)]
  [free-vars/context (-> context? (listof symbol?))]
  [formula-bound? (-> formula? any/c)]
  [free-vars (-> formula? (listof symbol?))]
  [occurs-free?/context (-> symbol? context? any/c)]
  [occurs-free? (-> symbol? formula? any/c)]
  [occurs-bound? (-> symbol? formula? any/c)]
  [alpha-eqv? (-> formula? formula? any/c)]
  [alpha-normalize (-> formula? formula?)]
  ; theories
  [theory->context (-> theory/c context?)]
  [theory-add-theorem! (-> theory/c proof? inference-tree?)]
  [rename make-theory theory (-> (listof formula?) (listof operator?) theory/c)]))

(require racket/contract/base
         racket/match
         racket/set
         racket/syntax)

; A Formula is one of
; symbol?                            variable
; (forall symbol? Formula)           universal quantification
; (exists symbol? Formula)           existential quantification
; (symbol? Formula ...)              operation
(define (formula? p)
  (match p
    [(? symbol?) #t]
    [(list (? symbol?) ps ...)
     (for/and ([p ps]) (formula? p))]
    [_ #f]))

; These are lists, where forall is 'forall

; Represents a statement in first order logic
; Examples:
(define p-formula 'p)
(define q-formula 'q)
(define p-and-q-formula '(and p q))

; A Context is a (listof Formula) representing formulae that are assumed to be true
; First element is most recent.

; Formula ... -> Context
(define context? (listof formula?))
(define (context . ps) ps)

; A Judgement is a (list Context Formula) written in math like
; ctx |- p
; which means that under the context ctx, the "conclusion" formula p is true.
(define judgement? (list/c context? formula?))

; Context Formula -> Judgement
(define (/- ctx p) (list ctx p))

; Examples:
(define and-judgement (/- (context 'p 'q) '(and p q)))

; A Rule is a
(struct rule [proc name]
  #:property prop:object-name (lambda (rul) (rule-name rul))
  #:property prop:procedure (lambda (rul . args) (apply (rule-proc rul) args)))
; where proc is a (Context Formula -> (listof Judgement))
; representing the required subproofs to prove the initial conclusion
; where name is a symbol, the name of the rule.
; A rule is responsible for checking that it can validly be applied.
; For rules that need additional information, curried functions are used.
; Rule are written in math like
(define rule/c (struct/c rule (-> context? formula? (listof judgement?)) symbol?))

; ctx2 |- p2   ctx3 |- p3 ...
; --------------------------- RuleName
; ctx1 |- p1

; This means p1 can be proven true under ctx1 if it can be proven that p2 is true
; under ctx2 and p3 is true under ctx3 and so on. The "inference line"
; separates the conclusion (bottom) from the required subproofs (top).
; Read it starting at the bottom, then read the top left-to-right.

; Examples:

; ctx |- p   ctx |- q
; ------------------- AndR
; ctx |- p and q
; to prove a conjunction, you must prove both statements.
(define AndR
  (rule (lambda (ctx p)
          (match p
            [`(and ,p ,q)
             (list (/- ctx p)
                   (/- ctx q))]
            [_ (error "expected a conjunction")]))
        'AndR))

; ----------- I
; ctx, p |- p
; If you assume a statement is true, it is true! No subproofs necessary
(define I
  (rule (lambda (ctx p)
          (assert-in-context p ctx)
          '())
        'I))

; ctx |- lemma   ctx,lemma |- p
; ----------------------------- Cut
; ctx |- p
; If you can prove an auxiliary statement (lemma),
; you can assume that it is true in a proof of your original statement.
; It is not obvious what the lemma is from just ctx and p, so we take in the lemma
; as an argument.
(define (Cut lemma)
  (rule (lambda (ctx p)
          (list (/- ctx lemma)
                (/- (cons lemma ctx) p)))
        'Cut))

; A Proof is a
; (list Judgement ProofTree)
; Representing a judgement and its proof
; Examples:

; ------- I   ------- I
; p,q | p     p,q | q
; --------------------- AndR
; p,q |- p and q
(define and-proof
  (list and-judgement
        (list AndR
              (list I)
              (list I))))
; could be written as
#;(list and-judgement (list AndR I I))
; using the ProofTree shorthand

; A ProofTree is a (or (list Rule ProofTree ...) Rule)
; Represents the use of a rule and proofs of its sub-judgements to prove an (implicit) conclusion judgement.
; The second case is shorthand for (list rul). This is used when you are using a rule like I with no subproofs.
(define proof-tree?
  (flat-rec-contract proof-tree
                     (or/c (cons/c rule? (listof proof-tree))
                           rule?)))
(define proof? (list/c judgement? proof-tree?))

; An InferenceTree is a (list Judgement Rule (listof InferenceTree))
; Representing the completed inference tree followed during a Proof
; The Judgement is what was proven
; The list of inference trees is the sub-proofs
(define inference-tree?
  (flat-rec-contract inference-tree
                     (list/c judgement? rule? (listof inference-tree))))
; Examples:
(define and-inference-tree
  (list (/- (list 'p 'q) '(and p q))
        AndR
        (list (list (/- (list 'p 'q) 'p)
                    I
                    '())
              (list (/- (list 'p 'q) 'q)
                    I
                    '()))))

; An Operator is a
(struct operator [name arity])
(define operator/c
  (struct/c operator symbol? procedure-arity?))
; Example:
(define and-operator (operator 'and (arity-at-least 1)))

; A Theory is a
(struct theory [axioms operators [theorems #:mutable]] #:transparent)
(define theory/c
  (struct/dc theory
             [axioms (listof formula?)]
             [operators (listof operator/c)]
             [theorems (and/c (listof formula?))]
             ; TODO operator check?
             ; TODO remove this and enforce it in add-theory! instead
             #:inv (axioms theorems) (for/and ([theorem theorems])
                                       (subset? (free-vars theorem)
                                                (free-vars/context (apply context axioms))))))
; Theorems are assumed to be proven under the axioms.
; Theorems may have free variables as long as they are free in the axioms (like zero in peano)
(define (make-theory axioms operators) (theory axioms operators '()))

; proof-checking

(define current-rule (make-parameter #f))
(define current-context (make-parameter (context)))
; the formula being proven
(define current-conclusion (make-parameter #f))

; Context Formula ProofTree -> InferenceTree
; Check that the proof tree proves the formula to be true under the context
(define (check-proof ctx p tree)
  (parameterize ([current-context ctx]
                 [current-conclusion p])
      (match tree
        [(? rule? rul)
         ; using a rule by itself like I is the same as (list I)
         (check-proof ctx p (list rul))]
        [(cons rul subtrees)
         (match-define
           (list (list subcontexts subformulae) ...)
           (parameterize ([current-rule rul])
             (rul ctx p)))
         (unless (= (length subtrees) (length subcontexts))
           (error (object-name rul) "incorrect number of subproofs. Expected ~a, given ~a" (length subcontexts) (length subtrees)))
         (list (/- ctx p) rul
               (for/list ([ctx subcontexts]
                          [p subformulae]
                          [tree subtrees])
                 (check-proof ctx p tree)))])))

(module+ test
  (check-equal? (check-proof
                 '(p q) '(and p q)
                 (list AndR I I))
                and-inference-tree))

; context operations

; Formula {Context} {symbol?} -> Void
(define (assert-in-context p [ctx (current-context)] [who-sym (object-name (current-rule))])
  (unless (in-context? p ctx)
    (if who-sym
        (error who-sym "~v not found in context ~v" p ctx)
        (error "~v not found in context ~v" p ctx))))

; Theory {Context} -> Void
; Assert that that a theory's axioms and theorems are available in the context.
(define (assert-context-has-theory thry [ctx (current-context)] [who-sym (object-name (current-rule))])
  (unless (subcontext? (theory->context thry) ctx)
    (if who-sym
        (error who-sym "expected access to theory")
        (error "expected access to theory"))))

; Formula Context -> boolean?
(define (in-context? p [ctx (current-context)])
  (member p ctx alpha-eqv?))

; (Formula -> Any) Context -> boolean?
(define (find-in-context proc [ctx (current-context)])
  (findf proc ctx))

; Context Formula ... -> Context
(define (extend-context ctx . ps)
  (context-union (flatten-and ps) ctx))

; (listof Formula) -> (listof Formula)
; takes the arguments of an and formula
; and flattens out nested ands
(define (flatten-and ps)
  (foldr (lambda (p flattened)
           (match p
             [`(and . ,ps)
              (append (flatten-and ps) flattened)]
             [p (cons p flattened)]))
         '()
         ps))
(module+ test
  (check-equal? (flatten-and '(a1 (and a2 a3) (and (and (and a4 a5) a6))))
                '(a1 a2 a3 a4 a5 a6)))

; Context ... -> Context
(define (context-union . ctxs)
  (apply append ctxs))

; Context Context -> Any
; Are all proofs under ctx1 valid under ctx2?
(define (subcontext? ctx1 ctx2)
  (for/and ([p ctx1])
    (in-context? p ctx2)))

; formula operations

; Formula Formula Formula -> Formula
; p[replacement/target]
(define (subst p target replacement)
  (match p
    [(== target alpha-eqv?)
     replacement]
    [(? symbol?) p]
    [(list (and quantifier (or 'forall 'exists)) a body)
     (if (occurs-free? a target)
         p
         (list quantifier a (subst body target replacement)))]
    [(cons op ps)
     (cons op (for/list ([p ps]) (subst p target replacement)))]))

; Context -> Any
; Are there no free vars in the context?
(define (context-bound? ctx)
  (set-empty? (free-vars/context ctx)))

; Context -> (listof symbol?)
(define (free-vars/context ctx)
  (apply set-union '() (for/list ([p ctx]) (free-vars p))))

; Formula -> Any
; Are there no free vars in the formula?
(define (formula-bound? p)
  (set-empty? (free-vars p)))

; Formula -> (listof symbol?)
(define (free-vars p)
  (match p
    [(? symbol?) (list p)]
    [(list (or 'forall 'exists) a body)
     (set-subtract (free-vars body) (list a))]
    [(cons _ ps)
     (apply append (map free-vars ps))]))

; symbol? Context -> boolean?
(define (occurs-free?/context x ctx)
  (for/or ([p ctx]) (occurs-free? x p)))

; symbol? Formula -> boolean?
(define (occurs-free? x p)
  (match p
    [(? symbol?)
     (eq? x p)]
    [(list (or 'forall 'exists) a p)
     (and (not (eq? x a)) (occurs-free? x p))]
    [(cons _ ps)
     (for/or ([p ps]) (occurs-free? x p))]))

; symbol? Formula -> boolean?
(define (occurs-bound? x p)
  (match p
    [(? symbol?) #f]
    [(list (or 'forall 'exists) a p)
     (or (eq? x a) (occurs-free? x p))]
    [(cons _ ps)
     (for/or ([p ps]) (occurs-bound? x p))]))

; Formula Formula {(hash-of symbol? symbol?) (hash-of symbol? symbol?)} -> boolean?
; Does there exist a renaming of bound variables that makes
; the two formulae equal?
; The two hashes map bound vars to gensyms.
(define (alpha-eqv? p q [pvars (hasheq)] [qvars (hasheq)])
  (match* (p q)
    [((? symbol?) (? symbol?))
     (eq? (hash-ref pvars p p)
          (hash-ref qvars q q))]
    [((list quantifier a p) (list quantifier b q))
     #:when (member quantifier '(forall exists))
     (define v (gensym))
     (alpha-eqv? p q (hash-set pvars a v) (hash-set qvars b v))]
    [((cons op ps) (cons op qs))
     #:when (eq? (length ps) (length qs))
     (for/and ([p ps] [q qs])
       (alpha-eqv? p q pvars qvars))]
    [(_ _) #f]))

(module+ test
  (check-true (alpha-eqv? 'a 'a))
  (check-false (alpha-eqv? 'a 'b))
  (check-true (alpha-eqv? '(forall a a) '(forall b b)))
  (check-true (alpha-eqv? '(exists a a) '(exists b b)))
  (check-false (alpha-eqv? '(forall a a) '(exists b b)))
  (check-true (alpha-eqv? '(forall a (forall b (=> a b)))
                          '(forall b (forall c (=> b c)))))
  (check-false (alpha-eqv? '(forall a (forall b (=> a b)))
                           '(forall b (forall c (and b c)))))
  (check-false (alpha-eqv? '(forall a (forall b (=> a b)))
                           '(forall b (forall b (=> b b)))))
  (check-false (alpha-eqv? '(forall b (forall b (=> b b)))
                           '(forall a (forall b (=> a b)))))
  (check-false (alpha-eqv? '(forall a (forall b (=> a b)))
                           '(forall a (forall b (=> b a))))))

; rename bound variables in a repeatable way,
; such that alpha-equivalent formulae become equal?
(define (alpha-normalize p [count 0] [vars (hasheq)])
  (match p
    [(? symbol?)
     (hash-ref vars p p)]
    [(list quantifier a p)
     #:when (member quantifier '(forall exists))
     (define v (format-symbol "_.~a" count))
     (list quantifier v (alpha-normalize p (add1 count) (hash-set vars a v)))]
    [(cons op ps)
     (cons op (for/list ([p ps]) (alpha-normalize p count vars)))]))

(module+ test
  (check-equal? (alpha-normalize 'a) 'a)
  (check-equal? (alpha-normalize '(forall a a))
                '(forall _.0 _.0))
  (check-equal? (alpha-normalize '(forall b (forall b (=> b b))))
                '(forall _.0 (forall _.1 (=> _.1 _.1)))))

; theories

; Theory Proof -> InferenceTree
; check the proof of the theorem. If it is true, add it to the theory and return the inference tree.
(define (theory-add-theorem! thry proof)
  (match proof
    [(list (list ctx p) tree)
     ; TODO filter ctx in this check to those assumptions that were actually used?
     (unless (subcontext? ctx (theory->context thry))
       (error 'theory-add-theorem "proof of theorem must be valid under theory's context"))
     (begin0 (check-proof ctx p tree)
       (set-theory-theorems! thry (cons p (theory-theorems thry))))]))

; Theory -> Context
(define (theory->context thry)
  (context-union (apply context (theory-axioms thry))
                 (apply context (theory-theorems thry))))
