#lang racket/base

; peano on top of zfc

(require "./core.rkt"
         "./sugar.rkt"
         "./first-order-logic.rkt"
         ; left off here about to get rid of define all out so struct ids like struct:S and S? aren't exported
         (rename-in "./peano.rkt" [S NS])
         (rename-in "./zfc.rkt" [S SS])
         racket/match
         racket/set
         racket/struct)
(module+ test (require rackunit))
(provide (all-defined-out))

(define zero-definition (= zero empty-set))
