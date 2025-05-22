#lang racket

(require redex)
(require rackunit)

(define-language Λ
  (e ::= b x f (o e) (if e e e) (e e) (queue) (add! e e))
  (b ::= true false)
  (f ::= (λ (x) e))
  (o ::= null? head tail)
  (x y z ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ (x) e #:refers-to x))
(default-language Λ)

(define-extended-language Λ-eval
  Λ
  (ζ ::= (E σ))  ;; question: should the `e` be an `E`?
  (e ::= .... α (err j k))
  (v ::= b f a)
  (E ::= hole (o E) (if E e e) (E e) (v E) (add! E e) (add! v E))
  (u ::= null (cons v α))
  (σ ::= (aSto α u σ) mtSto)
  (α ::= natural)
  (j k l ::= x))

(define -->Λ
  (reduction-relation
   Λ-eval

   ;; Standard reduction rules
   [--> (((e_1 e_2) E) σ)
        ((e_1 (in-hole E (hole e_2))) σ)
        scc1]

   ;; changed to just one argument
   [--> (((o e) E) σ)
        ((e (in-hole E (o hole))) σ)
        scc2]

   ;; beta
   [--> ((v (in-hole E ((λ (x) e) hole))) σ)
        (((substitute e x v) E) σ)
        sccβ]

   ;; administrative rule: application pop+push
   [--> ((v (in-hole E (hole e))) σ)
        ((e (in-hole E (v hole))) σ)
        scc3]

   ;; administrative rule: primitive operation pop+push
   #;
   [--> ((v (in-hole E (o v_1 ... hole e_1 e_2 ...))) σ)
        ((e_1 (in-hole E (o v_1 ... v hole e_2 ...))) σ)
        scc4]

   ;; delta
   ;; changed b/c primitive operations only take one argument
   [--> ((v (in-hole E (o hole))) σ)
        (((delta o v σ) E) σ)
        sccδ]

   ;; New rules from paper:
   [--> ((v (in-hole E (if hole e_1 e_2))) σ)
        ((e_1 E) σ)
        (side-condition (not (equal? (term v) (term false))))
        if-true]
   
   [--> ((false (in-hole E (if hole e_1 e_2))) σ)
        ((e_2 E) σ)
        if-false]

   [--> (((queue) E) σ)
        (((next σ) E) σ)
        queue]

   [--> ((v (in-hole E (add! α hole))) σ)
        ((α E) (add σ α v))
        add!]

   [--> ((v (in-hole E (v_f hole))) σ)
        (((err runtime REPL) E) σ)
        ;; rule only fires if `v_f` is not a function
        (side-condition (not (redex-match? Λ-eval f (term v_f))))
        err-app]

   [--> ((v (in-hole E (add! v_q hole))) σ)
        (((err runtime REPL) E) σ)
        ;; rule only fires if `v_q` is not an address
        (side-condition (not (redex-match? Λ-eval α (term v_q))))
        err-add!]

   [--> (((err j k) E) σ)
        ((err j k) σ)
        ;; rule only fires if `E` is not a hole
        (side-condition (not (redex-match? Λ-eval hole (term E))))
        err-unwind]))

(define-metafunction Λ-eval
  next : σ -> α
  [(next null) ,0]
  [(next (aSto α_1 u_1 σ_2))
   (max (+ 1 α_1) (next σ_2))])
;; I don't think this works currently since `(next σ_2)` will return a Redex term but `max` wants Racket terms
;; - Nicholas DG
  #;#;
  [(next (aSto α_1 u_1 null))
   ,(+ 1 (term α_1))]
  [(next (aSto α_1 u_1 σ_2))
   (next σ_2)]

;; TODO: write unit tests for `next`

;; empty store

        
; ((v E) σ)
; (v E σ)
