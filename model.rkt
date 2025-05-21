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
  (e ::= ... α (err j k))
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
   
   [--> (((o e) E) σ)
        ((e (in-hole E (o hole))) σ)
        scc2]  ;; changed to just one argument

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
   ;; if-true
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

   ))

(define-metafunction Λ-eval
  next : σ -> α
  [(next null) ,0]
  [(next (aSto α_1 u_1 σ_2))
   (max (+ 1 α_1) (next σ_2))])
  #;#;
  [(next (aSto α_1 u_1 null))
   ,(+ 1 (term α_1))]
  [(next (aSto α_1 u_1 σ_2))
   (next σ_2)]

;; TODO: write unit tests for `next`

;; empty store

        
; ((v E) σ)
; (v E σ)
