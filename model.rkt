#lang racket

(require redex)
(require rackunit)


;
;
;    ;;;;                  ;
;   ;;   ;                 ;
;   ;      ;   ;  ; ;;   ;;;;;  ;;;;   ;   ;
;   ;;     ;   ;  ;;  ;    ;        ;   ; ;
;    ;;;;   ; ;   ;   ;    ;        ;   ;;;
;        ;  ; ;   ;   ;    ;     ;;;;    ;
;        ;  ; ;   ;   ;    ;    ;   ;   ;;;
;   ;    ;  ;;    ;   ;    ;    ;   ;   ; ;
;    ;;;;    ;    ;   ;    ;;;   ;;;;  ;   ;
;            ;
;           ;
;          ;;


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
  (ζ ::= (e σ))  ;; question: should the `e` be an `E`?
  (e ::= .... α (err j k))
  (v ::= b f a)
  (E ::= hole (o E) (if E e e) (E e) (v E) (add! E e) (add! v E))
  (u ::= null (cons v α))  ;; store values
  (σ ::= ((α u) ...))  ;; store
  (α ::= natural)
  (j k l ::= x))

;; I don't think the syntax is exactly correct here, but the idea is there
(define-metafunction Λ-eval
  delta : o v σ -> e  ;; TODO: is `e` the correct type or is there something more specific we can say?
  [(delta null? α ((α_1 u_1) ... (α null) (α_2 u_2) ...))
   true]
  [(delta null? α ((α_1 u_1) ... (α (cons v α_3)) (α_2 u_2) ...))
   false]

  [(delta head α ((α_1 u_1) ... (α null) (α_2 u_2) ...))
   (err runtime REPL)]
  [(delta head α ((α_1 u_1) ... (α (cons v α_3)) (α_2 u_2) ...))
   v]

  [(delta tail α ((α_1 u_1) ... (α null) (α_2 u_2) ...))
   (err runtime REPL)]
  [(delta tail α ((α_1 u_1) ... (α (cons v α_3)) (α_2 u_2) ...))
   α_3]

  ;; v ∉ Addr
  [(delta o v σ)
   (err runtime REPL)])

;; Test cases for `delta`
(test-equal (delta null? 0 ((0 null)))
            (term true))


(define-metafunction Λ-eval
  next : σ -> α
  [(next ()) ,0]
  [(next ((α_1 u_1) (α_2 u_2) ...))
   ,(+ 1 α_1)])


;; TODO: write unit tests for `next`

(define-metafunction Λ-eval
  extend : σ -> σ
  [(extend ((α_1 u_1) ...)) (((next σ) null) (α_1 u_1) ...)])


;
;                                   ;
;     ;;                            ;                  ;       ;
;     ;;                            ;                  ;
;     ;;           ;;;;   ;;;    ;;;;  ;   ;   ;;;   ;;;;;   ;;;    ;;;   ; ;;
;    ;  ;          ;;  ; ;;  ;  ;; ;;  ;   ;  ;;  ;    ;       ;   ;; ;;  ;;  ;
;    ;  ;          ;     ;   ;; ;   ;  ;   ;  ;        ;       ;   ;   ;  ;   ;
;    ;  ;          ;     ;;;;;; ;   ;  ;   ;  ;        ;       ;   ;   ;  ;   ;
;    ;  ;          ;     ;      ;   ;  ;   ;  ;        ;       ;   ;   ;  ;   ;
;   ;    ;         ;     ;      ;; ;;  ;   ;  ;;       ;       ;   ;; ;;  ;   ;
;   ;    ;         ;      ;;;;   ;;;;   ;;;;   ;;;;    ;;;   ;;;;;  ;;;   ;   ;
;
;
;


(define -->Λ
  (reduction-relation
   Λ-eval

   ;; beta
   [--> ((in-hole E ((λ (x) e) v)) σ)
        ((in-hole E (substitute e x v)) σ)
        Λβ]

   ;; delta
   [--> ((in-hole E (o v)) σ)
        ((in-hole E (delta o v σ)) σ)
        Λδ]

   ;; New rules from paper:
   [--> ((in-hole E (if v e_1 e_2)) σ)
        ((in-hole E e_1) σ)
        (side-condition (not (equal? (term v) (term false))))
        if-true]

   [--> ((in-hole E (if false e_1 e_2)) σ)
        ((in-hole E e_2) σ)
        if-false]

   [--> ((in-hole E (queue)) σ)
        ((in-hole E (next σ)) σ)
        queue]

   [--> ((v (in-hole E (add! α hole))) σ)
        ((α E) (add σ α v))
        add!]

   [--> ((v (in-hole E (v_f hole))) σ)
        (([err runtime REPL] E) σ)
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


;; Load and unload

(define (load-Λ p)
  (cond
    [(redex-match? Λ e p) (term (,p ()))]
    [else (raise "load: expected a valid program")]))

(define-metafunction Λ-eval
  unload-Λ : ζ -> v
  [(unload-Λ (v σ)) v])


;
;
;  ;;;;;;;                 ;       ;
;     ;                    ;
;     ;     ;;;    ;;;   ;;;;;   ;;;   ; ;;    ;;;;
;     ;    ;;  ;  ;   ;    ;       ;   ;;  ;  ;;  ;
;     ;    ;   ;; ;        ;       ;   ;   ;  ;   ;
;     ;    ;;;;;;  ;;;     ;       ;   ;   ;  ;   ;
;     ;    ;          ;    ;       ;   ;   ;  ;   ;
;     ;    ;      ;   ;    ;       ;   ;   ;  ;; ;;
;     ;     ;;;;   ;;;     ;;;   ;;;;; ;   ;   ;;;;
;                                                 ;
;                                              ;  ;
;                                               ;;


(test-equal
 (term
  (unload-Λ
   ,(first
     (apply-reduction-relation*
      -->Λ
      (load-Λ (term ((λ (x) true) false)))))))
 (term true))
