#lang racket

(require redex)
(require rackunit)


;; =============================================================================
;;                                SECTION 1 : Λ
;; =============================================================================

;
;
;     ;;                                 ;
;     ;;                                 ;
;     ;;           ;;;   ;   ;  ; ;;   ;;;;;  ;;;;   ;   ;
;    ;  ;         ;   ;  ;   ;  ;;  ;    ;        ;   ; ;
;    ;  ;         ;       ; ;   ;   ;    ;        ;   ;;;
;    ;  ;          ;;;    ; ;   ;   ;    ;     ;;;;    ;
;    ;  ;             ;   ; ;   ;   ;    ;    ;   ;   ;;;
;   ;    ;        ;   ;   ;;    ;   ;    ;    ;   ;   ; ;
;   ;    ;         ;;;     ;    ;   ;    ;;;   ;;;;  ;   ;
;                          ;
;                         ;
;                        ;;


(define-language Λ
  (e ::= b x f (o e ...) (if e e e) (e e) (queue) (add! e e) (seqn e e ...))
  (b ::= true false)
  (f ::= (λ (x) e))
  (o ::= null? head tail consistent? alternating? ==? tt? ff?)
  (x y z ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ (x) e #:refers-to x))
(default-language Λ)

(define-extended-language Λ-eval
  Λ
  (ζ ::= (e σ))
  (e ::= .... α (err j k))
  (v ::= b f α)
  (non-fun ::= b α)  ;; not in paper; added to simplify err-app case
  (E ::= hole (o v ... E e ...) (if E e e) (E e) (v E) (add! E e) (add! v E) (seqn v ... E e ...))
  (u ::= null (cons v α))  ;; store values
  (σ ::= ((α u) ...))  ;; store
  (α ::= natural)
  (j k l ::= x))

;; `(err j k)` denotes an error with two labels:
;; j names the party that specified the violated contract, and
;; k names the party that violated the contract


;
;                                  ;;
;  ;;  ;;           ;             ;                           ;       ;
;  ;;  ;;           ;             ;                           ;
;  ;;  ;;   ;;;   ;;;;;  ;;;;   ;;;;;  ;   ;  ; ;;    ;;;   ;;;;;   ;;;    ;;;   ; ;;    ;;;
;  ; ;; ;  ;;  ;    ;        ;    ;    ;   ;  ;;  ;  ;;  ;    ;       ;   ;; ;;  ;;  ;  ;   ;
;  ; ;; ;  ;   ;;   ;        ;    ;    ;   ;  ;   ;  ;        ;       ;   ;   ;  ;   ;  ;
;  ;    ;  ;;;;;;   ;     ;;;;    ;    ;   ;  ;   ;  ;        ;       ;   ;   ;  ;   ;   ;;;
;  ;    ;  ;        ;    ;   ;    ;    ;   ;  ;   ;  ;        ;       ;   ;   ;  ;   ;      ;
;  ;    ;  ;        ;    ;   ;    ;    ;   ;  ;   ;  ;;       ;       ;   ;; ;;  ;   ;  ;   ;
;  ;    ;   ;;;;    ;;;   ;;;;    ;     ;;;;  ;   ;   ;;;;    ;;;   ;;;;;  ;;;   ;   ;   ;;;
;
;
;

;; Convert a Racket boolean to a Λ boolean
(define (Λ->bool t)
  (cond [(eq? t (term true)) #t]
        [(eq? t (term false)) #f]))

;; Convert a Λ boolean to a Racket boolean
(define (bool->Λ b)
  (if b (term true) (term false)))

(define-metafunction Λ-eval
  delta : o v ... σ -> e
  ;; null?
  [(delta null? α ((α_1 u_1) ... (α null) (α_2 u_2) ...))
   true]
  [(delta null? α ((α_1 u_1) ... (α (cons v α_3)) (α_2 u_2) ...))
   false]

  ;; head
  [(delta head α ((α_1 u_1) ... (α null) (α_2 u_2) ...))
   (err runtime REPL)]
  [(delta head α ((α_1 u_1) ... (α (cons v α_3)) (α_2 u_2) ...))
   v]

  ;; tail
  [(delta tail α ((α_1 u_1) ... (α null) (α_2 u_2) ...))
   (err runtime REPL)]
  [(delta tail α ((α_1 u_1) ... (α (cons v α_3)) (α_2 u_2) ...))
   α_3]

  ;; CONVENIENCE: we have added several queue operations not included in the
  ;; paper, namely the `consistent?` and `alternating?` predicates. This is
  ;; for the sake of legibility, since traces quickly become a mess when using
  ;; the Y-combinator.

  ;; consistent?
  [(delta consistent? α ((α_1 u_1) ... (α null) (α_2 u_2) ...))
   true]

  [(delta consistent? α σ)
   true
   (where ((_ _) ... (α   (cons _ α_t)) (_ _) ...) σ)
   (where ((_ _) ... (α_t null)         (_ _) ...) σ)]

  [(delta consistent? α σ)
   ,(bool->Λ
     (and (boolean=? (Λ->bool (term v_1)) (Λ->bool (term v_2)))
          (Λ->bool (term (delta consistent? α_t σ)))))
   (where ((_ _) ... (α   (cons v_1 α_t)) (_ _) ...) σ)
   (where ((_ _) ... (α_t (cons v_2 _))   (_ _) ...) σ)]

  ;; alternating?
  [(delta alternating? α ((α_1 u_1) ... (α null) (α_2 u_2) ...))
   true]

  [(delta alternating? α σ)
   true
   (where ((_ _) ... (α   (cons _ α_t)) (_ _) ...) σ)
   (where ((_ _) ... (α_t null)         (_ _) ...) σ)]

  [(delta alternating? α σ)
   ,(bool->Λ
     (and (not (boolean=? (Λ->bool (term v_1)) (Λ->bool (term v_2))))
          (Λ->bool (term (delta alternating? α_t σ)))))
   (where ((_ _) ... (α   (cons v_1 α_t)) (_ _) ...) σ)
   (where ((_ _) ... (α_t (cons v_2 _))   (_ _) ...) σ)]

  ;; CONVENIENCE: we also added several boolean operations to maximize
  ;; trace legibility: tt?, ff?, and ==?

  [(delta tt? true σ) true]
  [(delta tt? false σ) false]

  [(delta ff? false σ) true]
  [(delta ff? true σ) false]

  [(delta ==? v v σ) true]
  [(delta ==? v_1 v_2 σ) false]

  ;; in any other case, throw an error
  [(delta o v ... σ)
   (err runtime REPL)])

(define-metafunction Λ-eval
  next : σ -> α
  [(next ())
   ,0]
  [(next ((α_1 u_1) (α_2 u_2) ...))
   ,(+ 1 (term α_1))])

(define-metafunction Λ-eval
  extend : σ -> σ
  [(extend ((α_1 u_1) ...))
   ((α null) (α_1 u_1) ...)
   (where α (next ((α_1 u_1) ...)))])

(define-metafunction Λ-eval
  add : σ α v -> σ
  [(add ((α_1 u_1) ... (α_2 null) (α_3 u_3) ...) α_2 v)
   ((α_4 null) (α_1 u_1) ... (α_2 (cons v α_4)) (α_3 u_3) ...)
   (where α_4 (next ((α_1 u_1) ... (α_2 null) (α_3 u_3) ...)))]

  [(add ((α_1 u_1) ... (α_2 (cons v_2 α_4)) (α_3 u_3) ...) α_2 v)
   (add σ_1 α_4 v)
   (where σ_1 ((α_1 u_1) ... (α_2 (cons v_2 α_4)) (α_3 u_3) ...))])


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
   [--> ((in-hole E (o v ...)) σ)
        ((in-hole E (delta o v ... σ)) σ)
        Λδ]

   ;; sequenced operations
   [--> ((in-hole E (seqn v_1 ... v_2)) σ)
        ((in-hole E v_2) σ)
        Λseqn]

   ;; New rules from paper:
   [--> ((in-hole E (if v e_1 e_2)) σ)
        ((in-hole E e_1) σ)
        (side-condition (not (equal? (term v) (term false))))
        if-true]

   [--> ((in-hole E (if false e_1 e_2)) σ)
        ((in-hole E e_2) σ)
        if-false]

   [--> ((in-hole E (queue)) σ)
        ((in-hole E (next σ)) (extend σ))
        queue]

   [--> ((in-hole E (add! α v)) σ)
        ((in-hole E α) (add σ α v))
        add!]

   ;; TODO/question: will hardcoding `(err runtime REPL)` cause issues when we
   ;; get to a language that can have more nuanced errors?
   [--> ((in-hole E (non-fun v)) σ)
        ((in-hole E (err runtime REPL)) σ)
        ;; rule only fires if `v_f` is not a function
        ;(side-condition (not (redex-match? Λ-eval f (term v_f))))
        err-app]

   [--> ((in-hole E (add! v_q v)) σ)
        ((in-hole E (err runtime REPL)) σ)
        ;; rule only fires if `v_q` is not an address
        (side-condition (not (redex-match? Λ-eval α (term v_q))))
        err-add!]

   [--> ((in-hole E (err j k)) σ)
        ((err j k) σ)
        ;; rule only fires if `E` is not a hole
        (side-condition (not (redex-match? Λ-eval hole (term E))))
        err-unwind]))


;; Load, unload, eval

(define (load-Λ p)
  (cond
    [(redex-match? Λ e p) (term (,p ()))]
    [else (raise (string-append "load-Λ: expected a valid program, received: " (~a p)))]))

(define-metafunction Λ-eval
  unload-Λ : ζ -> e
  [(unload-Λ (v σ)) v]
  [(unload-Λ ((err j k) σ)) (err j k)])

(define (eval-Λ t)
  (term
   (unload-Λ
    ,(first
      (apply-reduction-relation*
       -->Λ
       (load-Λ t))))))

;
;
;     ;;            ;                    ;
;     ;;            ;                    ;
;     ;;          ;;;;;   ;;;    ;;;   ;;;;;   ;;;
;    ;  ;           ;    ;;  ;  ;   ;    ;    ;   ;
;    ;  ;           ;    ;   ;; ;        ;    ;
;    ;  ;           ;    ;;;;;;  ;;;     ;     ;;;
;    ;  ;           ;    ;          ;    ;        ;
;   ;    ;          ;    ;      ;   ;    ;    ;   ;
;   ;    ;          ;;;   ;;;;   ;;;     ;;;   ;;;
;
;
;

(test-equal
 (eval-Λ (term ((λ (x) true) false)))
 (term true))

(test-equal
 (eval-Λ (term (queue)))
 (term 0))

(test-equal
 (eval-Λ (term (null? (queue))))
 (term true))

(test-equal
 (eval-Λ (term (head (add! (queue) false))))
 (term false))

(test-equal
 (eval-Λ (term (tail (add! (queue) false))))
 (term 1))

(test-equal
 (eval-Λ (term (head (add! (add! (queue) false) true))))
 (term false))

(test-equal
 (eval-Λ (term (if (head (add! (add! (queue) false) true))
                   true
                   (head (add! (add! (add! (queue) (λ (x) x)) (λ (x) false)) false)))))
 (term (λ (x) x)))

;; TODO: test `seqn`

;; Errors ======================================================================

;; err-app case
;; function application with a non-function
(test-equal
 (eval-Λ (term (true false)))
 (term (err runtime REPL)))

;; err-add! case
;; attempting to add to a non-address
(test-equal
 (eval-Λ (term (add! true true)))
 (term (err runtime REPL)))

;; primitive operation errors
(test-equal
 (eval-Λ (term (null? true)))
 (term (err runtime REPL)))

(test-equal
 (eval-Λ (term (head false)))
 (term (err runtime REPL)))

(test-equal
 (eval-Λ (term (tail (λ (x) x))))
 (term (err runtime REPL)))


;; =============================================================================
;;                                SECTION 2 : ΛC
;; =============================================================================

;
;
;     ;;     ;;;                                ;
;     ;;    ;   ;                               ;
;     ;;   ;              ;;;   ;   ;  ; ;;   ;;;;;  ;;;;   ;   ;
;    ;  ;  ;             ;   ;  ;   ;  ;;  ;    ;        ;   ; ;
;    ;  ;  ;             ;       ; ;   ;   ;    ;        ;   ;;;
;    ;  ;  ;              ;;;    ; ;   ;   ;    ;     ;;;;    ;
;    ;  ;  ;                 ;   ; ;   ;   ;    ;    ;   ;   ;;;
;   ;    ;  ;   ;        ;   ;   ;;    ;   ;    ;    ;   ;   ; ;
;   ;    ;   ;;;          ;;;     ;    ;   ;    ;;;   ;;;;  ;   ;
;                                 ;
;                                ;
;                               ;;


;; `(e_d ->i e_c)` is a dependent function contract.
;; The codomain contract, e_c, can depend on the argument to the protected function.

;; `(mon j k l e_κ e_c)` is a monitor that attaches contract e_κ to e_c.
;; The value of e_c is dubbed the "carrier" of the contract.
;; j, k, and l name the parties that agreed to the contract.

;; monitor labels:
;; - j :: contract-defining module
;; - k :: server module
;; - l :: client module

;; KEY IDEA: monitors are what Kaylie and Joanna called "obligations"

(define-extended-language ΛC
  Λ
  (e ::= ....
     (e ->i e)            ;; dependent function contract
     (mon j k l e_κ e_c)) ;; three-label monitor
  (j k l ::= x))          ;; label

(define-union-language ΛC∪Λ-eval ΛC Λ-eval)

(define-extended-language ΛC-eval
  ;; inherit surface syntax from ΛC and evaluation syntax from Λ-eval
  ΛC∪Λ-eval
  (e ::= ....
     (mon j k e e) ;; two-label monitor
     (grd j k ω v) ;; guard
     (e · l))      ;; label application
  (v ::= .... κ (grd j k ω v))
  (non-fun ::= .... (v ->i v) (grd j k ω v))  ;; values that are not functions (not in paper)
  (κ ::= b (λ (x) e) (v ->i v))
  (non-con ::= α (grd j k ω v))  ;; values that are not contracts (not in paper)
  (ω ::= true (v ->i v))
  (E ::= .... (E ->i e) (v ->i E) (mon j k E e) (mon j k v E) (E · l)))


;
;                                          ;
;     ;;     ;;;                           ;                  ;       ;
;     ;;    ;   ;                          ;                  ;
;     ;;   ;              ;;;;   ;;;    ;;;;  ;   ;   ;;;   ;;;;;   ;;;    ;;;   ; ;;
;    ;  ;  ;              ;;  ; ;;  ;  ;; ;;  ;   ;  ;;  ;    ;       ;   ;; ;;  ;;  ;
;    ;  ;  ;              ;     ;   ;; ;   ;  ;   ;  ;        ;       ;   ;   ;  ;   ;
;    ;  ;  ;              ;     ;;;;;; ;   ;  ;   ;  ;        ;       ;   ;   ;  ;   ;
;    ;  ;  ;              ;     ;      ;   ;  ;   ;  ;        ;       ;   ;   ;  ;   ;
;   ;    ;  ;   ;         ;     ;      ;; ;;  ;   ;  ;;       ;       ;   ;; ;;  ;   ;
;   ;    ;   ;;;          ;      ;;;;   ;;;;   ;;;;   ;;;;    ;;;   ;;;;;  ;;;   ;   ;
;
;
;


(define -->ΛC
  (extend-reduction-relation
   -->Λ
   ΛC-eval

   [--> ((in-hole E (mon j k l e_κ e)) σ)
        ((in-hole E ((mon j k e_κ e) · l)) σ)
        mon-apply]

   [--> ((in-hole E (mon j k true v)) σ)
        ((in-hole E (grd j k true v)) σ)
        mon-true]

   [--> ((in-hole E (mon j k false v)) σ)
        ((in-hole E (err j k)) σ)
        mon-false]

   [--> ((in-hole E (mon j k (λ (x) e) v)) σ)
        ((in-hole E (mon j k ((λ (x) e) v) v)) σ)
        mon-flat]

   [--> ((in-hole E (mon j k (v_d ->i v_c) v)) σ)
        ((in-hole E (grd j k (v_d ->i v_c) v)) σ)
        mon-fun]

   [--> ((in-hole E ((grd j k true v) · l)) σ)
        ((in-hole E v) σ)
        grd-true]

   [--> ((in-hole E ((grd j k (v_d ->i v_c) v) · l)) σ)
        ((in-hole E (λ (x)
                      ((λ (x_g)
                        ((λ (x_j)
                           ((λ (x_k) (mon j k l (v_c x_j) (v x_k)))
                            (x_g · k)))   ;; let x_k = (x_g · k)
                         (x_g · j)))      ;; let x_j = (x_g · j)
                      (mon j l v_d x))))  ;; let x_g = (mon j l v_d x)
         σ)
        ;; we can't use "where", since it does not evaluate arguments before
        ;; substituting. Instead, since the language does not have
        ;; "let"-bindings, we use function application
        grd-fun]

   [--> ((in-hole E (mon j k non-con v)) σ)
        ((in-hole E (err runtime REPL)) σ)
        ;(side-condition (not (redex-match? ΛC-eval κ (term v_κ))))
        err-mon]))


(define (load-ΛC p)
  (cond
    [(redex-match? ΛC e p) (term (,p ()))]
    [else (raise (string-append "load-ΛC: expected a valid program, received: " (~a p)))]))

(define-metafunction ΛC-eval
  unload-ΛC : ζ -> e
  [(unload-ΛC (v σ)) v]
  [(unload-ΛC ((err j k) σ)) (err j k)])

(define (eval-ΛC t)
  (term
   (unload-ΛC
    ,(first
      (apply-reduction-relation*
       -->ΛC
       (load-ΛC t))))))


;
;
;     ;;     ;;;           ;                    ;
;     ;;    ;   ;          ;                    ;
;     ;;   ;             ;;;;;   ;;;    ;;;   ;;;;;   ;;;
;    ;  ;  ;               ;    ;;  ;  ;   ;    ;    ;   ;
;    ;  ;  ;               ;    ;   ;; ;        ;    ;
;    ;  ;  ;               ;    ;;;;;;  ;;;     ;     ;;;
;    ;  ;  ;               ;    ;          ;    ;        ;
;   ;    ;  ;   ;          ;    ;      ;   ;    ;    ;   ;
;   ;    ;   ;;;           ;;;   ;;;;   ;;;     ;;;   ;;;
;
;
;


;; Λ tests using -->ΛC to make sure that ΛC correctly extends Λ ================
(test-equal
 (eval-ΛC (term ((λ (x) true) false)))
 (term true))

(test-equal
 (eval-ΛC (term (queue)))
 (term 0))

(test-equal
 (eval-ΛC (term (null? (queue))))
 (term true))

(test-equal
 (eval-ΛC (term (head (add! (queue) false))))
 (term false))

(test-equal
 (eval-ΛC (term (tail (add! (queue) false))))
 (term 1))

(test-equal
 (eval-ΛC (term (head (add! (add! (queue) false) true))))
 (term false))

(test-equal
 (eval-ΛC (term (if (head (add! (add! (queue) false) true))
                    true
                    (head (add! (add! (add! (queue) (λ (x) x)) (λ (x) false)) false)))))
 (term (λ (x) x)))


;; ===================

;; TODO: Something that's a value in ΛC but not in Λ
;(term (grd j k true false)



;; Booleans as contracts =======================================================
(test-equal
 (eval-ΛC (term (mon j k l
                     true
                     false)))
 (term false))

(test-equal
 (eval-ΛC (term (mon ctc lib main
                     true
                     false)))
 (term false))

(test-equal
 (eval-ΛC (term ((mon ctc lib main
                      true
                      (λ (x) x))
                 true)))
 (term true))

(test-equal
 (eval-ΛC (term (mon j k l
                     (if true true (queue))
                     (λ (x) x))))
 (term (λ (x) x)))

(test-equal
 (eval-ΛC (term (mon j k l
                     false
                     true)))
 (term (err j k)))

(test-equal
 (eval-ΛC (term (mon ctc lib main
                     false
                     (λ (x) x))))
 (term (err ctc lib)))


;; Functions as contracts ======================================================
;; (mon j k l (λ (x) e) v)

;; ====================
;; |  Flat contracts  |
;; ====================
;; i.e. the function used as the contract is a predicate (returns a boolean)
(test-equal
 (eval-ΛC (term (mon j k l
                     (λ (x) true)
                     false)))
 (term false))

(test-equal
 (eval-ΛC (term (mon j k l
                     (λ (x) false)
                     false)))
 (term (err j k)))

(test-equal
 (eval-ΛC (term (mon j k l
                     (λ (v) (tt? v))
                     false)))
 (term (err j k)))

(test-equal
 (eval-ΛC (term (mon j k l
                     (λ (v) (ff? v))
                     false)))
 (term false))

;; Contract that accepts only true values
(test-equal
 (eval-ΛC (term (mon j k l
                     (λ (x) x)
                     true)))
 (term true))

(test-equal
 (eval-ΛC (term (mon j k l
                     (λ (x) x)
                     false)))
 (term (err j k)))

;; =========================
;; |  Cascading contracts  |
;; =========================
;; i.e. the function used as the contract returns a function contract

;; TODO


;; Arrow contracts =============================================================

;; =======================
;; |  Identity function  |
;; =======================

;; This contract is not as expressive as it could be since we don't have many
;; primitive operations at our disposal.
(test-equal
 (eval-ΛC (term ((mon j k l
                      (true ->i (λ (in) (λ (out) (==? in out))))
                      (λ (z) z))
                 false)))
 (term false))
(test-equal
 (eval-ΛC (term ((mon j k l
                      (true ->i (λ (in) (λ (out) (==? in out))))
                      (λ (z) z))
                 true)))
 (term true))

;; This new function doesn't satisfy the contract for the identity function.
;; Contract blames the server module because it defined the function in a way that
;; doesn't satisfy the contract.
(test-equal
 (eval-ΛC (term ((mon ctc serv client
                      (true ->i (λ (in) (λ (out) (==? in out))))
                      (λ (z) (ff? z)))
                 true)))
 (term (err ctc serv)))
(test-equal
 (eval-ΛC (term ((mon ctc serv client
                      (true ->i (λ (in) (λ (out) (==? in out))))
                      (λ (z) (ff? z)))
                 false)))
 (term (err ctc serv)))


;; =======================================================
;; |  Contract that restricts the input type to `false`  |
;; =======================================================
(test-equal
 (eval-ΛC (term ((mon j k l
                      ((λ (v) (ff? v)) ->i (λ (in) true))
                      (λ (x) x))
                 false)))
 (term false))

(test-equal
 (eval-ΛC (term ((mon ctc serv client
                      ((λ (v) (ff? v)) ->i (λ (in) true))
                      (λ (x) x))
                 true)))
 (term (err ctc client)))
;; Blames the client module because it passed in the wrong thing (`true`)


;; TODO: more arrow contracts


;; Effects aren't duplicated ===================================================
(test-equal
 (first
  (apply-reduction-relation*
   -->ΛC
   (load-ΛC (term ((mon j k l
                        ((λ (in) (seqn (add! (queue) in)
                                       true))
                         ->i
                         (λ (x) true))
                        (λ (x) x))
                   true)))))
 '(true ((1 null) (0 (cons true 1)))))


;; Contract itself is inconsistent =============================================
;; e.g. `(bool? -> bool?) ->i (λ (f) (f 42))` from paper, p. 16

;; TODO


;; Attempting to attach an address (rather than a contract) to an expression ===
(test-equal
 (eval-ΛC (term (mon j k l (queue) true)))
 (term (err runtime REPL)))

(test-equal
 (eval-ΛC (term (mon j k l (add! (queue) false) true)))
 (term (err runtime REPL)))

(test-equal
 (eval-ΛC (term (mon j k l (if true (queue) true) (λ (x) x))))
 (term (err runtime REPL)))

(test-equal
 (eval-ΛC (term (mon j k l (if false true (queue)) (λ (x) x))))
 (term (err runtime REPL)))

;; TODO: attempting to attach other things that aren't addresses or contracts?


;; Higher-order function contracts =============================================
;; (multiple arrows)

;; TODO


;; =============================================================================
;;                                SECTION 3 : ΛT
;; =============================================================================

;
;
;     ;;   ;;;;;;;                              ;
;     ;;      ;                                 ;
;     ;;      ;           ;;;   ;   ;  ; ;;   ;;;;;  ;;;;   ;   ;
;    ;  ;     ;          ;   ;  ;   ;  ;;  ;    ;        ;   ; ;
;    ;  ;     ;          ;       ; ;   ;   ;    ;        ;   ;;;
;    ;  ;     ;           ;;;    ; ;   ;   ;    ;     ;;;;    ;
;    ;  ;     ;              ;   ; ;   ;   ;    ;    ;   ;   ;;;
;   ;    ;    ;          ;   ;   ;;    ;   ;    ;    ;   ;   ; ;
;   ;    ;    ;           ;;;     ;    ;   ;    ;;;   ;;;;  ;   ;
;                                 ;
;                                ;
;                               ;;

(define-extended-language ΛT
  ΛC
  (e ::= .... (tr e_κ e_p))) ;; trace contract

;; trace contract parameters:
;; - e_κ :: body-contract constructor. function that, provided with a collector,
;;          returns a body contract
;; - e_p :: trace predicate

(define-union-language ΛT∪ΛC-eval ΛT ΛC-eval)

(define-extended-language ΛT-eval
  ;; surface syntax from ΛT and evaluation syntax from ΛC-eval
  ΛT∪ΛC-eval
  (e ::= .... (co α v_p))
  (non-fun ::= .... (tr v v) (co α v))  ;; (not in paper)
  (κ ::= .... (tr v v) (co α v))
  (E ::= .... (tr E e) (tr v E)))

;; collector parameters:
;; - α :: address of trace in the store
;; - v :: trace predicate

;
;                                          ;
;     ;;   ;;;;;;;                         ;                  ;       ;
;     ;;      ;                            ;                  ;
;     ;;      ;           ;;;;   ;;;    ;;;;  ;   ;   ;;;   ;;;;;   ;;;    ;;;   ; ;;
;    ;  ;     ;           ;;  ; ;;  ;  ;; ;;  ;   ;  ;;  ;    ;       ;   ;; ;;  ;;  ;
;    ;  ;     ;           ;     ;   ;; ;   ;  ;   ;  ;        ;       ;   ;   ;  ;   ;
;    ;  ;     ;           ;     ;;;;;; ;   ;  ;   ;  ;        ;       ;   ;   ;  ;   ;
;    ;  ;     ;           ;     ;      ;   ;  ;   ;  ;        ;       ;   ;   ;  ;   ;
;   ;    ;    ;           ;     ;      ;; ;;  ;   ;  ;;       ;       ;   ;; ;;  ;   ;
;   ;    ;    ;           ;      ;;;;   ;;;;   ;;;;   ;;;;    ;;;   ;;;;;  ;;;   ;   ;
;
;
;

(define -->ΛT
  (extend-reduction-relation
   -->ΛC
   ΛT-eval

   [--> ((in-hole E (mon j k (tr v_b v_p) v)) σ)
        ((in-hole E (mon j k (v_b (co α v_p)) v)) σ_1)
        (where α (next σ))
        (where σ_1 (extend σ))
        mon-trace]

   [--> ((in-hole E (mon j k (co α v_p) v)) σ)
        ((in-hole E (mon j k (v_p (add! α v)) v)) σ)
        mon-col]))


(define (load-ΛT p)
  (cond
    [(redex-match? ΛT e p) (term (,p ()))]
    [else (raise (string-append "load-ΛT: expected a valid program, received: " (~a p)))]))

(define-metafunction ΛT-eval
  unload-ΛT : ζ -> e
  [(unload-ΛT (v σ)) v]
  [(unload-ΛT ((err j k) σ)) (err j k)])

(define (eval-ΛT t)
  (term
   (unload-ΛT
    ,(first
      (apply-reduction-relation*
       -->ΛT
       (load-ΛT t))))))

;
;
;     ;;   ;;;;;;;         ;                    ;
;     ;;      ;            ;                    ;
;     ;;      ;          ;;;;;   ;;;    ;;;   ;;;;;   ;;;
;    ;  ;     ;            ;    ;;  ;  ;   ;    ;    ;   ;
;    ;  ;     ;            ;    ;   ;; ;        ;    ;
;    ;  ;     ;            ;    ;;;;;;  ;;;     ;     ;;;
;    ;  ;     ;            ;    ;          ;    ;        ;
;   ;    ;    ;            ;    ;      ;   ;    ;    ;   ;
;   ;    ;    ;            ;;;   ;;;;   ;;;     ;;;   ;;;
;
;
;

;; Test to match the ΛU test
;; Trace contract that imposes no constraints on the carrier
(test-equal
 (eval-ΛT
  (term
   ((mon j k l
         (tr (λ (coll) (true ->i (λ (x) coll)))
             (λ (addr) true))
         (λ (z) z))
    false)))
 (term false))


;; Body contract tests =========================================================

;; Note the modules in effect:
;; - contract module :: ctc
;; - server module   :: lib
;; - client module   :: main

;; Trace contract that collects function results, accepts all traces
(test-equal
 (eval-ΛT (term ((λ (f) (f false))
                 (mon ctc lib main
                      (tr (λ (coll) ((λ (v) (ff? v)) ->i (λ (in) coll)))
                          (λ (trace) true))
                      (λ (x) false)))))
 (term false))

#;
(traces -->ΛT
        (term (((λ (f) (f false))
                (mon ctc lib main
                     (tr (λ (coll) ((λ (v) (ff? v)) ->i (λ (in) coll)))
                         (λ (trace) true))
                     (λ (x) false)))
               ())))

;; ... Above, but the argument is incorrect
(test-equal
 (eval-ΛT (term ((λ (f) (f true))
                 (mon ctc lib main
                      (tr (λ (coll) ((λ (v) (ff? v)) ->i (λ (in) coll)))
                          (λ (trace) true))
                      (λ (x) false)))))
 (term (err ctc main)))
;; main gets blamed since it provides an input to `f` that violates the contract

;; Trace contract that collects function arguments, accepts all traces
(test-equal
 (eval-ΛT (term ((λ (f) (f false))
                 (mon ctc lib main
                      (tr (λ (coll) (coll ->i (λ (in) (λ (out) (ff? out)))))
                          (λ (trace) true))
                      (λ (x) false)))))
 (term false))

;; ... Above, but function is incorrect
(test-equal
 (eval-ΛT (term ((λ (f) (f false))
                 (mon ctc lib main
                      (tr (λ (coll) (coll ->i (λ (in) (λ (out) (ff? out)))))
                          (λ (trace) true))
                      (λ (x) true)))))
 (term (err ctc lib)))
;; lib gets blamed since it defines `f` in a way that violates the contract

;; Trace predicate tests =======================================================

;; Trace contract that rejects all traces, blaming main
(test-equal
 (eval-ΛT (term ((λ (f) (f false))
                 (mon ctc lib main
                      (tr (λ (coll) (coll ->i (λ (in) true)))
                          (λ (trace) false)) ;; pred returns false
                      (λ (x) true)))))
 ;; main gets blamed, since it produced the collected value
 (term (err ctc main)))

;; Trace contract that rejects all traces, blaming lib
(test-equal
 (eval-ΛT (term ((λ (f) (f false))
                 (mon ctc lib main
                      (tr (λ (coll) (true ->i (λ (in) coll)))
                          (λ (trace) false)) ;; pred returns false
                      (λ (x) true)))))

 ;; lib gets blamed, since it produced the collected value
 (term (err ctc lib)))

;; Function that produces the same value every time (server blame ex.)
(test-equal
 (eval-ΛT (term ((λ (f) (seqn (f true)
                              (f true)
                              (f true)
                              (f true)))
                 (mon ctc lib main
                      (tr (λ (coll) (true ->i (λ (in) coll)))
                          (λ (q) (consistent? q)))
                      (λ (x) x)))))
 (term true))

;; ... Above, trying all false return values
(test-equal
 (eval-ΛT (term ((λ (f) (seqn (f false)
                              (f false)
                              (f false)
                              (f false)))
                 (mon ctc lib main
                      (tr (λ (coll) (true ->i (λ (in) coll)))
                          (λ (q) (consistent? q)))
                      (λ (x) x)))))
 (term false))

;; ... Above, but trace violates predicate
(test-equal
 (eval-ΛT (term ((λ (f) (seqn (f false)
                              (f false)
                              (f true)
                              (f false)))
                 (mon ctc lib main
                      (tr (λ (coll) (true ->i (λ (in) coll)))
                          (λ (q) (consistent? q)))
                      (λ (x) x)))))
 ;; lib gets blamed, since it promised identical return values
 (term (err ctc lib)))

;; Function that accepts an alternating stream (client blame ex.)
(test-equal
 (eval-ΛT (term ((λ (f) (seqn (f true)
                              (f false)
                              (f true)
                              (f false)))
                 (mon ctc lib main
                      (tr (λ (coll) (coll ->i (λ (in) true)))
                          (λ (q) (alternating? q)))
                      (λ (x) true)))))
 (term true))

;; ... Above, but trace violates predicate
(test-equal
 (eval-ΛT (term ((λ (f) (seqn (f true)
                              (f false)
                              (f false)
                              (f true)))
                 (mon ctc lib main
                      (tr (λ (coll) (coll ->i (λ (in) true)))
                          (λ (q) (alternating? q)))
                      (λ (x) true)))))
 ;; main gets blamed, since it produced the collected value
 (term (err ctc main)))


;; =============================================================================
;;                                SECTION 4 : ΛU
;; =============================================================================

;
;
;     ;;   ;    ;                               ;
;     ;;   ;    ;                               ;
;     ;;   ;    ;         ;;;   ;   ;  ; ;;   ;;;;;  ;;;;   ;   ;
;    ;  ;  ;    ;        ;   ;  ;   ;  ;;  ;    ;        ;   ; ;
;    ;  ;  ;    ;        ;       ; ;   ;   ;    ;        ;   ;;;
;    ;  ;  ;    ;         ;;;    ; ;   ;   ;    ;     ;;;;    ;
;    ;  ;  ;    ;            ;   ; ;   ;   ;    ;    ;   ;   ;;;
;   ;    ; ;    ;        ;   ;   ;;    ;   ;    ;    ;   ;   ; ;
;   ;    ;  ;;;;          ;;;     ;    ;   ;    ;;;   ;;;;  ;   ;
;                                 ;
;                                ;
;                               ;;

;; `(tr v_κ v_b v_p)`
;; v_b and v_p are the same as in ΛT, i.e.:
;; - v_b :: body contract constructor
;; - v_p :: trace predicate

;; v_κ pairs each trace variable with a contract that governs collected values.

(define-extended-language ΛU
  ΛC
  (e ::= .... (tr e e e)))

(define-union-language ΛU∪ΛC-eval ΛU ΛC-eval)

(define-extended-language ΛU-eval
  ΛU∪ΛC-eval
  (e ::= .... (co v α v))
  (non-fun ::= .... (tr v v v) (co v α v))  ;; (not in paper)
  (κ ::= .... (tr v v v) (co v α v))
  (E ::= .... (tr E e e) (tr v E e) (tr v v E)))

;
;                                          ;
;     ;;   ;    ;                          ;                  ;       ;
;     ;;   ;    ;                          ;                  ;
;     ;;   ;    ;         ;;;;   ;;;    ;;;;  ;   ;   ;;;   ;;;;;   ;;;    ;;;   ; ;;
;    ;  ;  ;    ;         ;;  ; ;;  ;  ;; ;;  ;   ;  ;;  ;    ;       ;   ;; ;;  ;;  ;
;    ;  ;  ;    ;         ;     ;   ;; ;   ;  ;   ;  ;        ;       ;   ;   ;  ;   ;
;    ;  ;  ;    ;         ;     ;;;;;; ;   ;  ;   ;  ;        ;       ;   ;   ;  ;   ;
;    ;  ;  ;    ;         ;     ;      ;   ;  ;   ;  ;        ;       ;   ;   ;  ;   ;
;   ;    ; ;    ;         ;     ;      ;; ;;  ;   ;  ;;       ;       ;   ;; ;;  ;   ;
;   ;    ;  ;;;;          ;      ;;;;   ;;;;   ;;;;   ;;;;    ;;;   ;;;;;  ;;;   ;   ;
;
;
;

(define -->ΛU
  (extend-reduction-relation
   -->ΛC
   ΛU-eval
   
   [--> ((in-hole E (mon j k (tr v_κ v_b v_p) v)) σ)
        ((in-hole E (mon j k (v_b (co v_κ α v_p)) v)) σ_2)
        (where α (next σ))
        (where σ_2 (extend σ))
        mon-trace]
   
   [--> ((in-hole E (mon j k (co v_κ α v_p) v)) σ)
        ((in-hole E (seqn (add! α e_j)
                          (mon j k (v_p α) v)
                          e_v))
         σ)
        (where e_v (mon j k v_κ v))
        (where e_j (e_v · j))
        mon-col]))


(define (load-ΛU p)
  (cond
    [(redex-match? ΛU e p) (term (,p ()))]
    [else (raise (string-append "load-ΛU: expected a valid program, received: " (~a p)))]))

(define-metafunction ΛU-eval
  unload-ΛU : ζ -> e
  [(unload-ΛU (v σ)) v]
  [(unload-ΛU ((err j k) σ)) (err j k)])

(define (eval-ΛU t)
  (term
   (unload-ΛU
    ,(first
      (apply-reduction-relation*
       -->ΛU
       (load-ΛU t))))))

;
;
;     ;;   ;    ;          ;                    ;
;     ;;   ;    ;          ;                    ;
;     ;;   ;    ;        ;;;;;   ;;;    ;;;   ;;;;;   ;;;
;    ;  ;  ;    ;          ;    ;;  ;  ;   ;    ;    ;   ;
;    ;  ;  ;    ;          ;    ;   ;; ;        ;    ;
;    ;  ;  ;    ;          ;    ;;;;;;  ;;;     ;     ;;;
;    ;  ;  ;    ;          ;    ;          ;    ;        ;
;   ;    ; ;    ;          ;    ;      ;   ;    ;    ;   ;
;   ;    ;  ;;;;           ;;;   ;;;;   ;;;     ;;;   ;;;
;
;
;

;; Output is collected
;; Every collected value must be `false`
(test-equal
 (eval-ΛU
  (term
   ((mon ctc serv client
         (tr (λ (tr-var) (ff? tr-var))
             (λ (coll) (true ->i (λ (in) coll)))
             (λ (addr) true))
         (λ (y) y))
    false)))
 (term false))

;; ... Same as above, but with input that makes the contract fail

;; Note that the input itself is not the problem, but rather the function was
;; broken all along, it just happened to output a value that satisfied the
;; contract in the case above.
(test-equal
 (eval-ΛU
  (term
   ((mon ctc serv client
         (tr (λ (tr-var) (ff? tr-var))
             (λ (coll) (true ->i (λ (in) coll)))
             (λ (addr) true))
         (λ (y) y))
    true)))
 (term (err ctc serv)))
;; Server module gets blamed since the server provided the function `(λ (x) true)`
;; that violates the contract

;; Input is collected
(test-equal
 (eval-ΛU
  (term
   ((mon ctc serv client
         (tr (λ (tr-var) (tt? tr-var))
             (λ (coll) (coll ->i (λ (in) true)))
             (λ (addr) true))
         (λ (y) y))
    true)))
 (term true))

;; ... Same as above, but with input that violates the contract
(test-equal
 (eval-ΛU
  (term
   ((mon ctc serv client
         (tr (λ (tr-var) (tt? tr-var))
             (λ (coll) (coll ->i (λ (in) true)))
             (λ (addr) true))
         (λ (y) y))
    false)))
 (term (err ctc client)))
;; Client module is blamed since it provides the input (false) that violates
;; the trace variable contract


;; =============================================================================
;;                              SECTION 5 : TRACES
;; =============================================================================

;; TODO write (commented-out) examples with traces for live demonstration


;; =============================================================================
;;                                APPENDIX : DELTA
;; =============================================================================

;
;     ;        ;                                ;
;      ;       ;         ;;;      ;              ;            ;                    ;
;              ;           ;      ;                           ;                    ;
;           ;;;;   ;;;     ;    ;;;;;  ;;;;                 ;;;;;   ;;;    ;;;   ;;;;;   ;;;
;          ;; ;;  ;;  ;    ;      ;        ;                  ;    ;;  ;  ;   ;    ;    ;   ;
;          ;   ;  ;   ;;   ;      ;        ;                  ;    ;   ;; ;        ;    ;
;          ;   ;  ;;;;;;   ;      ;     ;;;;                  ;    ;;;;;;  ;;;     ;     ;;;
;          ;   ;  ;        ;      ;    ;   ;                  ;    ;          ;    ;        ;
;          ;; ;;  ;        ;      ;    ;   ;                  ;    ;      ;   ;    ;    ;   ;
;           ;;;;   ;;;;     ;;    ;;;   ;;;;                  ;;;   ;;;;   ;;;     ;;;   ;;;
;
;
;

;; primitive operation's input is an address ===================================

;; =============
;; |  `null?`  |
;; =============

(test-match Λ-eval
            true
            (term (delta null? 0 ((0 null)))))
(test-match Λ-eval
            false
            (term (delta null? 0 ((0 (cons false 1)) (1 null)))))
(test-match Λ-eval
            true
            (term (delta null? 1 ((0 (cons false 1)) (1 null)))))

;; 3 elements in store, all possible locations
(test-match Λ-eval
            false
            (term (delta null? 0 ((0 (cons false 1)) (1 null) (2 null)))))
(test-match Λ-eval
            true
            (term (delta null? 1 ((0 (cons false 1)) (1 null) (2 null)))))
(test-match Λ-eval
            true
            (term (delta null? 2 ((0 (cons false 1)) (1 null) (2 null)))))

(test-match Λ-eval
            false
            (term (delta null? 0 ((0 (cons (λ (x) x) 2)) (1 (cons true 3)) (2 null) (3 (cons 0 4)) (4 null)))))
(test-match Λ-eval
            false
            (term (delta null? 1 ((0 (cons (λ (x) x) 2)) (1 (cons true 3)) (2 null) (3 (cons 0 4)) (4 null)))))
(test-match Λ-eval
            true
            (term (delta null? 2 ((0 (cons (λ (x) x) 2)) (1 (cons true 3)) (2 null) (3 (cons 0 4)) (4 null)))))
(test-match Λ-eval
            false
            (term (delta null? 3 ((0 (cons (λ (x) x) 2)) (1 (cons true 3)) (2 null) (3 (cons 0 4)) (4 null)))))
(test-match Λ-eval
            true
            (term (delta null? 4 ((0 (cons (λ (x) x) 2)) (1 (cons true 3)) (2 null) (3 (cons 0 4)) (4 null)))))

;; ============
;; |  `head`  |
;; ============

(test-match Λ-eval
            (err runtime REPL)
            (term (delta head 0 ((0 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta head 0 ((0 null) (1 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta head 1 ((0 null) (1 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta head 1 ((0 (cons true 1)) (1 null)))))
(test-match Λ-eval
            true
            (term (delta head 0 ((0 (cons true 1)) (1 null)))))
(test-match Λ-eval
            true
            (term (delta head
                         0
                         ((0 (cons true 1))
                          (1 null)
                          (2 (cons (λ (x) y) 4))
                          (3 (cons 2 5))
                          (4 (cons false 6))
                          (5 null)
                          (6 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta head
                         1
                         ((0 (cons true 1))
                          (1 null)
                          (2 (cons (λ (x) y) 4))
                          (3 (cons 2 5))
                          (4 (cons false 6))
                          (5 null)
                          (6 null)))))
(test-match Λ-eval
            (λ (x) y)
            (term (delta head
                         2
                         ((0 (cons true 1))
                          (1 null)
                          (2 (cons (λ (x) y) 4))
                          (3 (cons 2 5))
                          (4 (cons false 6))
                          (5 null)
                          (6 null)))))
(test-match Λ-eval
            2
            (term (delta head
                         3
                         ((0 (cons true 1))
                          (1 null)
                          (2 (cons (λ (x) y) 4))
                          (3 (cons 2 5))
                          (4 (cons false 6))
                          (5 null)
                          (6 null)))))
(test-match Λ-eval
            false
            (term (delta head
                         4
                         ((0 (cons true 1))
                          (1 null)
                          (2 (cons (λ (x) y) 4))
                          (3 (cons 2 5))
                          (4 (cons false 6))
                          (5 null)
                          (6 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta head
                         5
                         ((0 (cons true 1))
                          (1 null)
                          (2 (cons (λ (x) y) 4))
                          (3 (cons 2 5))
                          (4 (cons false 6))
                          (5 null)
                          (6 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta head
                         6
                         ((0 (cons true 1))
                          (1 null)
                          (2 (cons (λ (x) y) 4))
                          (3 (cons 2 5))
                          (4 (cons false 6))
                          (5 null)
                          (6 null)))))

;; ============
;; |  `tail`  |
;; ============

(test-match Λ-eval
            (err runtime REPL)
            (term (delta tail 0 ((0 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta tail 0 ((0 null) (1 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta tail 1 ((0 null) (1 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta tail 1 ((0 (cons true 1)) (1 null)))))
(test-match Λ-eval
            1
            (term (delta tail 0 ((0 (cons true 1)) (1 null)))))
(test-match Λ-eval
            1
            (term (delta tail
                         0
                         ((0 (cons true 1))
                          (1 null)
                          (2 (cons (λ (x) y) 4))
                          (3 (cons 2 5))
                          (4 (cons false 6))
                          (5 null)
                          (6 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta tail
                         1
                         ((0 (cons true 1))
                          (1 null)
                          (2 (cons (λ (x) y) 4))
                          (3 (cons 2 5))
                          (4 (cons false 6))
                          (5 null)
                          (6 null)))))
(test-match Λ-eval
            4
            (term (delta tail
                         2
                         ((0 (cons true 1))
                          (1 null)
                          (2 (cons (λ (x) y) 4))
                          (3 (cons 2 5))
                          (4 (cons false 6))
                          (5 null)
                          (6 null)))))
(test-match Λ-eval
            5
            (term (delta tail
                         3
                         ((0 (cons true 1))
                          (1 null)
                          (2 (cons (λ (x) y) 4))
                          (3 (cons 2 5))
                          (4 (cons false 6))
                          (5 null)
                          (6 null)))))
(test-match Λ-eval
            6
            (term (delta tail
                         4
                         ((0 (cons true 1))
                          (1 null)
                          (2 (cons (λ (x) y) 4))
                          (3 (cons 2 5))
                          (4 (cons false 6))
                          (5 null)
                          (6 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta tail
                         5
                         ((0 (cons true 1))
                          (1 null)
                          (2 (cons (λ (x) y) 4))
                          (3 (cons 2 5))
                          (4 (cons false 6))
                          (5 null)
                          (6 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta tail
                         6
                         ((0 (cons true 1))
                          (1 null)
                          (2 (cons (λ (x) y) 4))
                          (3 (cons 2 5))
                          (4 (cons false 6))
                          (5 null)
                          (6 null)))))


;; primitive operation's input is not an address ===============================

;; =============
;; |  `null?`  |
;; =============

(test-match Λ-eval
            (err runtime REPL)
            (term (delta null? true ())))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta null? true ((0 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta null? 1 ((0 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta null? 0 ())))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta null? 3 ((0 null) (1 (cons (λ (x) true) 2)) (2 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta null? true ((0 null) (1 (cons (λ (x) true) 2)) (2 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta null? false ((0 null) (1 (cons (λ (x) true) 2)) (2 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta null? (λ (x) x) ((0 null) (1 (cons (λ (x) true) 2)) (2 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta null? (λ (x) 0) ((0 null) (1 (cons (λ (x) true) 2)) (2 null)))))

;; ============
;; |  `head`  |
;; ============

(test-match Λ-eval
            (err runtime REPL)
            (term (delta head true ())))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta head true ((0 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta head 1 ((0 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta head 0 ())))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta head 3 ((0 null) (1 (cons (λ (x) true) 2)) (2 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta head true ((0 null) (1 (cons (λ (x) true) 2)) (2 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta head false ((0 null) (1 (cons (λ (x) true) 2)) (2 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta head (λ (x) x) ((0 null) (1 (cons (λ (x) true) 2)) (2 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta head (λ (x) 0) ((0 null) (1 (cons (λ (x) true) 2)) (2 null)))))

;; ============
;; |  `tail`  |
;; ============

(test-match Λ-eval
            (err runtime REPL)
            (term (delta tail true ())))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta tail true ((0 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta tail 1 ((0 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta tail 0 ())))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta tail 3 ((0 null) (1 (cons (λ (x) true) 2)) (2 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta tail true ((0 null) (1 (cons (λ (x) true) 2)) (2 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta tail false ((0 null) (1 (cons (λ (x) true) 2)) (2 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta tail (λ (x) x) ((0 null) (1 (cons (λ (x) true) 2)) (2 null)))))
(test-match Λ-eval
            (err runtime REPL)
            (term (delta tail (λ (x) 0) ((0 null) (1 (cons (λ (x) true) 2)) (2 null)))))

