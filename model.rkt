#lang racket

(require redex)
(require rackunit)


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
  (ζ ::= (e σ))
  (e ::= .... α (err j k))
  (v ::= b f α)
  (E ::= hole (o E) (if E e e) (E e) (v E) (add! E e) (add! v E))
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


(define-metafunction Λ-eval
  delta : o v σ -> e
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

  ;; v ∉ Addr
  [(delta o v σ)
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
        ((in-hole E (next σ)) (extend σ))
        queue]

   [--> ((in-hole E (add! α v)) σ)
        ((in-hole E α) (add σ α v))
        add!]

   ;; TODO/question: will hardcoding `(err runtime REPL)` cause issues when we
   ;; get to a language that can have more nuanced errors?
   [--> ((in-hole E (v_f v)) σ)
        ((in-hole E (err runtime REPL)) σ)
        ;; rule only fires if `v_f` is not a function
        (side-condition (not (redex-match? Λ-eval f (term v_f))))
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


;; Load and unload

(define (load-Λ p)
  (cond
    [(redex-match? Λ e p) (term (,p ()))]
    [else (raise (string-append "load: expected a valid program, received: " (~a p)))]))

(define-metafunction Λ-eval
  unload-Λ : ζ -> e
  [(unload-Λ (v σ)) v]
  [(unload-Λ ((err j k) σ)) (err j k)])


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
 (term
  (unload-Λ
   ,(first
     (apply-reduction-relation*
      -->Λ
      (load-Λ (term ((λ (x) true) false)))))))
 (term true))

(test-equal
 (term
  (unload-Λ
   ,(first
     (apply-reduction-relation*
      -->Λ
      (load-Λ (term (queue)))))))
 (term 0))

(test-equal
 (term
  (unload-Λ
   ,(first
     (apply-reduction-relation*
      -->Λ
      (load-Λ (term (null? (queue))))))))
 (term true))

(test-equal
 (term
  (unload-Λ
   ,(first
     (apply-reduction-relation*
      -->Λ
      (load-Λ (term (head (add! (queue) false))))))))
 (term false))

(test-equal
 (term
  (unload-Λ
   ,(first
     (apply-reduction-relation*
      -->Λ
      (load-Λ (term (tail (add! (queue) false))))))))
 (term 1))

(test-equal
 (term
  (unload-Λ
   ,(first
     (apply-reduction-relation*
      -->Λ
      (load-Λ (term (head (add! (add! (queue) false) true))))))))
 (term false))

(test-equal
 (term
  (unload-Λ
   ,(first
     (apply-reduction-relation*
      -->Λ
      (load-Λ (term (if (head (add! (add! (queue) false) true))
                        true
                        (head (add! (add! (add! (queue) (λ (x) x)) (λ (x) false)) false)))))))))
 (term (λ (x) x)))

;; Errors

;; err-app case
;; function application with a non-function
(test-equal
 (term
  (unload-Λ
   ,(first
     (apply-reduction-relation*
      -->Λ
      (load-Λ (term (true false)))))))
 (term (err runtime REPL)))

;; err-add! case
;; attempting to add to a non-address
(test-equal
 (term
  (unload-Λ
   ,(first
     (apply-reduction-relation*
      -->Λ
      (load-Λ (term (add! true true)))))))
 (term (err runtime REPL)))

;; primitive operation errors
(test-equal
 (term
  (unload-Λ
   ,(first
     (apply-reduction-relation*
      -->Λ
      (load-Λ (term (null? true)))))))
 (term (err runtime REPL)))

(test-equal
 (term
  (unload-Λ
   ,(first
     (apply-reduction-relation*
      -->Λ
      (load-Λ (term (head false)))))))
 (term (err runtime REPL)))

(test-equal
 (term
  (unload-Λ
   ,(first
     (apply-reduction-relation*
      -->Λ
      (load-Λ (term (tail (λ (x) x))))))))
 (term (err runtime REPL)))



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


; `(e_d ->i e_c)` is a dependent function contract.
; The codomain contract, e_c, can depend on the argument to the protected function.

; `(mon j k l e_κ e_c)` is a monitor that attaches contract e_κ to e_c.
; The value of e_c is dubbed the "carrier" of the contract.
; j, k, and l are labels that name the parties that agreed to the contract:
; j is the contract-defining module,
; k is the server module, and
; l is the client module.

(define-extended-language ΛC
  Λ
  (e ::= ....
     (e ->i e)            ;; dependent function contract
     (mon j k l e_κ e_c)) ;; three-label monitor
  (j k l ::= x))          ;; label

;; monitor labels:
;; - j :: contract-defining module
;; - k :: server module
;; - l :: client module

(define-union-language ΛC∪Λ-eval ΛC Λ-eval)

(define-extended-language ΛC-eval
  ;; inherit surface syntax from ΛC and evaluation syntax from Λ-eval
  ΛC∪Λ-eval
  (e ::= ....
     (mon j k e e)        ;; two-label monitor
     (grd j k ω v)        ;; guard
     (e · l))             ;; label application

  (v ::= .... κ (grd j k ω v))
  (κ ::= b (λ (x) e) (v ->i v))
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
        ((in-hole E (λ (x) (mon j k l (v_c e_j) (v e_k)))) σ)
        (where e_g (mon j l v_d x))
        (where e_j (e_g · j))
        (where e_k (e_g · k))
        grd-fun]

   [--> ((in-hole E (mon j k v_κ v)) σ)
        ((in-hole E (err runtime REPL)) σ)
        (side-condition (not (redex-match? ΛC-eval κ (term v_κ))))
        err-mon]))

(define (load-ΛC p)
  (cond
    [(redex-match? ΛC e p) (term (,p ()))]
    [else (raise (string-append "load: expected a valid program, received: " (~a p)))]))

(define-metafunction ΛC-eval
  unload-ΛC : ζ -> e
  [(unload-ΛC (v σ)) v]
  [(unload-ΛC ((err j k) σ)) (err j k)])


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


;; Λ tests using -->ΛC to make sure that ΛC correctly *extends* Λ
(test-equal
 (term
  (unload-ΛC
   ,(first
     (apply-reduction-relation*
      -->ΛC
      (load-ΛC (term ((λ (x) true) false)))))))
 (term true))

(test-equal
 (term
  (unload-ΛC
   ,(first
     (apply-reduction-relation*
      -->ΛC
      (load-ΛC (term (queue)))))))
 (term 0))

(test-equal
 (term
  (unload-ΛC
   ,(first
     (apply-reduction-relation*
      -->ΛC
      (load-ΛC (term (null? (queue))))))))
 (term true))

(test-equal
 (term
  (unload-ΛC
   ,(first
     (apply-reduction-relation*
      -->ΛC
      (load-ΛC (term (head (add! (queue) false))))))))
 (term false))

(test-equal
 (term
  (unload-ΛC
   ,(first
     (apply-reduction-relation*
      -->ΛC
      (load-ΛC (term (tail (add! (queue) false))))))))
 (term 1))

(test-equal
 (term
  (unload-ΛC
   ,(first
     (apply-reduction-relation*
      -->ΛC
      (load-ΛC (term (head (add! (add! (queue) false) true))))))))
 (term false))

(test-equal
 (term
  (unload-ΛC
   ,(first
     (apply-reduction-relation*
      -->ΛC
      (load-ΛC (term (if (head (add! (add! (queue) false) true))
                        true
                        (head (add! (add! (add! (queue) (λ (x) x)) (λ (x) false)) false)))))))))
 (term (λ (x) x)))

;; example from paper, section 4.3
#;
(test-equal
 (term
  (unload-ΛC
   ,(first
     (apply-reduction-relation*
      -->ΛC
      (load-ΛC (term ?)))))))

;; TODO: write tests that actually use contracts

;; true and false as contracts (p. 15)
(test-equal
 (term
  (unload-ΛC
   ,(first
     (apply-reduction-relation*
      -->ΛC
      (load-ΛC (term (mon j k l true false)))))))
 (term false))

(test-equal
 (term
  (unload-ΛC
   ,(first
     (apply-reduction-relation*
      -->ΛC
      (load-ΛC (term (mon ctc lib main true false)))))))
 (term false))

(test-equal
 (term
  (unload-ΛC
   ,(first
     (apply-reduction-relation*
      -->ΛC
      (load-ΛC (term ((mon ctc lib main true (λ (x) x)) true)))))))
 (term true))

(test-equal
 (term
  (unload-ΛC
   ,(first
     (apply-reduction-relation*
      -->ΛC
      (load-ΛC (term (mon j k l false true)))))))
 (term (err j k)))

;; functions as contracts
;; predicate contracts (`mon j k (λ (x) e) v`)
;; arrow contracts
;; example that shows that effects aren't duplicated
;;   (maybe we just state that this is true; otherwise, we have to add effects to our language)
;; example where contract itself is inconsistent, e.g.
;;   `(bool? -> bool?) ->i (λ (f) (f 42))` from paper, p. 16
;; `(mon j k v_κ v)` where v_κ is not a contract (should error)

;; Program 4.1 from paper (p. 15)
;; TODO: need to add concept of equality to our language to make this work
;(mon ctc lib main (true ->i (λ (x) (λ (y) x == y))) (λ (z) z))


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
  Λ
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
  (κ ::= (tr v v) (co α v))
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
   ;; TODO
   ))

(define (load-ΛT p)
  (cond
    [(redex-match? ΛT e p) (term (,p ()))]
    [else (raise "load: expected a valid program")]))

(define-metafunction ΛT-eval
  unload-ΛT : ζ -> v
  [(unload-ΛT (v σ)) v])

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

(test-equal
 (term
  (unload-ΛT
   ,(first
     (apply-reduction-relation*
      -->ΛT
      (load-ΛT (term (tr true true)))))))
 (term (tr true true)))

;; Trace contract that accepts everything

;; Trace contract that rejects everything

;; Trace contract that only accepts one value
(test-equal
 (term
  (unload-ΛT
   ,(first
     (apply-reduction-relation*
      -->ΛT
      (load-ΛT (term (queue)))))))
 (term 0))


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


(define-extended-language ΛU
  Λ
  (e ::= .... (tr e e e)))

(define-union-language ΛU∪ΛC-eval ΛU ΛC-eval)

(define-extended-language ΛU-eval
  ΛU∪ΛC-eval
  (e ::= .... (co v α v))
  (κ ::= .... (tr v v v) (co v α v))
  (E ::= .... (tr E e e) (tr v E e) (tr v v E))

  )


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
   -->Λ
   ΛU-eval

   [-->((in-hole E (mon k j (tr v_κ v_b v_p))) σ)
       ((in-hole E (mon k j v_b (co v_κ α v_p) v)) in-hole σ (α -> null))
       mon-trace]
   [--> ((in-hole E (mon k j (co v_κ α v_p) v)) σ)
        ((in-hole E (add! α x_j (mon k j v_p α) v x_v)) σ)
        (where x_j (mon k j v_κ v))
        (where x_j (x_v · j))
        mon-col]


   )
  )

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



; TODO






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

#;
(test-equal (term (delta null? 0 ((0 null))))
            (term true))

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
