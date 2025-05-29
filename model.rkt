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
  (v ::= b f α)
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


(define-metafunction Λ-eval
  next : σ -> α
  [(next ()) ,0]
  [(next ((α_1 u_1) (α_2 u_2) ...))
   ,(+ 1 (term α_1))])


;; TODO: write unit tests for `next`

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

   ;; TODO: this should insert into the store
   [--> ((in-hole E (queue)) σ)
        ;((in-hole E (next σ)) σ)  ; old version
        ;; Potential solution below  - Nick DG
        ;((in-hole E (next σ)) (add σ (next σ) null))
        ((in-hole E (next σ)) (extend σ))
        queue]

   [--> ((in-hole E (add! α v)) σ)
        ((in-hole E α) (add σ α v))
        add!]

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


;; `null?` tests
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

;; `head` tests
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

;; `tail` tests
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

;;
;; primitive operation's input is not an address
;;

;; `null?`
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

;; `head`
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

;; `tail`
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

