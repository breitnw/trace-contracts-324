#lang racket

(module basic-trace racket
  ;; Trace contracts are provided by the trace-contract library
  (require trace-contract)

  (define calls-increasing/c
    (trace/c
     ;; ([num natural?]) declares `num` as a trace variable with contract
     ;; `natural?`. Trace variables represent values that we want to collect
     ;; into the trace as they flow through the function.
     ([num natural?])
     ;; (-> num) uses `num` as a collector contract. Whenever a value matches
     ;; `num` during a contract check (i.e., when that value is returned from
     ;; the function), it is accumulated into the trace.
     (-> num)
     ;; (accumulate ...) defines what the trace should look like, and how values
     ;; should be accumulated as they are intercepted by collectors.
     (accumulate
      0
      [(num) (λ (acc cur)
               (if (acc . < . cur) cur (fail)))])))

  (provide
   (contract-out
    [number-of-calls calls-increasing/c]
    [number-of-calls-broken calls-increasing/c]))

  ;; A simple function (thunk) whose outputs are strictly increasing
  (define number-of-calls
    (let ([count 0])
      (λ ()
        (set! count (+ count 1))
        count)))

  ;; Oops! we broke it...
  (define number-of-calls-broken
    (λ ()
      (let ([count 0])
        (set! count (+ count 1))
        count))))


#| ;; ==========================================================================

a trace contract consists of three components:

- a sequence of declarations for trace variables declarations, including a
  behavioral contract for each
- a contract expression, dubbed the body contract
- a sequence of predicate clauses, which determine whether the trace is valid
  and accumulate values in the trace

|# ;; ==========================================================================

(module client-blame-trace racket
  (require stream-etc)
  (require trace-contract)

  (define/match (no-duplicates? _)
    [((stream))
     true]
    [((stream* val xt))
     (and (not (stream-member? xt val))
          (no-duplicates? xt))])

  (define produces-unique-ids/c
    (trace/c ([id string?])
             (-> id)
             (full (id) no-duplicates?)))

  (provide
   (contract-out
    [register (trace/c ([id string?])
                       (-> id void)
                       (full (id) no-duplicates?))]
    [register-auto (-> produces-unique-ids/c (-> void))]))

  ;; register users, given their id
  (define (register user-id)
    (displayln (format "hi, ~a! you've successfully registered" user-id)))

  ;; register users, given a function that generates a unique id
  (define (register-auto generate-id)
    (λ ()
      (define user-id (generate-id))
      (displayln (format "hi, friend! you've successfully registered as ~a"
                         user-id)))))



;; TRACING FUNCTION INTERACTIONS ===============================================

(module multi-func-trace racket
  (require stream-etc)
  (require trace-contract)

  ;; Sometimes, we want multiple functions to depend on the same trace. This is
  ;; particularly useful when utilizing trace contracts as an analog for
  ;; integration testing, which aim to ensure our functions "play nicely together"

  (provide
   (contract-out
    [hash-set! hash-set/c]
    [string-set! (-> mutable/c natural? char? void?)]))

  (define/match (not-interfere? _)
    [((stream))
     true]
    ;; if we mutate `x`, it's ok to add it to a hash set later
    [((stream* `(mut ,_) xt))
     (not-interfere? xt)]
    ;; if `x` is in a hash set, we can't mutate it later
    [((stream* `(set ,x) xt))
     (and (not (stream-member? xt `(mut ,x)))
          (not-interfere? xt))])

  (define-values (hash-set/c mutable/c)
    (trace/c
     ;; We want to intercept the hash keys, which can have any type
     ([t any/c])
     ;; #:global states that we want to initialize the traces at definition time
     ;; rather than attachment time
     #:global
     (values
      ;; When a hash set has the hash-set/c contract, intercept the keys with the
      ;; collector, and use list/t to tag them with 'set in the trace.
      (-> hash? (list/t 'set t) any/c void?)
      ;; When any value has the mutable/c contract, immediately intercept the
      ;; value and tag it with 'mut in the trace.
      (list/t 'mut t))
     ;; whenever a value is collected in the trace, check that the mutable
     (full (t) not-interfere?))))


;; Requires for REPL ===========================================================

(require (submod "." basic-trace))
(require (submod "." client-blame-trace))
(require (submod "." multi-func-trace))


;; DEMO ========================================================================

;; client-blame-trace (define rauto (register-auto (lambda () (number->string (random)))))

;; multi-func-trace
;; (define key (string #\H #\e #\l #\l #\o))
;; (define my-hash (make-hash))
;; (hash-set! my-hash key 'the-val)
;; (string-set! key 0 #\W)
