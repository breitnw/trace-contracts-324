#lang racket

;; Trace contracts are provided by the trace-contract library
(require trace-contract)

(define calls-increasing/c
  (trace/c
   ;; ([x natural?]) declares `x` as a trace variable with contract `natural?`.
   ;; Trace variables represent values that we want to collect into the trace as
   ;; they flow through the function
   ([num natural?])
   ;; (-> num) uses `x` as a collector contract. Whenever a value matches `num`
   ;; during a contract check (i.e., when that value is returned from the
   ;; function), it is accumulated into the trace.
   (-> num)
   ;; (accumulate ...) defines what the trace should look like, and how values
   ;; should be accumulated as they are intercepted by collectors.
   (accumulate
    0
    [(num) (λ (acc cur)
           (if (acc . < . cur) cur (fail)))])))

;; A simple function (thunk) whose outputs are strictly increasing
(define/contract number-of-calls
  calls-increasing/c
  (let ([count 0])
    (λ ()
      (set! count (+ count 1))
      count)))

;; Oops! we broke it...
(define/contract number-of-calls-broken
  calls-increasing/c
  (λ ()
    (let ([count 0])
      (set! count (+ count 1))
      count)))

#|
a trace contract consists of three components:

- a sequence of declarations for trace variables declarations, including a
  behavioral contract for each
- a contract expression, dubbed the body contract
- a sequence of predicate clauses, which determine whether the trace is valid
  and accumulate values in the trace
|#

;; TODO multiple trace variables, one in client and one in server
;; TODO example where the client is blamed for not passing in a good value
;; TODO example where the trace contract is applied to a function passed into
;; the server, and the client is blamed
;; TODO make-immutable, mutate
