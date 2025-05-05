#lang racket

;; trace contracts are provided by the trace-contract library
(require trace-contract)

;; a simple function (thunk) whose outputs are strictly increasing
(define/contract (number-of-calls)
  ;; ([x natural?]) declares `x` as a trace variable with contract `natural?`
  ;; a trace variable can appear in the body contract of a function, and
  (trace/c ([num natural?])
    ;; (-> x natural?) is the body contract for f: it must accept
    (-> num)
    (accumulate
     0
     [(x) (λ (acc cur)
            (if (acc . < . cur) cur (fail)))]))
  ())

(f 1)

#|
a trace contract consists of three components:

- a sequence of declarations for trace variables declarations, including a
  behavioral contract for each
- a contract expression, dubbed the body contract
- a sequence of predicate clauses, which determine whether the trace is valid
  and accumulate values in the trace
|#
