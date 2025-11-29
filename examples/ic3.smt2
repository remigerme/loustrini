(set-logic ALL)

(define-fun-rec x ((n Int)) Int
    (ite (= n 0) 1 (+ (x (- n 1)) 1)))
(define-fun-rec y ((n Int)) Int
    (ite (= n 0) 1 (+ (y (- n 1)) (x (- n 1)))))
(define-fun ok ((n Int)) Bool
    (>= (y n) 0))

(declare-const n Int)

(push)
(echo "initialization: unsat iff ok(0) is true:")
(assert (not (ok 0)))
(check-sat)
(pop)

; The following will timeout because the property is not inductive.
; (push)
; (echo "consecution: unsat iff ok(n) => ok(n+1) is true:")
; (assert (>= n 0))
; (assert (ok n))
; (assert (not (ok (+ n 1))))
; (check-sat)
; (pop)

; Strengthening our proof with a simple lemma.
(define-fun lemma ((n Int)) Bool
    (>= (x n) 0))

(push)
(echo "initialization (lemma): unsat iff lemma(0) is true:")
(assert (not (lemma 0)))
(check-sat)
(pop)

(push)
(echo "consecution: unsat iff lemma(n) ^ ok(n) => lemma(n+1) ^ ok(n+1) is true:")
(assert (>= n 0))
(assert (ok n))
(assert (lemma n))
(assert (not (ok (+ n 1))))
(assert (not (lemma (+ n 1))))
(check-sat)
(pop)

(push)
(echo "implies desired property: trivial here")
(pop)
