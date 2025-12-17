(set-logic ALL)

(define-fun-rec x_naive ((n Int)) Int
    (ite (= n 0) 1 (+ (x_naive (- n 1)) 1)))
(define-fun-rec y_naive ((n Int)) Int
    (ite (= n 0) 1 (+ (y_naive (- n 1)) (x_naive (- n 1)))))
(define-fun ok_naive ((n Int)) Bool
    (>= (y_naive n) 0))

(declare-const n Int)

(push)
(echo "initialization: unsat iff ok(0) is true:")
(assert (not (ok_naive 0)))
(check-sat)
(pop)

; The following will timeout because the property is not inductive.
; But we don't want it to timeout, else we cannot learn from a counterexample.
; (push)
; (echo "consecution: unsat iff ok(n) => ok(n+1) is true:")
; (assert (>= n 0))
; (assert (ok n))
; (assert (not (ok (+ n 1))))
; (check-sat)
; (pop)

; Strengthening our proof with a simple lemma.
(define-fun lemma_naive ((n Int)) Bool
    (>= (x_naive n) 0))

(push)
(echo "initialization (lemma): unsat iff lemma(0) is true:")
(assert (not (lemma_naive 0)))
(check-sat)
(pop)

(push)
(echo "consecution: unsat iff lemma(n) ^ ok(n) => lemma(n+1) ^ ok(n+1) is true:")
(assert (>= n 0))
(assert (ok_naive n))
(assert (lemma_naive n))
(assert (not (ok_naive (+ n 1))))
(assert (not (lemma_naive (+ n 1))))
(check-sat)
(pop)

(push)
(echo "implies desired property: trivial here")
(pop)

(echo "")

; Better version (nonrecursive)
(define-fun init ((x Int) (y Int)) Bool (and (= x 1) (= y 1)))

(define-fun trans ((x Int) (y Int) (nx Int) (ny Int)) Bool
    (and (= nx (+ x 1))
         (= ny (+ y x))))

(define-fun ok ((y Int)) Bool (>= y 0))

(declare-const x Int)
(declare-const y Int)
(declare-const nx Int)
(declare-const ny Int)

(push)
(echo "init: unsat iff ok is true:")
(assert (and (init x y) (not (ok y))))
(check-sat)
(pop)

(push)
(echo "consecution: unsat iff ok is inductive:")
(assert (and (ok y) 
             (trans x y nx ny)
             (not (ok ny))))
(check-sat)
(pop)

(define-fun lemma ((x Int)) Bool (>= x 0))

(push)
(echo "init: unsat iff lemma is true:")
(assert (and (init x y) (not (lemma x))))
(check-sat)
(pop)

(push)
(echo "consecution: unsat iff lemma ^ ok is inductive:")
(assert (and (ok y)
             (lemma x)
             (trans x y nx ny)
             (not (ok ny))))
(check-sat)
(pop)
