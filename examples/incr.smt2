(set-logic ALL)

(declare-fun tic (Int) Bool)
(define-fun-rec cpt ((n Int)) Int
    (ite (= n 0) 0 (+ (cpt (- n 1)) (ite (tic n) 1 0))))
(declare-fun aux (Int) Bool)
(define-fun ok ((n Int)) Bool
    (ite (= n 0) true (aux n)))

(assert (forall ((n Int))
    (and
        (=> (aux n) (<= (cpt (- n 1)) (cpt n)))
        (=> (<= (cpt (- n 1)) (cpt n)) (aux n)))))

(declare-const n Int)

(push)
(echo "initialization: unsat iff ok(0) is true:")
(assert (not (ok 0)))
(check-sat)
(pop)

(push)
(echo "consecution: unsat iff ok(n) => ok(n+1) is true:")
(assert (>= n 0))
(assert (ok n))
(assert (not (ok (+ n 1))))
(check-sat)
(pop)
