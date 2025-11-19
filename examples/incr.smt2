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
(assert (not (ok n)))
(echo "unsat iff ok is always true:")
(check-sat)
