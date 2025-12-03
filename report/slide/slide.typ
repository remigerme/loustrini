#import "@preview/touying:0.6.1": *
#import themes.metropolis: *

#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.10": *
#show: codly-init.with()

#let oran = rgb("#eb811b")
#let sepa = align(center, line(length: 80%, stroke: oran))

#show: metropolis-theme.with(aspect-ratio: "16-9", config-info(
  title: [#smallcaps(text(weight: "bold", size: 0.8em, "Loustrini"))#text(size: 0.8em, ":") #text(
      size: 0.7em,
    )[A Lustre Model Checker using the H-Houdini Invariant Learning Algorithm]],
  subtitle: "A very early presentation",
  author: "Rémi Germe",
  date: datetime.today(),
))

#title-slide()

#outline(depth: 1)

= First experiments

== Initial fiddling with SMT solvers: finding bugs

*Goal:* SMT-solver-agnostic model checker $=>$ use of a frontend library $=>$ in OCaml: `Smt.ml`

- Surprising behavior from `Smt.ml`, played with different solvers as well as the SMTLIB2 format directly #text(size: 0.55em, [(and was stuck in a dependency hell regarding `opam`, `z3`, `llvm`, `ld`, ...)])

#sepa
Aftermath of these initial experiments:

- discovered unsound behavior in Bitwuzla mappings of `Smt.ml` (see #link("https://github.com/formalsec/smtml/issues/465", text(fill: oran, "issue #465")))

- discovered bug in AltErgo support of `Smt.ml` (see #link("https://github.com/formalsec/smtml/discussions/450", text(fill: oran, "discussion #450")))

- more generally, clarification of the current limitations of `Smt.ml` (also #link("https://github.com/formalsec/smtml/discussions/450", text(fill: oran, "discussion #450")))

- re-discovered a known issue in AltErgo failing to conclude `SAT` (see #link("https://github.com/OCamlPro/alt-ergo/issues/1323", text(fill: oran, "issue #1323")))

#sepa

$=>$ Loustrini is _not_ solver-agnostic (based on `Z3`).

== Initial fiddling with SMT solvers: encoding programs

Two encodings of the same Lustre program (`x = 1 -> pre x + 1; y = 1 -> pre (x + y); ok = y >= 0;`):

#{
  set text(size: 0.55em)
  grid(
    columns: (1fr, 1fr),
    column-gutter: 10pt,
    row-gutter: 1.5em,
    align: center,
    ```smt2
    (define-fun-rec x_naive ((n Int)) Int
        (ite (= n 0) 1 (+ (x_naive (- n 1)) 1)))
    (define-fun-rec y_naive ((n Int)) Int
        (ite (= n 0) 1 (+ (y_naive (- n 1)) (x_naive (- n 1)))))
    (define-fun ok_naive ((n Int)) Bool
        (>= (y_naive n) 0))

    (declare-const n Int)

    (echo "consecution: unsat iff ok(n) => ok(n+1) is true:")
    (assert (and (>= n 0) (ok n) (not (ok (+ n 1)))))
    (check-sat)
    ```,
    ```smt2
    (define-fun init ((x Int) (y Int)) Bool (and (= x 1) (= y 1)))

    (define-fun trans ((x Int) (y Int) (nx Int) (ny Int)) Bool
        (and (= nx (+ x 1))
             (= ny (+ y x))))

    (define-fun ok ((y Int)) Bool (>= y 0))

    (declare-const x Int)
    (declare-const y Int)
    (declare-const nx Int)
    (declare-const ny Int)

    (echo "consecution: unsat iff ok is inductive:")
    (assert (and (ok y)
                 (trans x y nx ny)
                 (not (ok ny))))
    (check-sat)
    ```,

    [Z3 *timeouts* without providing a counterexample.],

    [Z3 *immediately answers* `SAT`, providing a counterexample.],
  )
}

= H-Houdini and Invariant Learning Algorithms

== Overview of invariant learning algorithms

*Goal:* prove a safety property $P$.

Let's not use _$k$-induction_ but _invariant learning_ instead.

*Challenge:* find a property $F$ such that:
$
  & "(initialization)"           &              I & => F \
  & "(consecution)"              & F and T(F, F') & => F' \
  & "(implies desired property)" &              F & => P \
$

How to find such an $F$?

$
  & "start from" F_0 := P \
  & "while" F_0 and ... and F_i "is not inductive" \
  & space.quad space.quad "learn" F_(i+1) "from a counterexample (strengthening)" \
  & F := F_0 and ... and F_i
$

== Learning invariants with H-Houdini

TODO

= Current Status & Future Work

== Current status & future work

TODO
