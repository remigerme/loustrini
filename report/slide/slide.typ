#import "@preview/touying:0.6.1": *
#import themes.metropolis: *

#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.10": *
#show: codly-init.with()

#let oran = rgb("#eb811b")
#let sepa = align(center, line(length: 80%, stroke: oran))

#let st(content) = context {
  let width = measure(content).width
  box[
    #content
    #place(
      dy: -0.25em,
      line(stroke: 2pt + oran, length: width),
    )
  ]
}

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

== Learning invariants

IC3 PDR vs Houdini / instantiation based -> Sorcar (pdr)

== Learning invariants with H-Houdini @h-houdini

TODO

= Current Status & Future Work

== Lustre $=>$ SMT

TODO encoding with `n`

Straightforward except two constructs:
- handling tuples
- handling function calls

== Lustre $=>$ SMT: tuples

Two possible solutions:
- define tuple sorts directly in `Z3`'s logic
- *treat a $n$-tuple as $n$ expressions*: return a list of expr defining each member of the tuple.

#sepa

#text(size: 0.7em, {
  codly(highlights: ((line: 6, start: 25, end: 38, fill: red),))
  ```OCaml
  let rec compile_expr
    (ctx   : context  )
    (env   : z3_env_t )
    (n     : Expr.expr)
    (n_pre : int      )
    (n_arr : int      ) : Expr.expr list = ...
  ```
})

Remarks:
- nested tuples are flattened
- we considered *`if`* to be the only polymorphic operator @lustre-tutorial \ (other operators such as `=`, `+`, ... do not support tuples)

== Lustre $=>$ SMT: function calls

Problem:

#grid(
  columns: (1fr, 1fr),
  column-gutter: 20pt,
  text(size: 0.6em, ```lustre
  node incr(x: int) returns (y: int);
  var l: int;
  let
      l = x + 1;
      y = x + l;
  tel

  node compute(a, b: int) returns (c: int);
  var z, t: int;
  let
      z = incr(a);
      t = incr(b);
      b = z + t;
  tel
  ```),
  [We can't just have $ &"(incr def)" &&cases(l(n) = x(n) + 1, y(n) = x(n) + l(n)) \ &"(incr calls)" &&cases(x(n) = a(n), z(n) = y(n), text(fill: #red, x(n) = b(n)), text(fill: #red, t(n) = y(n))) $],
)

#v(1em)
#align(
  center,
  [We need to resort to *instantiating* the node at each call site (_i.e._ perform inlining). \ #text(size: 0.6em)[(And that was a very painful rabbit hole, because I wanted definitions to be functions of `n`: `expr -> expr`, instead: use substitutions.)]],
)

#pagebreak()

#grid(
  columns: (1fr, 1fr),
  $
    "(incr call 1)" cases(&x_a (n) &= a(n), &l_a (n) &= x_a (n), &y_a (n) &= x_a (n) + l_a (n), &z(n) &= y_a (n))
  $,

  $
    "(incr call 2)" cases(&x_b (n) &= b(n), &l_b (n) &= x_b (n), &y_b (n) &= x_b (n) + l_b (n), &t(n) &= y_b (n))
  $,
)

Problem: we now have to learn invariant for *each instance* (separately in the worst case).

How to learn efficiently invariants for a node (and not just for its instances)?

In real-world projects (see #link("https://github.com/kind2-mc/kind2/discussions/1256", text(fill: oran, "discussion #1256")) and @kind2 @instantiation-based-invariant-discovery):
- compositional reasoning
- modular reasoning
- progressive refinements
- ...

== Lustre $=>$ SMT: another encoding: transition system

Transition system $(I, T)$ using primed variables, verifying a property P:
$ I => P "and" P and T => P' $

#let sem(x) = $bracket.l.stroked #x bracket.r.stroked$

*Handling $mono("pre") e$:* introduce a new state variable $S_"id"^mono("pre") = {mono("init") =$ #sym.emptyset$; space mono("next") = sem(e)}$

*Handling of $e -> e'$:* use $"ite"(S_i^(->), sem(e), sem(e'))$ with:
- $S_0^(->) = {mono("init") = "true"; space mono("next") = "false"}$
- $S_1^(->) = {mono("init") = "false"; space mono("next") = S_0^(->)}$
- $S_2^(->) = {mono("init") = "false"; space mono("next") = S_1^(->)}$
- ...

We also need to make sure we have *at most one* of the $S_i^(->)$ to be true.

#sepa

$ #emoji.warning space.quad #st($Delta(n) and$) Delta(n+1) and P(n) => P(n+1) $

#align(center, text(
  size: 0.8em,
)[Even less precise, the consecution might fail because of *spurious counterexamples* (unreachable situations).])

#pagebreak()

#set align(top)
#bibliography("bibliography.bib", title: "References")
