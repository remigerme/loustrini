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

#show: metropolis-theme.with(
  aspect-ratio: "16-9",
  config-info(
    title: [#smallcaps(text(weight: "bold", size: 0.8em, "Loustrini"))#text(size: 0.8em, ":") #text(
        size: 0.7em,
      )[A Lustre Model Checker using (H-)Houdini Invariant Learning Algorithm]],
    subtitle: "Or me learning about invariant learning algorithms",
    author: "Rémi Germe",
    date: "09.01.2026",
  ),
)

#title-slide()

#outline(depth: 1)

= First experiments with SMT solvers

== First experiments with SMT solvers

*Goal:* SMT-solver-agnostic model checker $=>$ use a frontend library $=>$ in OCaml: `Smt.ml` @smtml

- Surprising behavior from `Smt.ml`, played with different solvers as well as the SMTLIB2 format directly #text(size: 0.55em, [(and was stuck in a dependency hell regarding `opam`, `z3`, `llvm`, `ld`, ...)])

#sepa
Aftermath of these initial experiments:

- discovered unsound behavior in Bitwuzla mappings of `Smt.ml` (see #link("https://github.com/formalsec/smtml/issues/465", text(fill: oran, "issue #465")))

- discovered bug in AltErgo @ae support of `Smt.ml` (see #link("https://github.com/formalsec/smtml/discussions/450", text(fill: oran, "discussion #450")))

- more generally, clarification of the current limitations of `Smt.ml` (also #link("https://github.com/formalsec/smtml/discussions/450", text(fill: oran, "discussion #450")))

- re-discovered a known issue in AltErgo failing to conclude `SAT` (see #link("https://github.com/OCamlPro/alt-ergo/issues/1323", text(fill: oran, "issue #1323")))

#sepa

$=>$ Loustrini is _not_ solver-agnostic (using `Z3` @z3 - best would have been `cvc5` @cvc5 for _abducts_).

= Translating Lustre to SMT expressions

== Encoding _à la_ k-induction

Encoding presented in the handout.

*$Delta(n)$* encodes the system equations at time $n$.

Checking a property $P$ is inductive on system $Delta$:

$
  & ("initiation")             && Delta(0) => P(0) \
  & ("consecution") space.quad && Delta(n) and Delta(n+1) and P(n) => P(n+1)
$

#sepa

Remark: I implemented a wrong semantics for $e -> e'$:

$1 -> 2 -> 3$ generates $cases(1 "if" n = 0, 2 "if" n = 1, 3 "if" n >= 2)$ instead of $cases(1 "if" n = 0, 3 "if" n >= 1)$.

== Encoding as a transition system
#text(size: 0.9em)[
  Transition system $(I, T)$ using state variables and primed variables, verifying a property P:
  $ I => P "and" P and T => P' $

  #let sem(x) = $bracket.l.stroked #x bracket.r.stroked$

  *Handling $mono("pre") e$:* introduce a new state variable $S_"id"^mono("pre") = {mono("init") =$ #sym.emptyset$; space mono("next") = sem(e)}$

  *Handling of $e -> e'$:* use $"ite"(S_i^(->), sem(e), sem(e'))$ with:
  - $S_0^(->) = {mono("init") = "true"; space mono("next") = "false"}$
  - $S_1^(->) = {mono("init") = "false"; space mono("next") = S_0^(->)}$
  - $S_2^(->) = {mono("init") = "false"; space mono("next") = S_1^(->)}$
  - ...

  We also need to make sure we have *at most one* of the $S_i^(->)$ to be true #text(size: 0.8em)[(+ harder to obtain positive examples)].

  #sepa

  $ #emoji.warning space.quad #st($Delta(n) and$) Delta(n+1) and P(n) => P(n+1) $

  #align(
    center,
    [Even less precise, the consecution might fail because of *spurious counterexamples* (unreachable situations), already the case before but less likely.],
  )
]

== Encoding non trivial constructs

=== Tuples.

Treat a n-tuple as n-expressions and translate each member separately.

#sepa

=== Node calls.

Instantiation (inlining) of nodes at call site.

How to learn efficiently invariants for a node (and not just for its instances)?

In real-world projects (see #link("https://github.com/kind2-mc/kind2/discussions/1256", text(fill: oran, "discussion #1256")) and @kind2 @instantiation-based-invariant-discovery):
- compositional reasoning
- modular reasoning
- progressive refinements
- ...

This issue will *not* be addressed in the project.

= Invariants learning algorithms, Houdini, H-Houdini

== Overview of invariant learning algorithms

TODO

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

== Houdini: overview @houdini @instantiation-based-invariant-discovery

#grid(
  columns: 2,
  column-gutter: 20pt,
  image("assets/houdini-pipeline.svg"),
  align(top, [
    #v(1.2em)
    - Generating a lot of candidates using templates (see next slide)

    #v(2.8em)
    - Initial sift: removing all candidates that do no satisfy a trace of execution (see next next slide)

    #v(2em)
    - Inductivity sift: removing all candidates that break inductivity, and iterate until reaching an inductive set (see next next slide)

    #v(3em)
    - Final learned inductive invariants
  ]),
)

== Houdini: generating invariants <invgen>

#let rel(x) = text(fill: rgb("e41deb"), $#x$)

Variables below are all evaluated at $n$. #link(<nnpone>)[(details)]

#grid(
  columns: 2,
  column-gutter: 10pt,
  row-gutter: 1em,
  [*Booleans.*], $cal(I)_b ::= b = "true" | b = "false" | rel(b_1 = b_2) | rel(b_1 = not b_2)$,
  [*Integers.*], $cal(I)_i ::= i diamond.small "cst" | rel(i_1 diamond.small i_2)$,

  [*Reals.*], [Same as for integers.],
)

Where:
- $"cst" in {0, 1, -1} union {"constants of interest (hardcoded in the program)"}$
- $diamond.small ::= space.thin >= | > | <= | < | = | !=$

We obtain a set of candidates $H = and.big_(i=1)^d h_i$.

#v(1em)
#align(center, [*SOUND* but absolutely not *COMPLETE*

  but Houdini is complete _relative_ to the templates])

== Houdini: sifting candidates

=== Inductivity check.

$ Delta(n) and Delta(n+1) and H(n) and not H(n+1) space ? $

$
  & mono("UNSAT"): H "is inductive OR" H(n) "contradicts" Delta(n) and Delta(n+1) \
  & mono("SAT"): exists "cex"\, cases("cex" tack.r.double H(n), "cex" tack.r.double not H(n+1)) space i.e. space exists i in {1, ..., d}, underbrace(#[*$"cex" tack.r.double not h_i (n+1)$*], "remove all these candidates")
$

#place(dy: -1.5em, text(size: 0.7em)[Better than checking each $h_i$ separately.])

=== Initial sift.

+ Prune the search space by removing many candidates that do not hold.
+ Ensure $H$ is non-contradictory (vacuously false).

$ Delta(0) and ... and Delta(k) and not H(k) $

$
  & mono("UNSAT"): H "is consistent with step" k \
  & mono("SAT"): exists "cex", ... "(similar as above, and we keep iterating for this" k")"
$

== Houdini: demo

Extra-prunning of "obvious" invariants.

=== `ic3.lus`

#codly(number-format: none)
```
x = 1 -> pre x + 1;
y = 1 -> pre (x + y);
ok = y >= 0;
```

Not k-inductive!

#v(1em)

=== `fib.lus`

With/without explicit state variables.

== H-Houdini: overview @h-houdini

TODO

== Conclusion

TODO

#pagebreak()

#show: appendix

#{
  set align(top)
  set text(size: 0.7em)
  bibliography("bibliography.bib", title: "References")
}

== Initial fiddling with SMT solvers: encoding programs

#grid(
  columns: (1fr, 1fr),
  column-gutter: 10pt,
  row-gutter: 1em,
  align: center,
  [Two encodings of the same Lustre program:],
  text(size: 0.6em, ```
  x = 1 -> pre x + 1;
  y = 1 -> pre (x + y);
  ok = y >= 0;
  ```),

  text(size: 0.5em, ```smt2
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
  ```),
  text(size: 0.5em, ```smt2
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
  ```),

  [Z3 *timeouts* without providing a counterexample.],

  [Z3 *immediately answers* `SAT`, providing a counterexample.],
)

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

This issue will *not* be addressed in the project.

== Properties refering to $n$ and $n+1$ <nnpone>

They require careful thinking:

$
  underbrace(Delta(n) and Delta(n+1), "do not constrain" x(n+2)) and P(n) => underbrace(P(n+1), "refers to" x(n+2)) ? " will fail, so still sound"
$

$=>$ strenghten our lhs with $Delta(n+2)$

#link(<invgen>)[Go back.]

== Positive examples for transition system

Strategy: $(C and T => C') <==> C and T and not C'$ to see if $C$ is inductive (iff query $mono("UNSAT")$).

Problem: *if $C$ is $mono("UNSAT")$* alone #text(size: 0.8em, [(e.g. $C = x >= 0 and x < 0$)]), we *cannot refine* $C$ any further.

$=>$ @instantiation-based-invariant-discovery @h-houdini: use *positive examples* (concretely: some traces of the program) to first sift $C$

Problem: initial state alone is not sufficient: $mono("pre")$ variables are not initialized

#{
  set text(size: 0.8em)
  grid(
    columns: (1fr, 2fr),
    $x = 0 -> 1 -> "pre" "pre" x$,
    [
      - $x = "ite"(S_0^->, 0, "ite"(S_1^->, 1, S_1^"pre"))$
      - $S_1^"pre" ' = S_0^"pre"$
      - $S_0^"pre" ' = x$
    ],
  )
}

#{
  set text(size: 0.8em)
  table(
    columns: (1fr,) * 6,
    align: center,
    $t$, $x$, $S_0^->$, $S_1^->$, $S_1^"pre"$, $S_0^"pre"$,
    $0$, $0$, [true], [false], $diameter$, $diameter$,
    $1$, $1$, [false], [true], $diameter$, $0$,
    $2$, $0$, [false], [false], $0$, $1$,
  )
}

$=>$ simulate the program for $k$ steps (where $k$ denotes the max depth of $mono("pre")$ statements): _difficult_ with this encoding
