#import "@preview/touying:0.6.1": *
#import themes.metropolis: *

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

= TODO

== Initial fiddling with SMT solvers

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
