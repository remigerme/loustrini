#set text(font: "Libertinus Sans")
#set heading(numbering: "I.1 ")
#set par(justify: true)
#show link: set text(fill: red)
#show "TODO": set text(fill: red, weight: "bold", style: "italic")
#set page(numbering: "1 of 1")

#align(center)[
  #text(size: 1.4em)[Loustrini: a Lustre model checker using (H-)Houdini algorithm]

  Rémi Germe

  05.01.2026
]

_This short report was written as part of my project for the SYNC class at MPRI. Please refer to the #link("https://github.com/remigerme/loustrini", "repository")#footnote([#link("https://github.com/remigerme/loustrini")]) for the latest version of the project._

= Introduction

Real-world model checkers such as #link("https://kind2-mc.github.io/kind2/", "Kind2") @kind2 use several invariant learning algorithms @instantiation-based-invariant-discovery, and also pair them with other techniques such as k-induction @scalingup. On the other hand, Loustrini solely relies on invariant learning algorithms.

When trying to prove a property with Loustrini, it will attempt to learn invariants that imply the desired property. If such inductive invariants are discovered, the property holds. Else, Loustrini fails to prove that the property holds.

My work consisted in:
- reading about model checking of Lustre programs,
- reading about invariant learning algorithms such as Houdini @houdini @instantiation-based-invariant-discovery and H-Houdini @h-houdini,
- implementing a prototype model checker named Loustrini.

The rest of the report is structured as follows: I first present some initial experiments I made with SMT solvers, (re)discovering several bugs. Next, I detail the translation from a Lustre program to SMT expressions. I then describe the invariant learning algorithms powering Loustrini: Houdini and H-Houdini. Finally, I provide a very limited evaluation of Loustrini.

= Initial experiments with SMT solvers

The original skeleton of the project was using Alt-Ergo Zero @aez, a solver derived from an old version of Alt-Ergo @ae. I wanted Loustrini to be solver-agnostic and be able to use different SMT solvers interchangeably.

The only OCaml SMT frontend I was able to find is Smt.ml @smtml. I discovered some issues/limitations (unsound behavior in Bitwuzla mappings #footnote([See #link("https://github.com/formalsec/smtml/issues/465").]), bug in Alt-Ergo support, and limitations of uninterpreted functions #footnote([See #link("https://github.com/formalsec/smtml/discussions/450").])) which led me to believe the library was not mature enough yet.

Then, I considered several solvers individually:
- Alt-Ergo, which sometimes answers `UNKNOWN` when the expected answer clearly is `SAT` #footnote([See #link("https://github.com/OCamlPro/alt-ergo/issues/1323").]). This issue could be addressed, as models are still generated, but this discouraged me from using Alt-Ergo.
- cvc5 @cvc5, which whould have been ideal as it natively provides an abduct operation (see @abduct), but cvc5 unfortunately does not officialy provide OCaml bindings.
- Z3 @z3, which was eventually designated as the underlying solver for Loustrini.

= Translating Lustre to SMT expressions

There is two possible encodings for Lustre programs: _à la_ k-induction or as a transition system. Both were implemented, but the k-induction encoding was eventually kept for reasons detailed below.

*À la k-induction* @scalingup @instantiation-based-invariant-discovery. This is the encoding mentioned in the project description: our Lustre program is encoded by a function $Delta : NN -> mono("Expr")$. We can check that a property $P : NN -> mono("Expr")$ is inductive with the following queries:
$
  & ("initiation") && Delta(0) => P(0) \
  & ("consecution") space.quad && Delta(n) and Delta(n+1) and P(n) => P(n+1) #footnote(numbering: "1 ", [We could technically consider $Delta(n+1) and P(n) => P(n+1)$ but this would lead to more spurious counterexamples, _i.e._ states that contradict the inductivity check are in fact not reachable anyway.])
$

*As a transition system* @h-houdini. Our program is given by a pair $(I, T)$ where $I$ encodes the initial state of our program, and $T$ encodes the transition relation to go from one step to the next. We do not have an explicit $n$: $x(n)$ becomes $x$ and $x(n+1)$ becomes $x'$. Note that, for each delay $->$ and $mono("pre")$ operator, we introduce a state variable. With this encoding, the queries for checking inductivity are:
$
  & ("initiation")             && I => P \
  & ("consecution") space.quad && T and P => P'
$

Although the transition system encoding might seem conceptually simpler, I found it far less convenient to work with in practice when trying to compute positive examples, _i.e._ a trace of execution of the program (see @positive-examples).

*On properties refering to multiple steps.* Let's consider a property $P(n) = x(n+1) >= x(n)$. $P(n+1)$ depends on $x(n+2)$. Using our query presented above for checking inductivity, $x(n+2)$ does not appear in $Delta(n) and Delta(n+1)$, so the inductivity will fail. If we want such a property to have a chance to pass the test, we also need to consider $Delta(n+2)$. I chose not to consider such properties for the rest of the project, but this could be a fairly easy extension.

Translating Lustre expressions to SMT expressions using either one of the above encoding is pretty straightforward except for tuples and node calls.

#let tr(x) = $bracket.stroked #x bracket.r.stroked$

*Translating tuples.* I chose to flatten all tuples, that is translate and equate each member separately. For example, the Lustre statement $x, y = (e, d)$ is translated as $tr(x) = tr(e) and tr(y) = tr(d)$.

*Translating node calls.* I performed instantiation of a node every time it is called, aka inlining. This raises a scalability problem as, if this inlining is not taken into account for invariant generation (see @invgen), we need to learn invariants for each instance of the node separately. Kind2 comes up with different mechanisms to ensure modularity and scalability (compositional reasoning, modular reasoning, progressive refinements, ...) #footnote([See #link("https://github.com/kind2-mc/kind2/discussions/1256").]) @kind2 @instantiation-based-invariant-discovery which I chose not to implement.

= Houdini

== Generating candidate invariants <invgen>

== Sifting candidate invariants

<positive-examples>

= H-Houdini

H-Houdini @h-houdini, which stands for Hierarchical Houdini is a way to top-down/property directed.

== Overview

== Slicing

== Mining

== Abducting <abduct>

= Evaluation

#bibliography("bibliography.bib")
