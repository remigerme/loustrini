#set text(font: "Libertinus Sans")
#set heading(numbering: "I.1 ")
#set par(justify: true)
#show link: set text(fill: red)
#show "TODO": set text(fill: red, weight: "bold", style: "italic")
#set page(numbering: "1 of 1")

#import "@preview/algorithmic:1.0.7"
#import algorithmic: algorithm-figure, style-algorithm
#show: style-algorithm

#align(center)[
  #text(size: 1.4em)[Loustrini: a Lustre model checker using the (H-)Houdini algorithm]

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

*Translating tuples.* I chose to flatten all tuples, that is translate and equate each member separately. For example, the Lustre statement $x, y = (e, d)$ is translated as $(tr(x) = tr(e)) and (tr(y) = tr(d))$.

*Translating node calls.* I performed instantiation of a node every time it is called, aka inlining. This raises a scalability problem as, if this inlining is not taken into account for invariant generation (see @invgen), we need to learn invariants for each instance of the node separately. Kind2 comes up with different mechanisms to ensure modularity and scalability (compositional reasoning, modular reasoning, progressive refinements, ...) #footnote([See #link("https://github.com/kind2-mc/kind2/discussions/1256").]) @kind2 @instantiation-based-invariant-discovery which I chose not to implement.

= An invariant learning algorithm: Houdini

I first provide a very brief overview of invariant learning algorithms, and then focus on Houdini.

== Overview of invariant learning algorithms

The context is the following: we want to prove a property $P$ _by induction_ on a given program. $P$ might not be inductive by itself, so we want to strenghten it with inductive lemmas (_.i.e._ invariants) to make the resulting set of properties inductive. Invariant learning algorithms can be classified in two classes: bottom-up or top-down (property-directed) algorithms.

*Bottom-up.* These algorithms try to learn as many inductive invariants on the program as possible. This learning process is executed without any specific desired property. Then, we can check if the learned invariants make the desired property inductive. We might have learned many invariants which appear to be useless when looking at the desired property. Houdini @houdini and instantiation-based invariant discovery @instantiation-based-invariant-discovery #footnote("Morally, the algorithm described as instantiation-based invariant discovery can be seen as an instance of Houdini.") are instances of bottom-up algorithms.

*Top-down.* These algorithms try to strenghten the desired property until it is inductive. IC3 @ic3 and (unlike Houdini) H-Houdini are property-directed algorithms.

As mentioned earlier, real-world projects such as Kind2 use both kinds of algorithms simultaneously to perform an efficient and modular analysis. In practice, bottom-up algorithms (at least the ones studied here) are simpler than top-down ones.

== Houdini

Houdini consists in three steps:
- generate (a huge number of) candidate invariants according to some templates,
- remove candidates invalidated by positive examples, that is a trace of execution of the program,
- remove predicates that break inductivity; iterate this step until the overall property is inductive.

Also, an additional step consists in filtering "obvious" invariants. This leads to a less polluted output of Loustrini when printing learned invariants.

=== Generating candidate invariants <invgen>

I used the following templates for boolean and numeric (integer and real) variables:

$
                          cal(I)_b & ::= b = "true" | b = "false" | b_1 = b_2 | b_1 = not b_2 \
                      cal(I)_"num" & ::= x diamond.small "cst" | x_1 diamond.small x_2 \
  "where" space.quad diamond.small & ::= = | != | >= | > | <= | < \
                             "cst" & ::= -1 | 0 | 1 | {"any numeric value hardcoded in the program"}
$

Above, $b$, $b_1$, and $b_2$ are boolean variables, and $x$, $x_1$, and $x_2$ are integer (or real) variables. All possible candidates are generated using these templates. This unfortunately leads to contradictory candidates, which we need to be cautious about when trying to remove invalid candidates.

=== Sifting candidate invariants <positive-examples>

*Removing candidates breaking inductivity.* Let's take things backwards and start with the third step. We consider a set of candidates ${h_1, ..., h_d}$ and $H = and.big_(i=1)^d h_i$. Is $H$ inductive? We use the following query:

$
  Delta(n) and Delta(n+1) and H(n) and not H(n+1) space.quad ?
$
$
  & mono("UNSAT"): H "is inductive OR" H(n) "contradicts" Delta(n) and Delta(n+1) \
  & mono("SAT"): exists "cex"\, "cex" tack.r.double H(n) and "cex" tack.r.double not H(n+1)) space i.e. space exists i in {1, ..., d}, "cex" tack.r.double not h_i (n+1)
$

Using the counterexample $"cex"$, we remove all candidates that are invalidated by it, and we iterate until the remaining $H$ is inductive (the empty set in the worst case).

This method is complete relatively to the templates, that is, if an invariant exists as a conjunction of candidates, it will be found. That would not work at all with a naive algorithm consisting in checking every candidate separately.

Note that to be able to use this method, we need to ensure that $Delta(n) and Delta(n+1) and H(n)$ is not vacuously false, else we are not able to conclude when the query for inductivity is $mono("UNSAT")$.

*Initial sift using positive examples.* The role of this initial sift is twofold: first, it allows to make $H$ consistent with our system equations, then, it allows to greatly shrink the set of candidates, accelerating the third step of the algorithm. We can obtain positive examples (_i.e._ examples that the invariants must satisfy) by simulating a trace of execution of length $d$, for all $k <= d$:

$ Delta(0) and ... and Delta(k) and not H(k) $

$
  & mono("UNSAT"): H "is consistent with step" k \
  & mono("SAT"): exists "cex", ... "(similar as above, and we keep iterating for this" k")"
$

=== Comments on Houdini

Houdini is conceptually very simple, but this comes at a cost:
1. candidates generation is subject to combinational explosion,
2. we might need to perform many _large_ SMT queries before reaching an inductive set,
3. we can only learn invariants which are conjuncts of candidates given by the templates (compared to k-induction or IC3 which do not suffer from this restriction).

= H-Houdini <hh>

H-Houdini @h-houdini, which stands for Hierarchical Houdini aims at solving point 2. from above (and also point 1.), by making Houdini top-down/property-directed.

== Overview

Before explaining the algorithm, let's introduce the concept of abducts. An abduct $A$ for a property $p$ is a property that makes $p$ inductive. That is, we have $A and p => p'$.

A very simplified version of the algorithm is provided in @algo-hh. Intuitively, H-Houdini tries to divide-and-conquer the inductivity of $p$ using abducts. If an abduct fails, we need to backtrack.

#algorithm-figure("H-Houdini", {
  import algorithmic: *
  Procedure("learn", "p_target", {
    Comment[Returns $H$ an invariant that proves p_target or none]
    Assign($V$, $cal(O)_"slice" ("p_target")$)
    Assign($P$, $cal(O)_"mine" ("p_target", V)$)
    Assign("solution", "false")
    While("not solution", {
      Assign($H$, "p_target")
      Assign($A$, $cal(O)_"abduct" ("p_target", H)$)
      If([$A$ is none], Return("none"))
      Assign("solution", "true")
      For($p in A$, {
        Assign($H_"sol"$, "learn(p)")
        If([$H_"sol"$ is none], {
          Assign("solution", "false")
          Break
        })
        Assign($H$, $H and H_"sol"$)
      })
    })
    Return($H$)
  })
}) <algo-hh>

To find inductive invariants to prove p_target, H-Houdini works as follows:
1. First, we extract a set $V$ of variables on which p_target depends on, using a slice operator $cal(O)_"slice"$. $V$ is the set of all variables which can influence p_target in one step of execution.
2. Then, we generate a set of candidate invariants $P$ using an operator $cal(O)_"mine"$.
3. Then, until we found a solution or none is returned, we generate an abduct $A$ from $P$ using $cal(O)_"abduct"$. We require each call to $cal(O)_"abduct"$ to generate a new abduct $A$ or none if no new abduct is possible.

== Slicing
$cal(O)_"slice"$ was implemented by instrumenting the translation from Lustre to SMT. Note that the current implementation requires to handle equations of a node in (combinatorial) topological order, which was not implemented yet, so for now, equations should be written in topological order.

== Mining
$cal(O)_"mine"$ is very similar to the generation of candidates for Houdini, but we need to make sure that the generated invariants are consistent with p_target. As of submitting the project, the implementation could be more straightforward: I generate candidates without knowledge of p_target and then sift these candidates. It would be better to generate candidates with respect to p_target.

== Abducting <abduct>

This is the magical part, and so, where the issues are.

A method described in the paper is to emit the following query:

$ P and "p_target" and not "p_target'" $

If it is $mono("SAT")$, we return none. Else, it is $mono("UNSAT")$ and we fetch and return an unsat core using the SMT solver. Ideally, this unsat core should be "minimal" (because each assertion of the unsat core will (potentially) lead to a H-Houdini call).

I fail to see how this method allows to generate more than one abduct for given p_target and $P$. An other way would be to rely on the SMT solver directly, but to the best of my knowledge Z3 does not provide an API to compute abducts. cvc5 does but does not provide OCaml bindings.

Moreover, in practice, the unsat core returned by Z3 suffers from two issues:
- instead of being a list of simple assertions, it is a list containing only one expression: a large conjunction,
- and this conjunction seems very far from being minimal, for any reasonable definition of minimal, which really doesn't help as it would emit more proof obligations for H-Houdini.

As of submitting the project, this part contains known and also, for sure, yet unknown bugs.

= Evaluation

*Proving with Houdini.* Loustrini can successfully prove non k-inductive properties (see `ic3.lus`). Also, Houdini successfully finds invariants that would fail if tested separately (see remark on completeness in @positive-examples, and `ic_more.lus`).

However, Houdini (and H-Houdini) can easily fail: we generate candidates only for existing Lustre variables. It could be beneficial to introduce state variables (see `fib.lus`) and generate candidates for them too, at the risk of combinational explosion.

*Proving with H-Houdini.* This part is clearly not ready yet.

#bibliography("bibliography.bib")
