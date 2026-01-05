# Loustrini

A Lustre model-checker using the H-Houdini invariant learning algorithm.

## Installation

We need to install the following dependencies:

- dune
- z3
- (optional) ocaml-lsp-server when developing
- (optional) ocamlformat when developing
- (optional) typst to build the report

### Creating a switch

Create an opam switch using OCaml 5.3.0:

```shell
opam switch create loustrini 5.3.0
```

Don't forget to activate the switch:

```shell
eval $(opam env --switch=loustrini)
```

### Installing dependencies

This project uses the dune build system:

```shell
opam install dune
```

And the Z3 SMT solver OCaml bindings:

```shell
opam install z3
```

### Building and running

Then you can build the project using:

```shell
dune build
```

and run it with:

```shell
dune exec ./src/loustrini.exe file.lus node
```

### Building the report

The report is written using [Typst](https://github.com/typst/typst). Assuming Typst is installed on your system, it can be compiled using

```shell
typst compile report/report.typ
```

You can also build the presentation slides. Note that, as of submitting the project, this is only a very drafty version of the slides that I will present.

```shell
typst compile report/slide/slide.typ --root=report
```

## Usage

Loustrini supports two invariant learning backends:

- Houdini, used by default,
- H-Houdini, very experimental as of submitting the project, can be enabled using the `-hh` flag.

You can run Loustrini with dune:

```shell
dune exec ./src/loustrini.exe ./examples/ic3/ic3.lus check
```

or using H-Houdini:

```shell
dune exec ./src/loustrini.exe ./examples/ic3/ic3.lus check -- -hh
```

I strongly discourage to use H-Houdini for now, as the current abduct oracle is too messy to be used in practice. For more information on this issue, please refer to comments in the [code](./src/invariant/hhoudini.ml).

## Skimming the project

All source files are in the [`src`](./src/) directory:

- [`ast`](./src/ast/) contains the AST provided by the project template
- [`compile`](./src/compile/) contains the translation from Lustre to SMT for both encodings, even though I deprecated the `trans` (for transition system) because of updates in `common.ml`
  - [`env_kind.ml`](./src/compile/env_kind.ml) is probably the most important file as it contains the SMT encoding and how it is used to emit equations
- [`checking`](./src/checking/) contains the pipeline to prove a property:
  1. learn invariants using Houdini or H-Houdini (and add the desired property for Houdini),
  2. verify that these invariants are non-contradictory (should pass),
  3. verify that these invariants imply the desired property (should pass as we added the desired property when using Houdini),
  4. verify that initiation holds,
  5. verify that consecution holds.
- [`invariant`](./src/invariant/) contains the implementations for Houdini and H-Houdini.

## Acknowledgments

The skeleton of the project (see the [initial commit](https://github.com/remigerme/loustrini/commit/689e7a1439ee5960ce7f122506f1134aa755e688)) was provided by [Marc Pouzet](https://www.di.ens.fr/~pouzet/) and [Timothy Bourke](https://www.tbrk.org/) for the SYNC: Synchronous Programming of Reactive Systems class at [MPRI](https://mpri-master.ens.fr/).

## References

See [`bibliography.bib`](./report/bibliography.bib).
