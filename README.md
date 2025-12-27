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
dune exec ./bin/loustrini.exe file.lus node
```

### Building the report

The report is written using [Typst](https://github.com/typst/typst). Assuming Typst is installed on your system, it can be compiled using

```shell
typst compile report/report.typ
```

You can also build the presentation slides. Note that this was a very early presentation, way before Loustrini was completed.

```shell
typst compile report/slide/slide.typ
```

## Acknowledgments

The skeleton of the project (see the [initial commit](https://github.com/remigerme/loustrini/commit/689e7a1439ee5960ce7f122506f1134aa755e688)) was provided by [Marc Pouzet](https://www.di.ens.fr/~pouzet/) and [Timothy Bourke](https://www.tbrk.org/) for the SYNC: Synchronous Programming of Reactive Systems class at [MPRI](https://mpri-master.ens.fr/).

## References

See [`bibliography.bib`](./report/bibliography.bib).
