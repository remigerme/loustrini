# Loustrini

A Lustre model-checker using the H-Houdini invariant learning algorithm [1].

## Installation

We need to install the following dependencies:

- dune
- smtml
- (optional) ocaml-lsp-server when developing
- (optional) ocamlformat when developing
- (optional) typst to build the report

### Creating a switch

Create an opam switch using OCaml 5.3.0:

```shell
opam switch create 5.3.0
```

Don't forget to activate the switch:

```shell
eval $(opam env --switch=5.3.0)
```

### Installing dependencies

This project uses the dune build system:

```shell
opam install dune
```

Instead of Alt-Ergo Zero, Loustrini relies on [Smt.ml](https://github.com/formalsec/smtml) to manage SMT solvers:

```shell
opam install smtml
```

### Building and running

Then you can build the project using:

```shell
dune build
```

and run it with:

```shell
dune exec ./bin/loustrini file.lus node
```

### Building the report

The report is written using [Typst](https://github.com/typst/typst). Assuming Typst is installed on your system, it can be compiled using

```shell
typst compile report/report.typ
```

## Acknowledgments

The skeleton of the project (see the [initial commit](https://github.com/remigerme/loustrini/commit/689e7a1439ee5960ce7f122506f1134aa755e688)) was provided by [Marc Pouzet](https://www.di.ens.fr/~pouzet/) and [Timothy Bourke](https://www.tbrk.org/) for the SYNC: Synchronous Programming of Reactive Systems class at [MPRI](https://mpri-master.ens.fr/).

## References

- [1] Sushant Dinesh, Yongye Zhu, and Christopher W. Fletcher. 2025. H-Houdini: Scalable Invariant Learning. In Proceedings of the 30th ACM International Conference on Architectural Support for Programming Languages and Operating Systems, Volume 1 (ASPLOS '25). Association for Computing Machinery, New York, NY, USA, 603–618. https://doi.org/10.1145/3669940.3707263
