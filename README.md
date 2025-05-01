# LeanFoundations

## Preliminaries
- Install [Lean](https://lean-lang.org/documentation/).
- We use [Just](https://just.systems/man/en/) to manage project-specific commands.

To show what commands we have, run `just --list`.

## Documents

To build the documents,

```shell
just docs
# or
cd docbuild && lake build LeanFoundations:docs

# Then, the compiled HTML document is located in docbuild/.lake/build/doc
ls -al docbuild/.lake/build/doc
```

You can run an HTTP server with python by `just html`.

The documents are built from doc strings and sectioning comments automatically by [doc-gen](https://github.com/leanprover/doc-gen4).
Check [here](https://leanprover-community.github.io/contribute/doc.html) for more informations.
