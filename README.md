# LeanFoundations

## Preliminaries
- Install [Lean](https://lean-lang.org/documentation/).
- We use [Just](https://just.systems/man/en/) to manage project-specific commands.

To show what commands we have, run `just --list`.

## Documents

Lean provides [doc-gen](https://github.com/leanprover/doc-gen4) to build
documents from doc strings and module comments. However this method is not suitable
for this book, so we write another tool [leanbook](https://github.com/fduxiao/leanbook) 
for better presentation of the book.

```shell
# install leanbook
pip install git+https://github.com/fduxiao/leanbook
# compile
leanbook build .

python3 -m http.server -b 127.0.0.1 -d .lake/build/doc
```

You can compile, copy and run an HTTP server with python by `just html`.

Check [here](https://leanprover-community.github.io/contribute/doc.html) if
you want to know the document conventions for Lean.
