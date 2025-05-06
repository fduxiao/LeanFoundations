# LeanFoundations

## Preliminaries
- Install [Lean](https://lean-lang.org/documentation/).
- We use [Just](https://just.systems/man/en/) to manage project-specific commands.

To show what commands we have, run `just --list`.

## Documents

Lean provides [doc-gen](https://github.com/leanprover/doc-gen4) to build
documents from doc strings and module comments. To build them,

```shell
just docs
# or
cd docbuild && lake build LeanFoundations:docs

# Then, the compiled HTML document is located in docbuild/.lake/build/doc:
ls -al docbuild/.lake/build/doc
```

But this method is not suitable for a book, so we write another tool
[leanbook](https://github.com/fduxiao/leanbook) for better presentation
of the book.

```shell
# install leanbook
pip install git+https://github.com/fduxiao/leanbook
# compile
leanbook build .

# The compiled book also contains api document, so
cp -r docbuild/.lake/build/doc .lake/build/doc/api
python3 -m http.server -b 127.0.0.1 -d .lake/build/doc
```

You can compile, copy and run an HTTP server with python by `just html`.

Check [here](https://leanprover-community.github.io/contribute/doc.html) if
you want to know the document conventions for Lean.
