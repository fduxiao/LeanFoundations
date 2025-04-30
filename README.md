# LeanFoundations

## Preliminaries
- Install [Lean](https://lean-lang.org/documentation/)
- We use [Just](https://just.systems/man/en/) to manage project-specific commands.


## Documents

```shell
just docs
# or
cd docbuild && lake build LeanFoundations:docs

# Then, the compiled HTML document is located in docbuild/.lake/build/doc
ls -al docbuild/.lake/build/doc
```

Check [here](https://leanprover-community.github.io/contribute/doc.html) for more informations.
