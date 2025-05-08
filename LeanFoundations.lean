/-
Copyright (c) 2025 Xiao Tan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan

-/

import LeanFoundations.Logic
import LeanFoundations.PL


/-!
# Preface
We are inspired by the [Software Foundations (SF)][Pierce:SF1]
series. There should also be a systematic introduction to `how to
programming and verify algorithms in lean`. Yet, we are more ambitious
in that we want to show how to make a (toy) lean out of lean itself and
verify related code. We assume you know nothing about computer programming,
but we do assume you are familiar with Unix-like operating systems
(shell commands, text editors, file systems, etc) so that you know how to
install `lean`, write the code and run other tools like `lake` or `elan`.
If you are taking/teaching a course, then the first class should be about
how to use a Unix-like operating system, system-wide software package
management and install `lean`. And, some kind of proficiency of mathematics
is helpful (and maybe necessary, e.g., you have to know natural numbers and
mathematical induction on them).

The whole book is built on
[this Github repository](https://github.com/fduxiao/LeanFoundations).
It is just an ordinary `lean` package where the `module comments` are compiled
as descriptions in this book, while the lean codes are displayed with
a light green background. You can clone the repository or just make your
own `lake project` and copy those lines.
-/

/-TOC-/
/-!
# Contents
- `LeanFoundations.Logic`: Logical foundations in Lean
- `LeanFoundations.PL`: Programming language foundations in Lean
-/

/-!
# QuickStart

## Install Lean

### Command line
I prefer installing everything through CLI.

First, install [elan](https://github.com/leanprover/elan), the Lean version manager.
```shell
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

Then, install toolchains
```shell
elan self update
elan default leanprover/lean4:stable
```

### VSCode
See [here](https://docs.lean-lang.org/lean4/doc/quickstart.html).

### Homebrew
```shell
brew install elan-init
```

## Make a project
```shell
lake new foo
cd foo
lake build
.lake/build/bin/foo
```
-/

/-!
# Reference
- [Software Foundations (SF)][Pierce:SF1]
- [Programming Language Foundations in Agda (PLFA)][plfa22_08]
-/
