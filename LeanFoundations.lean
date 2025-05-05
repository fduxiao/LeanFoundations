/-
Copyright (c) 2025 Xiao Tan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan

-/

-- This module serves as the root of the `LeanFoundations` library.
-- Import modules here that should be built as part of the library.
import LeanFoundations.Logic
import LeanFoundations.PL



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
