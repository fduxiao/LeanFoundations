update:
    lake update LeanFoundations
    cd docbuild && lake update doc-gen4

docs:
    cd docbuild && lake build LeanFoundations:docs
