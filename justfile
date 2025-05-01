# update the dependencies
update:
    lake update LeanFoundations
    cd docbuild && lake update doc-gen4

# build docs
docs:
    cd docbuild && lake build LeanFoundations:docs

# build docs and run an HTTP server
html: docs
    python3 -m http.server -b 127.0.0.1 -d docbuild/.lake/build/doc
