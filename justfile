# update the dependencies
update:
    lake update LeanFoundations
    cd docbuild && lake update doc-gen4


# build docs
docs:
    cd docbuild && \
    bibtool --preserve.key.case=on \
            --preserve.keys=on \
            --print.use.tab=off \
            --pass.comments=on \
            -s -i docs/references.bib \
            -o docs/references.bib && \
    lake build LeanFoundations:docs


# build via leanbook
book:
    leanbook build .


# build docs and run an HTTP server
html: docs book
    cp -r docbuild/.lake/build/doc .lake/build/doc/api
    python3 -m http.server -b 127.0.0.1 -d .lake/build/doc
