# update the dependencies
update:
    lake update LeanFoundations


# build docs
format-bib:
    bibtool --preserve.key.case=on \
            --preserve.keys=on \
            --print.use.tab=off \
            --pass.comments=on \
            -s -i references.bib \
            -o references.bib


# build via leanbook
book:
    leanbook build .


# build docs and run an HTTP server
html: format-bib book
    python3 -m http.server -b 127.0.0.1 -d .lake/build/doc
