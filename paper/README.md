# Formal-verification preprint

This directory contains the self-contained preprint documenting the
machine-verified fixed `r = 5` result. Ramazan Kara completed the local
cross-check and approved public release on 24 July 2026.

Build from this directory with:

```sh
make clean all
```

The build runs `latexmk` with `pdflatex` and BibTeX.  The final artifact is
`erdos617-r5-formal-verification.pdf`.  The unrestricted all-`r` conjecture is
not claimed.

The current build, after a post-release prose revision, is 11 A4 pages, is
390,512 bytes, and has SHA-256
`fbcd4e1b8b9fd94f91b387f417cb5a2418ee5e8e826ffc2ddb501a02b7ca0743`.
Two clean builds produced byte-identical PDFs, the final TeX log has no
warnings or overfull/underfull boxes, and all 11 Poppler-rendered pages were
visually inspected.

OpenAI Codex materially assisted with the formalization, verification
automation, documentation, and preprint.  Its assertions are not treated as
mathematical evidence; the claim rests on replayable certificates and
kernel-checked Lean declarations.  The preprint contains the full disclosure.
