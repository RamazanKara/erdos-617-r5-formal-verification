# E045 — zero-anchor quotient and complete finite Brooks result

Checkpointed: 2026-07-22 (Europe/Berlin)

Status: `PARTIAL-CERTIFIED` for the finite special-Brooks theorem used by
E035. This is not a complete proof of fixed r=5 and says nothing about all r.

## Exact quotient and audit correction

The initial preregistration incorrectly described all six remaining
neighborhood masks as six-edge graphs. The independent pre-solver audit caught
the error. Their exact internal-edge counts are `4,5,6,6,5,6`, hence their
cross-stub totals are `12,10,8,8,10,8`; at least
`8,10,12,12,10,12` of the twenty exterior rows are zero. The plan and
generator assertions were corrected before proof search.

Choose one guaranteed zero-cross-pattern exterior vertex as anchor `6`. Its
five degree-forced exterior neighbors may be relabelled `7,...,11`, with the
fourteen nonneighbors relabelled `12,...,25`. Sorting cross patterns only
within those two freely permutable classes is orbit-retaining. The independent
audit verifies all six mask/stub calculations, 144 primary anchor units, 102
five-bit lex comparisons, all 413,721 E044 clauses, and 720 at-most-six
clauses for the six fixed anchor neighborhoods. All 1,024 lex truth rows pass.

## Certificates and complete neighborhood coverage

All six E045 branches `20,...,25` returned UNSAT and converted to verified
zero-RAT LRATs. Every formula regenerates exactly, and both the pinned C and
independent Python checkers accept every proof. The receipt
`artifacts/e045_zero_anchor_quotients/receipt.json` has SHA-256
`9481c920cb33de9afb20eac982fd517fd8bac5ebbd5986f91d67459f5cd0fdde`.

The complete finite coverage is now:

```text
E038: neighborhood branches 00--18          19 certificates
E042: branch 19 direct cross-patterns        17 certificates
E043: branch 19 residual subbranches         47 certificates
E045: neighborhood branches 20--25            6 certificates
                                                   --
total                                              89
```

The persistent residual verifier checks the 70 new formulas/proofs with 70 C
acceptances, 70 Python acceptances, 280 deliberate corruption rejections, 70
exact regenerations, and 70 raw/XZ hash round trips. Together with E038, the
full inventory has 89 certificates and 356 corruption rejections. The 70 new
compressed CNFs occupy 58,827,988 bytes and the compressed LRATs 103,120,240
bytes; their raw sizes and every individual hash are in the three receipts.
The clean combined replay log is
`artifacts/e045_special_brooks_verify.log`, SHA-256
`ae39396770fb20f28cf6dfd00af46978c7881d5f002f8af36f159bd3ab41bd25`.

Therefore no admissible simple graph on 26 vertices is simultaneously
5-regular, independent-six-free, and six-clique-free. This discharges the
finite hypothesis of E035 at the two-checker certificate level. The LRAT chain
is not imported into the Lean kernel, so the existing Lean theorem remains
syntactically conditional; Kang--Pikhurko, later endpoint layers, and the
final fixed-r=5 contradiction remain outside the complete checked graph.

Reproduce the exact finite theorem with

```sh
make verify-r5-special-brooks
```

An unsafe anchor quotient, incorrect zero-row lower bound, omitted
neighborhood/cross-pattern/anchor branch, formula mismatch, non-zero-RAT
dependency, checker failure, accepted corruption, or content-hash mismatch
falsifies the certified theorem.
