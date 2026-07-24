# E042 — branch-19 cross-pattern split: result

Checkpointed: 2026-07-22 (Europe/Berlin)

Status: `PARTIAL-CERTIFIED`. The exact 20-orbit split is independently
exhaustive. Seventeen children have direct checked zero-RAT LRATs; children
`04`, `09`, and `19` are covered by the complete E043 residual split. Thus
E042 together with E043 certifies E038 neighborhood branch 19, but E042 alone
does not certify its three residual children.

The `K4` plus isolated-neighbor type has cross-column sums `(1,1,1,1,4)`.
Independent set-partition and direct labelled-row enumerations recover 94 raw
row multisets and exactly 20 orbits under `S4 x S20`, with nonzero-row
distribution `4:5, 5:7, 6:5, 7:2, 8:1`. Every child has 3,930 variables,
493,836 clauses, and 100 fixed cross-edge units.

Direct children

```text
00 01 02 03 05 06 07 08 10 11 12 13 14 15 16 17 18
```

regenerate exactly and have RUP-only LRATs accepted by the pinned upstream C
checker and independent Python checker. The three capped `UNKNOWN` results
`04`, `09`, and `19` are non-evidence; no incomplete trace was retained.

The receipt at `artifacts/e042_branch19_cross_patterns/receipt.json` records
every raw/compressed hash, dimension, solver return, and tool hash. Its SHA-256
is `f1a42f4ebe2c3ccd28e5e050e52e494800e210e473458cd1466146e05bdd9319`.
The 17 CNFs and proofs are under `artifacts/e042_branch19_cross_patterns/` and
`certificates/e042_branch19_cross_patterns/`.

Reproduce the structural and certificate audits with

```sh
python3 tests/test_r5_brooks_branch19_cross_pattern_cnf.py
python3 tests/test_r5_brooks_residual_certificates.py
```

An omitted row multiset or orbit, unsafe `S4` action, wrong primary unit,
uncovered residual, regeneration mismatch, proof/checker failure, accepted
corruption, or hash mismatch falsifies the certified scope.
