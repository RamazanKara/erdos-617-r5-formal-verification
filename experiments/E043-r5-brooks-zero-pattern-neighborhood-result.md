# E043 — branch-19 residual anchor neighborhoods: result

Checkpointed: 2026-07-22 (Europe/Berlin)

Status: `PARTIAL-CERTIFIED`, with all 47 exact residual children certified.

The three open E042 parents have zero-pattern exterior class sizes 14, 15, and
16. Relabelling a zero-pattern vertex as anchor `6`, and quotienting its
degree-five neighborhood by the exact residual row/K4 stabilizer, gives
respectively 26, 16, and 5 orbits. An independent row-class invariant audit
recovers every orbit and no duplicate. Each formula retains its exact E042
prefix, fixes all 19 possible anchor-to-exterior edges with exactly five
positive units, and has 3,930 variables and 493,855 clauses.

All 47 formulas regenerate byte-for-byte. Every proof converts to a verified
zero-RAT LRAT and passes both LRAT checkers. The persistent combined verifier
also rejects a truncation and forged empty derivation with both checkers for
every proof.

The receipt at `artifacts/e043_branch19_zero_neighborhoods/receipt.json` has
SHA-256
`fd60b220ab27b19a221eaebaa7893b3c1b0c3293cfd484da602dc06eb0f95a1d`.
The retained CNFs and LRATs are in the corresponding `artifacts/` and
`certificates/` directories. Together with the 17 direct E042 certificates,
these 47 proofs cover all 20 cross-pattern parents and certify neighborhood
branch 19.

Reproduce with

```sh
python3 tests/test_r5_brooks_zero_pattern_neighborhood_cnf.py
python3 tests/test_r5_brooks_residual_certificates.py
```

An unsafe zero-row choice, incomplete stabilizer, omitted subset orbit, wrong
degree unit, missing E042 parent, proof/checker failure, accepted corruption,
regeneration mismatch, or hash mismatch falsifies the result.
