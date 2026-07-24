# E038 — exterior-pattern finite Brooks branches: result

Checkpointed: 2026-07-22 (Europe/Berlin)

Status: `PARTIAL-CERTIFIED` for neighborhood branches 00 through 18 only.
Branches 19 through 25 remain open, so neither the finite special-Brooks
statement nor the fixed (r=5) theorem is certified by this experiment.

## Exact finite formula and split

E036 encodes all simple graphs on 26 labelled vertices that are 5-regular,
have no independent six-set, and have no six-clique.  Fixing the five neighbors
of vertex 0 is a safe relabelling.  The independently audited monolithic CNF
has 3,835 variables and 473,771 clauses, including both polarities for all
230,230 six-sets and full degree-counter recurrences.

For the admissible color graphs relevant to E035, its kernel-checked local
bound restricts the fixed five-neighbor graph to at most six edges. E037
enumerates all 1,024 labelled graphs on that set under all 120 permutations.
There are 34 graph orbits in total and exactly 26 with at most six edges, with
distribution

```text
0:1, 1:1, 2:2, 3:4, 4:6, 5:6, 6:6.
```

E038 uses the remaining free permutation of the 20 exterior vertices to sort
their five-bit adjacency vectors into the fixed neighborhood.  Its 19 full
prefix-equality comparisons were exhaustively checked on all 1,024 pairs of
five-bit vectors.  Every branch CNF has 3,930 variables and 474,332 clauses.

## Certified branch inventory

Branches

```text
00 01 02 03 04 05 06 07 08 09 10 11 12 13 14 15 16 17 18
```

have retained compressed CNFs and RUP-only LRAT certificates.  For every
branch, the CNF regenerates exactly; `drat-trim -U -L` reports zero essential
RAT lemmas; the pinned upstream C LRAT checker and independent Python LRAT
checker both derive the empty clause; truncation and forged-empty corruptions
are rejected by both; and compressed/raw hashes round-trip.  The final
regression reports

```text
R5-BROOKS-EXTERIOR-SORTED-CERTIFICATE-PASS certified_branches=19 open_branches=7 c_checks=19 python_checks=19 negative_checks=76 exact_regenerations=19 zero_rat=19
```

The complete per-branch dimensions, neighborhood masks, compressed and raw
hashes, and pinned tool hashes are in
`artifacts/e038_brooks_branches/receipt.json`, whose SHA-256 is
`4dc9b52aa30c321f14a8be873cf61b09cd53400dd29aac0f78288da9fa8c32af`.

Reproduce the semantic audits and certificate verification with

```sh
python3 tests/test_r5_five_regular_brooks_cnf.py
python3 tests/test_r5_brooks_neighborhood_branch_cnf.py
python3 tests/test_r5_brooks_exterior_sorted_cnf.py
python3 tests/test_r5_brooks_exterior_sorted_certificates.py
```

## Open branches and capped searches

Branches 19, 20, 21, 22, 23, 24, and 25 have no retained certificate.  The
batch stopped when branch 19 returned `UNKNOWN` at the preregistered 90-second
solver cap.  Branch 19 has neighborhood mask 183, a `K4` plus an isolated
neighbor.

The following results are search metadata only:

- E036's monolithic 590-second Kissat run returned `UNKNOWN`.
- E037 branches 00 and 17, before exterior sorting, returned `UNKNOWN` at 90
  seconds.
- E039 branch 19 / first exterior pattern 00 returned `UNKNOWN` at 90 seconds.
- E040 independently audited 19,404 additional admissibility clauses for all
  231 `K4`-plus-pair six-sets, but Kissat returned `UNKNOWN` at 90 seconds.
- E041 ran pinned CaDiCaL 1.9.5 in plain mode on that unchanged 493,736-clause
  E040 formula and returned `UNKNOWN` at 290 seconds.

All incomplete traces from these runs were deleted.  Timeouts, solver
agreement, and raw solver status are not evidence for satisfiability or
unsatisfiability.

## Exact conclusion

The 19 certificates prove that no admissible graph satisfying the finite
special-Brooks hypotheses occurs in those 19 neighborhood orbits. (Each CNF
is a safe relaxation: it needs only the selected neighborhood consequence of
admissibility.) They say nothing beyond that union of branches. An omitted
neighborhood orbit, unsafe exterior quotient, clause mismatch, checker error,
accepted corruption, or hash mismatch
falsifies the certified scope.  Certifying all seven open branches (or proving
the special theorem directly in Lean) remains necessary before E035 can remove
its explicit Brooks hypothesis.
