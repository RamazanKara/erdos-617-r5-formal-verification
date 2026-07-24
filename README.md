# Erdős Problem 617 research repository

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21535385.svg)](https://doi.org/10.5281/zenodo.21535385)

**Exact status: unrestricted fixed \(r=5\)
`MACHINE-VERIFIED-RESOLUTION`; full all-\(r\) conjecture `OPEN`.** E058
exports the unconditional Lean declaration
`Erdos617.e058Problem617AtFive : Problem617At 5`. One uninterrupted audit of
the exact committed final source began with no local Lean build, checked 89
zero-RAT cores with two external checkers, rejected 356 corruptions, imported
89 LRAT theorems into Lean, proved 89 graph-semantic closures and eight
coverage modules, and ran 192 assumption queries. Its terminal receipt has
SHA-256
`789acb2bc829fcba0a5656fabca5a37d9d4fdd2b493858039ad0081cc37032d1`
and records `fresh_local_build=true` and
`resumed_after_core_replay=false`. The earlier raw clean-start/resume sequence
and hardened final-source replay remain retained as historical evidence. The
final theorem depends exactly on `propext`,
`Classical.choice`, and `Quot.sound`. It contains no project axiom or
`sorryAx`.

The preregistered raw branch-02 timing diagnostic failed its fixed 300-second
cap; the reduced side was not run and no speedup is claimed. The failed
diagnostic is retained and disclosed, but is not a theorem premise.

The mathematical source is Robert Sneiderman's fixed-\(r=5\) preprint. This
repository's contribution is an independent formal and certificate
verification, not authorship of that argument. OpenAI Codex materially
assisted the work; see `AI_USAGE.md`. Neither the formalization nor the
preprint has completed independent expert review, so the result is not an
`EXTERNALLY-VERIFIED-RESOLUTION`. This repository contains no \(K_{26}\)
counterexample and no unrestricted full-formula UNSAT certificate.

The approved public repository is
`RamazanKara/erdos-617-r5-formal-verification`. The project is licensed under
Apache-2.0; see `LICENSE`.

The public snapshot removes personal host-path prefixes from retained JSON
receipts and logs and uses a clean Git history so those paths cannot survive
in earlier commits. No pinned Lean source or certificate file was changed.
See `PUBLICATION_REDACTIONS.md` for the exact boundary and counts.

E034--E035 and E048--E057 provide the graph-theoretic Lean chain. E058 bridges
the exact E038/E042--E045 finite obstruction into that chain. Its 89
certificate branches cover all 26 neighborhood types and use two external
checkers plus 356 deliberate corruption rejections; the resulting
unsatisfiability theorems, graph semantics, relabeling, orbit coverage,
sorting, and branch composition are all checked in Lean. E047 additionally
certifies the four broad independence-three lower bounds at orders 19--22 with
four zero-RAT LRATs; its two broad independence-four searches are `UNKNOWN`.
E048 kernel-checks the manuscript's large admissible independence-two terminal
bound, including complement maximum degree at most four from order twelve and
the edge lower bound `choose n 2 - 2n`. E049 then kernel-checks the exact edge
decomposition, exterior independence reduction, and minimum-degree propagation
needed to prove all six large numerical bounds in the actual admissible
fixed-`r=5` context. The broader E047 order-24/25 formulas remain unproved, but
are no longer premises of this route. E050 directly kernel-checks the
order-eleven 36-edge endpoint; E051 proves the complete order-ten structure;
E052--E054 prove the small independence-three/four obstructions and both
order-fifteen classifications. Conditional on the explicit special-Brooks
proposition, E055 proves edge equalization and reaches an exact order-21,
55-edge residual. E056 independently eliminates that residual's complete
minimum-degree-four branch, so its verified minimum degree is now at least
five. E057 eliminates the complete minimum-degree-five branch and proves the
fixed-`r=5` upper statement conditional only on the explicit special-Brooks
proposition. E058 discharges that proposition and composes the unconditional
fixed-\(r=5\) theorem. See
`formal/README.md`,
`experiments/E058-r5-special-brooks-kernel-bridge-result.md`, and
`REPRODUCE_E058.md`.

This checkpoint establishes an executable specification, two independent exhaustive
coloring checkers, a verified sharp \(K_{25}\) affine-plane example, a proved
nonextension result for that exact example, and unrestricted local
Turán/triangle constraints that every hypothetical balanced coloring of \(K_{26}\)
must satisfy. The checked LRAT chain eliminates the original equality case and
every local count from 204 through 209, so the local count is at least 210 at
every vertex. E014 combines its complete six-target reduction with four final
unsplit neighbor-color availability certificates. This gives
\(B+3R\ge5460\), \(2R-M\ge2860\), and \(3M\ge2E+260\).

The unrestricted edge-count chain now also proves that every color class in a
hypothetical \(K_{26}\) coloring has at least 64 edges. E018 excludes 59 edges;
E027/E028/E024 exclude 60; E029 excludes 61; and E030 reduces 62 edges to four
residual graph classes and certifies that none has an unrestricted four-color
extension. E031 certifies the exact-63 component and residual catalogs,
exhaustively constructs the 48 final 6-Ore classes, and excludes every exact
unrestricted extension. Counts 64 and 65 remain open in this independent
machine-certificate chain; the E033 candidate proof excludes them by a
different human argument. Neither the earlier global necessary theorem nor the
local results are an UNSAT certificate for the full coloring problem.

E033 additionally pins
[`Robby955/erdos-617-fixed-cases`](https://github.com/Robby955/erdos-617-fixed-cases)
at commit `735c2eeffcb5c8abe92f8a6be04be2fa3c8bb6ab`, rebuilds and audits its complete
r=5 manuscript, rechecks the Kang--Pikhurko dependency, and independently
enumerates the order-10 and order-11 endpoint graphs. E058 now independently
machine-verifies the resulting fixed-\(r=5\) theorem. The same external
repository's r=6--9 claims have not yet been independently reproduced here.
Their pinned Git object database and in-repository SHA-256 manifests pass, but
that is only an integrity intake, not a proof or certificate replay; see
`docs/external-fixed-cases-intake-2026-07-22.md`.
Even if all those fixed cases are correct, they do not settle every r.

Run the complete local verification with:

```sh
./repro/verify.sh
```

The verified environment used Python 3.12.3 and GCC 13.3.0 on 64-bit WSL2 Linux.
Only the Python standard library and a C compiler are required. The verification
enumerates every \(\binom{25}{6}=177100\) subset twice, checks committed artifact
hashes, regenerates the affine construction, audits 23,751 degree profiles, and runs
positive, negative, malformed-input, scope-lock, and damaged-certificate tests.
It also regenerates the 18,630-clause equality CNF, the E006/E008/E011/E012
fixed incidence CNFs, and the classification-free E009/E011/E012 variable-graph
systems. E013 adds two classification-free one-exception systems, fourteen
exhaustive equality-template double-exception branches, and one independently
audited hard-branch representation quotient. E014 adds its complete arithmetic,
deletion, classification, counter-split, composition, full-LRAT, model-checker,
and neighbor-color availability audits. Verification regenerates and checks
the balanced-49 proof, thirteen direct classified proofs, and four final
unsplit availability proofs with a pinned upstream C checker and an independent
streaming Python checker. It audits every E011--E014 reduction used by the
theorem, audits the E009 search core semantically, and rejects proof and core
corruptions. E018 adds two exact 59-edge formulas and proofs. E024/E027/E028
add the exact 60-edge recursive reduction and its two certified finite
obstructions. E029 adds a 42,492-case transversal audit, a certified two-class
residual classification, and two certified exact remaining-color extension
obstructions for count 61. E030 adds complete equality/slack attachment and
critical-subgraph audits, a certified four-class residual classification, and
four certified exact remaining-color extension obstructions for count 62.
E031 adds a fresh complete attachment/component reduction, certified
one-class residual-12 and five-class residual-11 catalogs, an exhaustive
48-class 6-Ore construction for the final critical residual, and 13 checked
RUP-only certificates covering every residual and unrestricted extension.
E033 adds a separate semantic audit of 12,172 order-10 and 6,153 order-11
triangle-free representatives, all 20 endpoint equality templates, the full
arithmetic chain, minimum-cover facts, and all 177,100 affine six-sets.
E058 supersedes the conditional formal audit with a clean-start/hardened
historical replay and an uninterrupted exact-final-source replay of the
complete certificate-to-theorem bridge. E036--E045 add independent finite-Brooks formula, orbit,
sorting, cross-pattern, anchor, and local-clause audits. E038, E042--E043, and
E045 retain and dual-check 89 exact zero-RAT certificates covering all 26
neighborhood branches; E044's six capped timeouts are retained only as
non-evidence. E046--E047 add six exact broad extremal formulas, four checked
proofs, and two explicitly open timeouts; `make verify-r5-kp-large` replays
their complete structural and certificate audit. E048--E057 independently
replace the large numerical uses, all small endpoints and classifications,
edge equalization/low-degree recursion, both final residual branches, and the
conditional coloring contradiction with kernel-checked arguments, without
using those LRATs, the E033 graph catalog, or Kang--Pikhurko.
Large proof files are stored XZ-compressed and verified one at a time.

Optional byte-for-byte certificate reproduction is `make reproduce-certificate`;
it additionally requires `python-sat==1.9.dev7`. Normal verification neither
requires nor trusts that solver.

Optional reproduction of all E006 certificates is `make reproduce-local-204
CADICAL=/path/to/cadical`; it requires official CaDiCaL 1.9.5. Normal
verification neither runs nor trusts CaDiCaL.

E008 reproduction is `make reproduce-local-205 CADICAL=/path/to/cadical`.
E009 reproduction is
`make reproduce-local-205-near KISSAT=/path/to/kissat`; it requires official
Kissat 4.0.4 and takes about nine minutes for proof search on the recorded
machine. Normal verification neither runs nor trusts either solver.

E011 fixed-catalog reproduction is
`make reproduce-local-206 CADICAL=/path/to/cadical`. Its variable-graph proofs
are reproduced by
`make reproduce-local-206-near KISSAT=/path/to/kissat`; the hardest branches
use the recorded 30-minute cap. Normal verification checks certificates but
does not run or trust either solver.

E012's redundant fixed certificates are reproduced by
`make reproduce-local-207 CADICAL=/path/to/cadical`. Its two selected
classification-free proofs are reproduced by
`make reproduce-local-207-near KISSAT=/path/to/kissat`; both use the recorded
15-minute cap. Normal verification checks certificates but does not run or
trust either solver.

E013's two one-exception proofs are reproduced by
`make reproduce-local-208 KISSAT=/path/to/kissat`. Its fourteen exhaustive
double-exception proofs, including the hard quotient, are reproduced by
`make reproduce-local-208-classified KISSAT=/path/to/kissat`. Both require the
pinned official Kissat 4.0.4 binary. Normal verification checks every proof but
does not run or trust Kissat.

E014 is complete at its exact local-count-209 scope. Its reduction, diagnostic
models, failed searches, redundant counter leaves, and final availability
certificates are in `experiments/E014-local-209-result.md` and
`experiments/E014-local-209-plan.md`. Normal verification checks the four
unsplit availability proofs; uncomposed split leaves are not presented as
parent proofs.

E018, E024/E027/E028, E029, E030, and E031 are complete at exact minority-color
counts 59, 60, 61, 62, and 63.
Their mathematical scope, raw and compressed hashes, certificate statistics,
and trust boundaries are recorded in the corresponding result files under
`experiments/`. Earlier E019--E023, E025, and E026 `UNKNOWN` runs and the SAT
model of a deliberately weaker relaxation are retained only as exploratory
records and are not theorem premises.

## AI-assistance disclosure

OpenAI Codex materially assisted with formalization, verification automation,
documentation, LaTeX, and execution of the audit workflow. Codex is not an
author, and its textual assertions are not mathematical evidence. Exact scope,
responsibility, and verification boundaries are recorded in `AI_USAGE.md`.

Start with `RESEARCH_GOAL.md`, `STATE.md`, `CLAIMS.md`, and `NEXT.md`. Exact
definitions are in `docs/problem-spec.md`; proof details and the audit of the
published \(r=3,4\) arguments are in `docs/theory-notes.md`.

## License

Copyright 2026 Ramazan Kara. Licensed under the Apache License, Version 2.0.
See `LICENSE`.
