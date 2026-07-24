# E058 result — special-Brooks obstruction imported into Lean

Status: `MACHINE-CERTIFIED`.

Fixed \(r=5\) project level: `MACHINE-VERIFIED-RESOLUTION`.

All-\(r\) project level: `OPEN`.

## Result

E058 closes the sole explicit mathematical premise left by E057. The pinned
Lean kernel now checks:

```lean
theorem e058R5SpecialBrooksObstruction :
    R5SpecialBrooksObstruction

theorem e058NoR5Counterexample :
    ¬∃ χ : EdgeColoring (Fin 26) (Fin 5), IsCounterexample 6 χ

theorem e058R5Upper : R5Upper

theorem e058Problem617AtFive : Problem617At 5
```

The last theorem is unconditional: its type contains no special-Brooks,
certificate, solver, or project-defined premise. It proves only Erdős Problem
617 at fixed \(r=5\). It neither proves the all-\(r\) conjecture nor verifies
the pinned external claims for \(r=6,\ldots,9\).

## Attribution and contribution

The proof architecture and original mathematical proof are attributed to
Robert Sneiderman's Robby955 preprint, pinned at Git commit
`735c2eeffcb5c8abe92f8a6be04be2fa3c8bb6ab`. E033 independently audited that
manuscript. E034--E057 reconstructed its mathematical chain as explicit Lean
theorems and independently checked finite endpoints.

The new E058 contribution is independent formal verification of the remaining
finite special-Brooks obstruction: deterministic certificate reduction,
dual-checker replay, generated staged Lean proofs, graph-semantic closure
proofs, exhaustive branch coverage, assumption auditing, retained evidence,
and reproducible packaging. This is not a claim of authorship of Sneiderman's
mathematical argument.

## Checked certificate-to-kernel chain

The theorem-bearing inventory is exactly the 89 RUP-only cores covering all 26
neighborhood-orbit branches:

- 19 E038 branches;
- 17 E042 direct cross-pattern children;
- 47 E043 residual anchor-neighborhood children; and
- 6 E045 zero-anchor quotient branches.

The audit performed all of the following:

1. regenerated all 89 source unit CNFs;
2. deterministically extracted every reachable RUP core;
3. checked every reduced CNF/LRAT pair with the pinned C checker;
4. checked the same 89 pairs with an independent Python checker;
5. required both checkers to reject a truncation and a forged empty-clause
   proof for every core, giving 356 negative outcomes;
6. regenerated and kernel-checked all 89 staged Lean imports;
7. regenerated and kernel-checked all 89 graph-semantic closure theorems;
8. compiled eight coverage modules culminating in
   `E058SpecialBrooksCoverage.lean`;
9. audited 192 theorem assumption sets; and
10. scanned the final source and output for warnings and forbidden constructs.

The final source inventory contains 51 Lean files. The retained generated
inventory contains 466 Lean files, with combined SHA-256
`c79bbd0b3deea2af4ed0c95cd15566c8c708b146ee2f5100b8256230dcb04b8e`.

## Core aggregate

The independently recomputed aggregate covers:

- 89 source CNFs;
- 2,709,936,427 decompressed CNF bytes;
- 43,878,934 source clauses;
- 795,950,803 decompressed LRAT bytes;
- 1,274,831 RUP additions and zero RAT additions;
- 183,145 retained source clauses;
- 441,983,911 reduced-LRAT bytes; and
- 48,467,568 map bytes.

All proof additions reachable from the final empty clauses were retained.
Solver UNSAT output is not evidence; the checked proof chains are.

## Successful audit evidence

### Uninterrupted exact committed source

The exact committed final source at
`d19a0cf786a0fa714289830f276cf406408ab65b` was extracted into a mirror with
no `formal/lean/.lake/build` directory. The independent C LRAT checker was
compiled from its committed upstream source before the audit began. One
uninterrupted process then completed every E058 gate and exited zero:

```text
E058-FRESH-LEAN-AUDIT-PASS cores=89 kernel_imports=89 semantic_closures=89 axiom_queries=192 warnings=0 forbidden_hits=0 receipt_sha256=789acb2bc829fcba0a5656fabca5a37d9d4fdd2b493858039ad0081cc37032d1
```

The receipt records `fresh_local_build=true`,
`resumed_after_core_replay=false`, a 51-file final-source inventory matching
the committed SHA-256 aggregate, and a 466-file generated-source inventory
matching the committed aggregate. The run took 25,497.97 seconds.

- Exact-HEAD audit-receipt SHA-256:
  `789acb2bc829fcba0a5656fabca5a37d9d4fdd2b493858039ad0081cc37032d1`.
- Byte-identical audit/driver transcript SHA-256:
  `52f10416d02808c606bcffff53871f0a9c37c0ab15606235f00f33031b97fb2a`.
- Exact executed runner SHA-256:
  `f2a504d3c9588cb14e9256cfed624fbcc46b10047d8e8fd9f2b8b4f1b76a6620`.
- Core aggregate receipt SHA-256:
  `d5c4413e2843d7855148c63c78501a61e1e281893a339f23196f76108f422c2c`.
- Kernel aggregate receipt SHA-256:
  `57f39d08fb019d2d211c3e95013d6a998ad8aa9b17e8e65f04866ba84c7ec29d`.
- Semantic aggregate receipt SHA-256:
  `5e366f024444474f74483baa257661819a279263e8ee57d71f1d9350c9abe6b4`.
- Exact-HEAD evidence-collection receipt SHA-256:
  `2f9a1d9e4027998eb3405a2db92f2130886f4eac7fd3137c4db36325eee7c047`.

Two preceding exact-source attempts are retained as infrastructure
diagnostics, not successful evidence: the first was externally terminated at
the command-session boundary, and the second stopped before core replay
because the fresh mirror lacked the separately built C checker. Neither wrote
a terminal receipt. Exact hashes and dispositions are in
`artifacts/e058_special_brooks_kernel_bridge/exact_head_fresh_audit/ATTEMPTS.md`.

### Earlier raw clean start

The raw no-local-build run completed all 89 kernel imports, all 89 semantic
closures, all eight coverage modules, and all 192 assumption queries:

```text
E058-FRESH-LEAN-AUDIT-PASS cores=89 kernel_imports=89 semantic_closures=89 axiom_queries=192 warnings=0 forbidden_hits=0
```

- Raw clean-start receipt SHA-256:
  `d1b00435407e6811bb5e128bb5dbdc953e0a71ba01dacacc2b999b7b7a1bbddd`.
- Raw clean-start transcript SHA-256:
  `486267f93b823959bdc76c7e5daba13fb06523a3abf6446ea9042c331efd6d7a`.
- Exact executed runner SHA-256:
  `c69d27f7ca1cc5c98c087c287f832ca9d1ed4925d21f4166f762af1c0b37fb72`.
- Independently validated sequence-receipt SHA-256:
  `fe098ddd671c090586fe17d1d719e82edc3d4be8bc6b625234d78107b328d665`.

### Earlier hardened final source

The final source adds the separately named
`e058NoR5Counterexample` corollary and changes one redundant assumption query.
The first hardened pass completed the proof checks but failed while assembling
its JSON receipt because `kernel_receipt` had not been assigned. The failing
driver and transcript are retained.

After that receipt-only bug was fixed, the hardened run resumed after the
expensive core replay, revalidated all sources and objects, regenerated the
unit inventory, recompiled all coverage modules, reran all semantic and
assumption validations, and passed:

```text
E058-FRESH-LEAN-AUDIT-PASS cores=89 kernel_imports=89 semantic_closures=89 axiom_queries=192 warnings=0 forbidden_hits=0 receipt_sha256=7aa6cf6d38d3a38f1fa42867d15c1ebd48a8d6e191a35e69c37aff0fac6c0326
```

The receipt explicitly records `fresh_local_build=false` and
`resumed_after_core_replay=true`; it is not misrepresented as a second clean
start.

- Final audit-receipt SHA-256:
  `7aa6cf6d38d3a38f1fa42867d15c1ebd48a8d6e191a35e69c37aff0fac6c0326`.
- Final audit-runner SHA-256:
  `f2a504d3c9588cb14e9256cfed624fbcc46b10047d8e8fd9f2b8b4f1b76a6620`.
- Final-source inventory combined SHA-256:
  `6a14c6b7443e13d2a2769c013825beddee54e53d07c493e1306638d05cc1371d`.
- Final axiom-audit source SHA-256:
  `8aa0d752885442e44abfd3387e0a5a2f49210d91d9ee2d70efdf703aee27a218`.
- Final axiom-audit output SHA-256:
  `0f116384e742d753baff099152d7f46841f5305e1e8ab48b3018f505d3ba0a50`.
- Evidence-collection receipt SHA-256:
  `3a6613e93d4620d9a66b0fd1fe97405062d977d53a5aa335dff45afc05cd0a1b`.

The historical retained evidence collection contains 949 files including its
receipt and occupies 7,050,674 bytes before filesystem allocation. The later
exact-HEAD collection contains 935 files including its receipt; its 934 copied
files occupy 6,883,281 bytes before filesystem allocation.

## Trust and assumptions

Every queried final theorem depends only on a subset of:

```text
propext
Classical.choice
Quot.sound
```

There are no project axioms, `sorry`, `admit`, `unsafe` declarations,
`native_decide`, `ofReduceBool`, or unchecked solver-result assumptions in the
theorem chain. The execution/reproducibility boundary still includes Lean and
its kernel, the pinned source and certificate generators, the two proof
checkers, Python, the C compiler, the operating system, XZ/LZMA, and SHA-256.
The generated proof terms and semantic bridges are checked by Lean rather than
taking checker agreement as an axiom.

## Failed diagnostic benchmark

The preregistered branch-02 raw-versus-reduced performance benchmark did not
pass its fixed raw-import cap. The raw Lean import timed out after 300 seconds
with status 124. GNU `time` recorded:

- 310.08 user seconds;
- 7.57 system seconds;
- 5:19.34 elapsed including termination grace and cleanup; and
- 5,924,372 KiB maximum resident memory.

The reduced side was therefore not run, no successful benchmark receipt was
written, and no speedup ratio is claimed. The raw source, empty Lean output,
resource log, and exact driver diagnostic are retained. This is a failed
performance/reproducibility diagnostic, not a logical verification failure:
branch 02 is among the 89 cores dual-checked and accepted through the staged
Lean theorem audit.

## Reproduction

The complete commands, environment pins, hardware guidance, uninterrupted
exact-final replay, historical clean-start/resume qualification, benchmark
outcome, and release-overlay instructions are in `REPRODUCE_E058.md`. The
focused regression suite is:

```sh
make verify-e058-unit
```

It contains 25 tests. The final release-candidate package must also pass its
scoped SHA-256 ledger after extracting all three deterministic archive
overlays.

The self-contained preprint was clean-built twice to byte-identical 11-page
PDFs, with no final TeX warnings or overfull/underfull boxes. Every rendered
page was visually inspected. The PDF is 390,401 bytes and has SHA-256
`c248918bde85c9a0306c13e751b613760be88f02b9474b1565af8662a1d5a543`.

## Disclosure and review status

OpenAI Codex provided material assistance in planning, formalization,
certificate engineering, testing, audit design, documentation, and preprint
drafting. The exact disclosure is in `AI_USAGE.md`. AI output is not treated as
proof evidence; the machine-checkable artifacts and replay records are the
evidence.

This checkpoint has not received qualified independent human review. It must
not be described as `EXTERNALLY-VERIFIED-RESOLUTION`. No push, tag, remote
creation, or release is authorized until Ramazan completes the requested
cross-check and explicitly approves publication. The all-\(r\) conjecture
remains open.
