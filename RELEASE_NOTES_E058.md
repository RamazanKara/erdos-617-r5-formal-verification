# Release notes

## Machine-verified fixed \(r=5\) case — partial result toward Erdős Problem 617

This release contains an independent formal and certificate verification of
the fixed-\(r=5\) case of Erdős Problem 617:

> Every five-coloring of the edges of \(K_{26}\) has a six-vertex set on which
> at least one color is absent.

The exported Lean declaration is:

```lean
Erdos617.e058Problem617AtFive : Problem617At 5
```

The original mathematical proof is due to Robert Sneiderman, in
[The five-color case of an Erdős–Gyárfás balanced-coloring
problem](https://github.com/Robby955/erdos-617-fixed-cases/tree/735c2eeffcb5c8abe92f8a6be04be2fa3c8bb6ab),
pinned at commit `735c2eeffcb5c8abe92f8a6be04be2fa3c8bb6ab`. This project's contribution is an
independent formal and certificate verification of that fixed-case proof. It
does not claim authorship of Sneiderman's argument or independent external
review of the formalization.

### Verification record

The fresh E058 audit checks:

- 89 deterministically regenerated backward RUP cores;
- 89 checks with the pinned C LRAT checker and 89 checks with an independent
  Python checker;
- 356 deliberate corruption rejections;
- 89 staged LRAT imports accepted by the Lean kernel;
- 89 Lean graph-semantic closure theorems;
- eight exhaustive symmetry and branch-coverage modules; and
- 192 theorem-assumption queries.

The final theorem depends exactly on `propext`, `Classical.choice`, and
`Quot.sound`. The audit reports no `sorryAx`, project-defined axiom, warning,
or forbidden source construct.

The exact committed final source at
`d19a0cf786a0fa714289830f276cf406408ab65b` passed one uninterrupted
no-local-build replay. Its receipt SHA-256 is
`789acb2bc829fcba0a5656fabca5a37d9d4fdd2b493858039ad0081cc37032d1`;
it records `fresh_local_build=true`, `resumed_after_core_replay=false`, and a
25,497.97-second run. The earlier clean-start/resume and hardened-final
evidence remains included with its original qualifications.

### Diagnostic benchmark outcome

The separately preregistered branch-02 raw-versus-reduced proof-only benchmark
did not pass its fixed raw-import cap. The raw Lean import timed out at 300
seconds with status 124. GNU `time` recorded 310.08 user seconds, 7.57 system
seconds, 5:19.34 elapsed including termination grace and cleanup, and
5,924,372 KiB maximum resident memory. The reduced side was not run, no
successful benchmark receipt was produced, and no speedup ratio is claimed.
The executed source, resource log, empty Lean output, and driver diagnostic
are included in the audit evidence.

This failed performance diagnostic is not a premise of the theorem. The same
branch-02 reduced core is among the 89 cores regenerated, independently
accepted by both proof checkers, staged, and accepted by the Lean kernel.

### AI-assistance disclosure

OpenAI Codex materially assisted with Lean and Python drafting, verification
automation, documentation, LaTeX, and execution of the audit workflow. Codex
is not an author, and its textual assertions are not mathematical evidence.
Ramazan Kara directed the project and decides whether any material is
published; he assumes responsibility for any
approved release. See `AI_USAGE.md` and the preprint's dedicated disclosure
section.

### Publication path redactions

The public snapshot mechanically removes personal host-path prefixes from 716
JSON receipts, 15 logs, and two source-metadata files. It uses a clean Git
history so those paths cannot survive in earlier commits. The 51 pinned
theorem sources, 466 generated Lean sources, all 182 certificate files, replay
programs, and preprint PDF are byte-for-byte unchanged.

Embedded hashes in path-redacted receipt views continue to describe the raw
audit products. The release-level and scoped `SHA256SUMS` files authenticate
every published byte after redaction. See `PUBLICATION_REDACTIONS.md` for the
exact trust boundary and reproduction implications.

### Exact scope

This is a machine-verified resolution only of fixed \(r=5\). The claimed
fixed cases \(r=6,\ldots,9\) in the upstream repository are not verified by
this release. The all-\(r\) Erdős Problem 617 conjecture remains open.
Independent expert review of this formalization and preprint has not yet been
completed.

### Assets and reproduction

The release provides deterministic source, certificate, and audit-evidence
archives, the rendered preprint, and SHA-256 hashes for every payload.
`REPRODUCE_E058.md` gives the complete clean replay procedure and resource
envelope.

Ramazan Kara cross-checked the committed checkpoint and approved public
release on 24 July 2026. The publication target is
`RamazanKara/erdos-617-r5-formal-verification`, licensed under Apache-2.0.
