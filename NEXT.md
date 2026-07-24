# Next actions

## Terminal publication action

The fixed-\(r=5\) verification checkpoint is complete locally. E058 imports all
89 RUP-only special-Brooks cores into generated, staged Lean proofs, checks all
89 kernel imports and 89 semantic closures, compiles eight coverage modules,
and audits 192 theorem assumptions. The final source proves:

```lean
theorem e058Problem617AtFive : Problem617At 5
```

The exact terminal assumption set is `propext`, `Classical.choice`, and
`Quot.sound`. This supports `MACHINE-VERIFIED-RESOLUTION` for fixed \(r=5\)
only. The all-\(r\) conjecture remains `OPEN`; the pinned \(r=6,\ldots,9\)
claims remain provisional and unverified here; and the work has not received
independent external review.

The exact committed source at
`d19a0cf786a0fa714289830f276cf406408ab65b` passed one uninterrupted
no-local-build audit. Receipt SHA-256:
`789acb2bc829fcba0a5656fabca5a37d9d4fdd2b493858039ad0081cc37032d1`.
It records `fresh_local_build=true`, `resumed_after_core_replay=false`, zero
warnings, and zero forbidden hits.

Ramazan Kara completed the local cross-check and explicitly approved public
release on 24 July 2026. The approved target is
`RamazanKara/erdos-617-r5-formal-verification`; the approved project license is
Apache-2.0, matching the Lean source headers, and a root `LICENSE` is included.

The only remaining action in this terminal goal is to push the exact
license-bearing checkpoint, create the GitHub release titled
“Machine-verified fixed \(r=5\) case — partial result toward Erdős Problem
617.”, upload all five release files, and independently download and
hash-check them.

## Exact diagnostic caveat

The preregistered branch-02 raw-versus-reduced performance comparison did not
complete. The raw Lean import hit its fixed 300-second timeout (status 124),
using 310.08 user seconds, 7.57 system seconds, and 5,924,372 KiB maximum RSS.
The reduced comparison was therefore not run, and no speedup ratio is claimed.
This failed performance diagnostic is retained in the evidence and release
notes. It is not a premise of the theorem: the reduced branch-02 core is among
the 89 cores independently checked by both proof checkers and accepted through
the staged Lean import.

## Terminal boundary

Do not begin \(r\ge10\), all-\(r\), or additional fixed-case research under
this goal. The fixed-\(r=5\) release is the terminal deliverable. The
all-\(r\) conjecture remains open, and the pinned \(r=6,\ldots,9\) claims
remain provisional and unverified here.
