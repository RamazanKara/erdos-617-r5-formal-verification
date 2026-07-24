# E058 release and publication record

Ramazan Kara cross-checked the local checkpoint and explicitly approved public
release on 24 July 2026. The approved target is
`RamazanKara/erdos-617-r5-formal-verification` under Apache-2.0.

## Local verification gates

- [x] Complete the fresh local-build-free E058 audit.
- [x] Complete one uninterrupted no-local-build replay of the exact committed
      final source. Receipt:
      `789acb2bc829fcba0a5656fabca5a37d9d4fdd2b493858039ad0081cc37032d1`;
      `fresh_local_build=true`; `resumed_after_core_replay=false`.
- [x] Preserve and validate the exact clean-start transcript, legacy runner,
      completed receipt, and every later resume segment.
- [x] Preserve and label both unsuccessful exact-source infrastructure
      attempts; neither produced a terminal receipt or is counted as proof
      evidence.
- [x] Confirm all 89 reduced cores with both external checkers and all 356
      deliberate corruption rejections.
- [x] Confirm 89 Lean kernel LRAT imports, 89 graph-semantic closures, eight
      coverage modules, and 192 theorem-assumption queries.
- [x] Re-split every reduced LRAT and regenerate every committed staged Lean
      source byte-for-byte before accepting a completed receipt.
- [x] Confirm the final declaration is
      `Erdos617.e058Problem617AtFive : Problem617At 5`.
- [x] Confirm its assumptions are exactly `propext`, `Classical.choice`, and
      `Quot.sound`, with no `sorryAx` or project-defined axiom.
- [x] Confirm the source-safety scan, source before/after hashes, and complete
      artifact inventory.
- [x] Execute and retain the preregistered E038 branch-02 raw/core proof-only
      benchmark attempt, executed Lean source, resource log, and toolchain
      record. Exact outcome: **FAILED diagnostic performance cap**; raw timed
      out at 300 seconds, the reduced side was not run, and no speedup is
      claimed. This is not a theorem premise.
- [x] Run all 25 E058 unit tests, including generated-source tampering
      rejection.
- [x] Rebuild the preprint twice with identical PDF bytes and visually inspect
      every rendered page.
- [x] Build the four local release payloads twice with identical hashes,
      extract the three archive overlays into an empty directory, verify the
      scoped hash inventory, and rerun the 25 E058 unit tests there.
- [x] Commit the complete local checkpoint while excluding the user-owned
      `formal/lean/Check.lean`.

## Attribution and scope gates

- [x] Credit the original fixed-\(r=5\) mathematical proof to Robert
      Sneiderman and pin upstream commit
      `735c2eeffcb5c8abe92f8a6be04be2fa3c8bb6ab`.
- [x] Describe this project as an independent formal and certificate
      verification, not as authorship of the original proof.
- [x] Disclose material use of OpenAI Codex.
- [x] State prominently that only fixed \(r=5\) is claimed, that fixed
      \(r=6,\ldots,9\) is unverified here, and that the all-\(r\) conjecture
      remains open.
- [x] State that independent expert review has not yet been completed.

## Remote publication gate

- [x] Ramazan Kara has inspected the committed local checkpoint and explicitly
      approved publication.
- [x] Ramazan Kara has confirmed the public repository
      `RamazanKara/erdos-617-r5-formal-verification` and Apache-2.0 license; a
      project-level `LICENSE` is included.
- [ ] Only after that approval: create or select the GitHub repository, push
      the reviewed snapshot, create the release, upload the source,
      certificates, audit evidence, preprint, and hash inventory, then
      independently download and hash-check every release asset.

The remaining unchecked item is executed from the exact license-bearing
checkpoint; it is not a mathematical verification premise.
