# E058 publication receipt

Recorded on 24 July 2026 after independent post-publication download
verification.

## Remote identity

- Repository:
  [RamazanKara/erdos-617-r5-formal-verification](https://github.com/RamazanKara/erdos-617-r5-formal-verification)
- Release:
  [Machine-verified fixed r=5 case — partial result toward Erdős Problem
  617.](https://github.com/RamazanKara/erdos-617-r5-formal-verification/releases/tag/e058-r5)
- Tag: `e058-r5`
- Target commit: `3d5c835a5845309f6e91babee367f005f30d1e77`
- Published at: `2026-07-24T13:51:19Z`
- State: public, non-draft, non-prerelease
- License: Apache-2.0

## Published assets

| Asset | Bytes | SHA-256 |
|---|---:|---|
| `SHA256SUMS` | 392 | `88d7e10ea78a2b270635ec1f4aa6e82be0c38d48d5dc680d8acdb0a1b96d45e0` |
| `erdos617-r5-source.tar.xz` | 749,908 | `5b56635df7a30b9fbee469ee5d732dadcf52ddf315fa568ea111b6b91f97c787` |
| `erdos617-r5-certificates.tar.xz` | 182,454,548 | `235ac33402eaedda5913254fbf0d15f8671f7d923c51a285be85e0a4595a34d7` |
| `erdos617-r5-audit-evidence.tar.xz` | 577,176 | `c85728b10281f9a9a9ab2dd6e05b1c440a813790020c2742f8a57de4ce0a78df` |
| `erdos617-r5-formal-verification.pdf` | 390,401 | `c248918bde85c9a0306c13e751b613760be88f02b9474b1565af8662a1d5a543` |

GitHub reported the same server-side SHA-256 digest and `uploaded` state for
each asset. The outer `SHA256SUMS` authenticates the four payloads; the hash
shown above authenticates the outer ledger itself.

## Independent post-publication checks

All five assets were downloaded from GitHub into a new empty directory.

- The downloaded names and byte sizes matched the table above.
- `sha256sum --check SHA256SUMS` passed.
- Every downloaded asset matched the twice-built local final byte-for-byte.
- The three archives extracted as a 2,830-file overlay with no symlinks,
  traversal paths, non-regular members, or nondeterministic ownership,
  timestamp, or mode metadata.
- The scoped 2,829-file inner SHA-256 ledger passed.
- A byte scan of the extracted overlay found none of the prohibited personal
  host-path prefixes.
- All 25 focused E058 tests passed from the downloaded source.

## Path-redaction boundary

The public snapshot replaces 10,901 personal host-path occurrences in 733
metadata/evidence files. It changes zero of the 51 pinned theorem sources,
zero of the 466 generated Lean sources, zero of the 182 certificate files, and
zero bytes of the preprint PDF. The public Git repository has a clean history
so the removed paths cannot survive in earlier commits. Exact interpretation
of raw versus public receipt hashes is documented in
`PUBLICATION_REDACTIONS.md`.

## Exact verification scope

The exported Lean theorem is:

```lean
Erdos617.e058Problem617AtFive : Problem617At 5
```

Its audited assumptions are exactly `propext`, `Classical.choice`, and
`Quot.sound`. This is a machine-verified result only for fixed \(r=5\).
The upstream \(r=6,\ldots,9\) claims are not verified by this release, the
all-\(r\) conjecture remains open, and independent expert review has not yet
been completed.

The original mathematical proof is credited to Robert Sneiderman. This
project's contribution is independent formal and certificate verification.
Material OpenAI Codex assistance is disclosed in `AI_USAGE.md` and in the
preprint; AI-generated assertions are not treated as mathematical evidence.

Anthropic's Claude (via Claude Code) also performed a consistency review and
produced the wording-only revision described below after the release staging
snapshot was frozen. Claude's statements are not mathematical evidence or
independent human review.

## Post-publication preprint revision (2026-07-24)

The `main` branch now carries the post-release prose revision of the
preprint: wording-only changes to `paper/main.tex`, two bibliography entry
types corrected in `paper/references.bib`, and no mathematical, numerical,
attribution, or scope change. The revised PDF is 390,512 bytes with SHA-256
`fbcd4e1b8b9fd94f91b387f417cb5a2418ee5e8e826ffc2ddb501a02b7ca0743`, rebuilt
twice to byte-identical output from the committed source of this branch.
`paper/README.md` records the revised build, the E058 result record carries
a dated addendum, and `AI_USAGE.md` now discloses the second AI system
involved in the revision. The `e058-r5` release tag and its five published
assets remain the frozen originals described above and are intentionally
unchanged.
