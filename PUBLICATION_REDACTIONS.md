# Publication path redactions

This public snapshot removes personal host-path prefixes from retained
execution records. The redaction is publication-only and does not change the
mathematical result.

The mechanical pass replaced three private path prefixes with the public
tokens `/PUBLICATION_REDACTED_HOME`,
`/PUBLICATION_REDACTED_WINDOWS_HOME`, and
`C:/PUBLICATION_REDACTED_WINDOWS_HOME`. It replaced 10,901 occurrences in 733
files:

- two source-bundle metadata files (`STATE.md` and
  `artifacts/source_hashes.json`);
- zero files in the certificate bundle; and
- 716 JSON receipts and 15 logs in the audit-evidence bundle.

The 51 pinned theorem sources, 466 generated Lean sources, all 182 certificate
files, replay programs, and preprint PDF are byte-for-byte unchanged by this
redaction.

The path-redacted JSON receipts and logs are public review views of the raw
execution records. Embedded hashes inside those views continue to describe the
raw audit products and therefore are not, in general, hashes of the redacted
views themselves. The raw originals remain in the private verification
workspace and are not published. The original uninterrupted audit receipt is
identified by SHA-256
`789acb2bc829fcba0a5656fabca5a37d9d4fdd2b493858039ad0081cc37032d1`.

The release-level `SHA256SUMS` and the scoped
`artifacts/e058_special_brooks_kernel_bridge/SHA256SUMS` authenticate every
published byte after redaction. A verifier can regenerate new raw receipts and
logs, with paths appropriate to the verifier's own machine, by following
`REPRODUCE_E058.md`.

The public Git repository is intentionally a clean-history publication
snapshot so private paths cannot survive in earlier commits. The verification
lineage commit identifiers in the documentation remain provenance identifiers;
the per-file hashes and release ledgers bind the published source bytes.
