# Reproducing the fixed-\(r=5\) verification

This guide covers E058 only: the machine verification of
`Erdos617.e058Problem617AtFive : Problem617At 5`. It does not verify the
claimed fixed cases \(r=6,\ldots,9\), and it does not resolve the all-\(r\)
Erdős Problem 617 conjecture.

## Release assets

The release consists of four payloads plus an outer
`SHA256SUMS`:

- `erdos617-r5-source.tar.xz`;
- `erdos617-r5-certificates.tar.xz`;
- `erdos617-r5-audit-evidence.tar.xz`; and
- `erdos617-r5-formal-verification.pdf`.

Verify the downloaded payloads before extracting them:

```sh
sha256sum --check SHA256SUMS
```

The three archives are deterministic overlays with one common top-level
directory. Extract all three in the same empty directory:

```sh
tar -xJf erdos617-r5-source.tar.xz
tar -xJf erdos617-r5-certificates.tar.xz
tar -xJf erdos617-r5-audit-evidence.tar.xz
cd erdos617-r5-formal-verification
sha256sum --check \
  artifacts/e058_special_brooks_kernel_bridge/SHA256SUMS
```

The published JSON receipts and logs are path-redacted review views. Embedded
hashes in those views continue to identify raw audit products; the outer and
scoped `SHA256SUMS` files authenticate the published redacted bytes. The
theorem sources and certificate files were not altered. Read
`PUBLICATION_REDACTIONS.md` before interpreting retained receipt hashes or
comparing a fresh replay's machine-local paths.

The assets are built by:

```sh
python3 repro/build_e058_release_assets.py \
  --repository "$PWD" \
  --output-directory /absolute/path/to/empty/output
```

Two runs into separate empty output directories must give identical hashes.

## Pinned environment

The Lean package pins:

- Lean `leanprover/lean4:v4.32.0`, commit
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`;
- mathlib commit
  `81a5d257c8e410db227a6665ed08f64fea08e997`; and
- the package graph in `formal/lean/lake-manifest.json`.

The recorded audit ran on x86-64 Linux under WSL2 with Python 3.12.3, GCC
13.3.0, and XZ Utils 5.4.5. It used an AMD Ryzen 7 5800X3D exposed as eight
logical CPUs. The largest individual Lean stages used roughly 5--6 GiB
resident memory; a semantic closure can approach 8 GiB. The successful
machine had 11 GiB RAM plus 3 GiB swap. Allow at least 15 GiB free disk space;
16 GiB RAM is recommended.

Install the pinned Lean toolchain with Elan, populate the dependencies from
the committed manifest, and compile the small independent C checker:

```sh
elan toolchain install leanprover/lean4:v4.32.0
cd formal/lean
lake update
cd ../..
make build/lrat-check-upstream
```

The audit rejects a changed mathlib revision even if dependency resolution
succeeds.

## Fast parser and generator tests

Run the 25 E058 unit tests:

```sh
make verify-e058-unit
```

These cover backward RUP slicing and corruption rejection, staged proof
splitting and generated-source replay, cached semantic-receipt and object
tampering rejection, and the finite neighborhood-orbit certificate generator.
They also validate the strict parser and proof-only source renderer for the
preregistered branch-02 benchmark.

## Preregistered branch-02 benchmark

After the base Lean dependencies have been built, reproduce the exact raw
versus reduced proof-only comparison:

```sh
python3 repro/run_e058_branch02_benchmark.py \
  --project "$PWD" \
  --lake "$E058_LAKE" \
  --output-directory /absolute/path/to/empty/benchmark-output
```

Each import is limited to 300 seconds and Lean's 8192 MiB memory setting. The
driver checks the measured resident-memory maximum against the same limit,
regenerates the backward core, requires the exact pinned source, proof, map,
deletion count, and final-clause hashes, pins the same Lean commit, mathlib
revision, and complete Lake manifest as the theorem audit, and accepts only
the axiom set `{propext}`.

The recorded final-machine attempt did **not** pass this diagnostic benchmark.
The raw import reached timeout exit status 124. GNU `time` recorded 310.08
user seconds, 7.57 system seconds, 5:19.34 elapsed including termination
grace and cleanup, and 5,924,372 KiB maximum resident memory. The exact raw
source, empty Lean output, resource log, and driver diagnostic are retained
under `artifacts/e058_special_brooks_kernel_bridge/fresh_audit/transcripts/`.
Because the raw side timed out, the runner did not execute the reduced side
and wrote no successful comparison receipt; no speedup ratio is claimed.

This performance outcome is not a premise of
`Erdos617.e058Problem617AtFive`. The reduced branch-02 core is among the 89
cores independently regenerated, dual-checked, staged, and accepted by Lean
in both successful theorem audits. A future benchmark rerun must use an empty
output directory and must not be reported as passing unless the runner exits
zero and writes its complete receipt.

## Complete clean audit

Run the proof in a source tree whose local Lean build directory does not
exist. A release extraction is already suitable before its first build.
Confirm the condition and record the exact Lake executable:

```sh
test ! -e formal/lean/.lake/build
E058_LAKE="$(elan which lake)"
test -x "$E058_LAKE"
```

Then run:

```sh
python3 repro/run_e058_special_brooks_kernel_audit.py \
  --project "$PWD" \
  --lake "$E058_LAKE" \
  --log "$PWD/e058-fresh-audit.log" \
  --require-no-local-build
```

The recorded exact-final-source run used this command without interruption.
It started from exact commit
`d19a0cf786a0fa714289830f276cf406408ab65b`, after the C checker had been
compiled but while `formal/lean/.lake/build` was absent. It completed in
25,497.97 seconds and records `fresh_local_build=true` and
`resumed_after_core_replay=false`.

The earlier release-candidate evidence is also retained. Its clean-start
source already contained `e058Problem617AtFive`; a later final source added
the separately named `e058NoR5Counterexample` corollary and changed one
redundant assumption query. That historical run began under the no-build gate
but used post-core resume segments. Its unaltered legacy runner, transcript,
and raw receipt are tied together by
`repro/validate_e058_clean_start_sequence.py`. The hardened resume embeds that
sequence receipt and explicitly reports `fresh_local_build=false`. A hardened
resume accepts only the complete `CLEAN-START-SEQUENCE-PROVENANCE` wrapper; a
bare audit-receipt JSON is deliberately insufficient. These historical
qualifications are preserved even though the later exact-HEAD run now supplies
the simpler uninterrupted evidence.

This deliberately long command:

1. verifies the Lean/mathlib pins and regenerates three transparent orbit
   certificates byte-for-byte;
2. builds the non-certificate graph theory;
3. regenerates all 89 backward RUP cores;
4. checks every core with the C and Python checkers and makes both reject a
   truncated proof and a forged empty clause (four negative outcomes per
   core);
5. re-splits every reduced LRAT, regenerates every staged Lean source
   byte-for-byte, and imports all 89 theorems into the Lean kernel;
6. proves all 89 graph-semantic closure theorems;
7. compiles eight exhaustive coverage modules;
8. queries 192 theorem assumption sets; and
9. repeats source-safety, warning, and before/after source-hash checks.

The only successful terminal marker is:

```text
E058-FRESH-LEAN-AUDIT-PASS cores=89 kernel_imports=89 semantic_closures=89 axiom_queries=192 warnings=0 forbidden_hits=0
```

The marker continues with the SHA-256 of
`formal/lean/.e058-audit/fresh-audit-receipt.json`. The receipt is authoritative
only if the process exits with status zero. The final declaration's assumption
set must be exactly:

```text
propext
Classical.choice
Quot.sound
```

Any `sorryAx`, project-defined axiom, warning, forbidden source construct,
missing branch, failed corruption rejection, checker disagreement, changed
hash, or nonzero exit invalidates promotion.

For exact commit `d19a0cf`, the successful receipt SHA-256 is
`789acb2bc829fcba0a5656fabca5a37d9d4fdd2b493858039ad0081cc37032d1`.
The audit and driver transcripts are byte-identical with SHA-256
`52f10416d02808c606bcffff53871f0a9c37c0ab15606235f00f33031b97fb2a`.
The collected exact-run evidence is under
`artifacts/e058_special_brooks_kernel_bridge/exact_head_fresh_audit/`; its
collection receipt SHA-256 is
`2f9a1d9e4027998eb3405a2db92f2130886f4eac7fd3137c4db36325eee7c047`.
`ATTEMPTS.md` there distinguishes the successful run from two retained
infrastructure failures that produced no terminal receipt.

## Rebuilding the preprint

The PDF build has a fixed `SOURCE_DATE_EPOCH`. From `paper/`:

```sh
make clean all
sha256sum erdos617-r5-formal-verification.pdf
make clean all
sha256sum erdos617-r5-formal-verification.pdf
```

The two PDF hashes must be identical. Rendering all pages with Poppler is the
layout check:

```sh
mkdir -p /tmp/erdos617-r5-paper
pdftoppm -png -r 120 \
  erdos617-r5-formal-verification.pdf \
  /tmp/erdos617-r5-paper/page
```

The preprint and `AI_USAGE.md` disclose material assistance by OpenAI Codex.
AI-generated assertions are not part of the proof evidence.
