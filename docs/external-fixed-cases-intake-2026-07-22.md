# Intake: external fixed-case claims through `r = 9`

Accessed: 2026-07-22 (Europe/Berlin)

Repository: `https://github.com/Robby955/erdos-617-fixed-cases`

Pinned commit: `735c2eeffcb5c8abe92f8a6be04be2fa3c8bb6ab`

The user-supplied repository is the same immutable commit already pinned for
the E033 `r=5` manuscript audit.  Its current top-level claims are the five
fixed cases `r=5,6,7,8,9`; it explicitly says these do not settle the
all-`r` conjecture and that none has completed external mathematical review.

The evidence types differ:

- `r=5,6`: human mathematical manuscripts; program output is stated not to be
  a proof premise;
- `r=7`: direct labeled enumeration plus a separate Sage/nauty reconstruction;
- `r=8`: a human reduction with one endpoint and 861 core-shell LRAT
  refutations;
- `r=9`: a human reduction with solver-free order-26 classifications and 50
  order-27 LRAT refutations distributed in four release assets.

This intake independently cloned the commit, checked its Git object database,
and checked the top-level, `r7-r8`, and `r9` in-repository SHA-256 manifests
from their intended directories.  Those integrity checks pass.  They establish
only that the checked Git files match the repository's own manifests.

The integrity portion is reproducible with a fresh clone:

```sh
git clone https://github.com/Robby955/erdos-617-fixed-cases.git repo
git -C repo checkout 735c2eeffcb5c8abe92f8a6be04be2fa3c8bb6ab
git -C repo fsck --full
(cd repo && sha256sum -c SHA256SUMS)
(cd repo/r7-r8 && sha256sum -c SHA256SUMS)
(cd repo/r9 && sha256sum -c SHA256SUMS)
```

No `r=6` proof reconstruction, `r=7` enumeration replay, `r=8` LRAT replay, or
`r=9` release/proof replay was completed in this intake.  The four external
`r=9` release archives (about 776 MB compressed in total) were not downloaded,
so their hashes and 50 LRATs have not been independently checked here.  The
human implication chains and imported extremal theorems also remain unaudited
for `r=6,7,8,9`.

Accordingly, E033's independently audited fixed-`r=5` claim remains a
`CANDIDATE-RESOLUTION`; the external `r=6`--`r=9` statements remain unverified
proof claims in this project.  Even successful independent verification of all
five fixed cases would not prove the assertion for arbitrary `r`.
