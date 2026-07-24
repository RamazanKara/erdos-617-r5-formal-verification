# Claim ledger

Overall project level: `MACHINE-VERIFIED-RESOLUTION` for fixed \(r=5\), and
`PARTIAL-CERTIFIED`/`OPEN` for the unrestricted all-\(r\) conjecture. A claim's
evidence class is one of `speculation`, `experimental evidence`, `proved
lemma`, `machine-certified theorem`, or `externally reviewed theorem`. No entry
below resolves the all-\(r\) conjecture. The fixed \(r=6,\ldots,9\) claims in
the pinned upstream repository remain provisional and unverified here.

Entries through `C-FORMAL-012` preserve the verification label and caveats at
their own checkpoint. Present-tense phrases such as “remains
`CANDIDATE-RESOLUTION`” in those historical entries are superseded for fixed
\(r=5\) by `C-FORMAL-013` and `C-R5-002`; they are not superseded for the
all-\(r\) conjecture.

## C-LIT-001 — current recorded frontier

- Statement/scope: sources checked through 2026-07-22 still present the all-\(r\)
  conjecture as open. The newly supplied repository at commit
  `735c2eeffcb5c8abe92f8a6be04be2fa3c8bb6ab` claims the five fixed cases
  `r=5,6,7,8,9`, explicitly not arbitrary `r`; all are labeled unreviewed by
  that repository.
- Evidence class: `experimental evidence` (literature search, never a proof of
  nonexistence of other literature).
- Dependencies/location: `docs/literature.md` and
  `docs/external-fixed-cases-intake-2026-07-22.md`.
- Verifiers/hashes: primary PDF SHA-256 recorded in
  `artifacts/source_hashes.json`.
- Caveat/falsifier: an overlooked or later publication can falsify this status.

## C-SPEC-001 — exact finite semantics

- Statement/scope: a coloring file of scope \((n,r,k)\) is valid exactly when it
  assigns one color in \([0,r)\) to every unordered pair and every \(k\)-set
  contains every color. At \((26,5,6)\) this is exactly the negation of the
  \(r=5\) conjecture.
- Evidence class: `proved lemma`.
- Dependencies/location: `docs/problem-spec.md`, `src/check_coloring.py`,
  `src/check_coloring.c`.
- Verifiers: line-by-line human correspondence proof plus two implementations.
- Caveat/falsifier: an indexing, parsing, subset-enumeration, or quantifier mismatch.

## C-RED-001 — color graph equivalence

- Statement/scope: for a balanced \(r=5\) coloring, every color graph \(G_c\)
  has \(\alpha(G_c)\le5\), equivalently \(H_c=\overline{G_c}\) is \(K_6\)-free.
- Evidence class: `proved lemma`.
- Dependencies/location: `docs/theory-notes.md` §1.
- Falsifier: a six-set missing color \(c\), exactly the forbidden witness.

## C-RED-002 — simultaneous complements and deficits

- Statement/scope: every edge belongs to exactly four \(H_c\),
  \(\sum_c e(H_c)=1300\), \(H_i\cup H_j=K_{26}\), each
  \(e(H_c)\le270\), and with \(q_c=270-e(H_c)\) one has
  \(q_c\ge0\) and \(\sum_cq_c=50\).
- Evidence class: `proved lemma`.
- Dependencies/location: `C-RED-001`, Turán's theorem,
  `docs/theory-notes.md` §1.
- Falsifier: an edge-coverage or Turán arithmetic counterexample.

## C-RED-003 — chromatic product and deficit consequence

- Statement/scope: if \(H_i,H_j\) have proper colorings with \(a,b\) colors,
  then \(ab\ge26\); hence at most one \(H_c\) is 5-colorable. Using the
  Kang–Pikhurko theorem, every non-5-colorable \(H_c\) has at most 266 edges,
  so at least four deficits satisfy \(q_c\ge4\).
- Evidence class: product claim `proved lemma`; 266 bound
  `externally reviewed theorem` with hypotheses checked.
- Dependencies/location: `docs/theory-notes.md` §§1–2; Kang–Pikhurko (2005),
  Theorem 1 with \((n,r)=(26,5)\).
- Caveat: this uses only 16 of the total deficit 50 and is not close to a
  contradiction. The imported theorem is not locally formalized.

## C-R3-001 — published \(r=3\) case

- Statement/scope: every three-coloring of \(K_{10}\) has a four-set missing
  a color.
- Evidence class: `proved lemma` (published proof independently reconstructed).
- Dependencies/location: Brooks' theorem, \(R(3,3)=6\),
  `docs/theory-notes.md` §5.
- Verifier: human line-by-line audit; no kernel-checked formalization.
- Falsifier: an error in the two standard imported theorems or the recorded cases.

## C-R4-001 — published \(r=4\) case

- Statement/scope: every four-coloring of \(K_{17}\) has a five-set missing
  a color.
- Evidence class: `externally reviewed theorem`; local reproduction remains open.
- Dependencies/location: Erdős–Gyárfás (1999), Lemma 2;
  `docs/theory-notes.md` §6.
- Caveat: the final 34-versus-35 edge-count subcase and the uniqueness of the
  \((3,4)\)-Ramsey graph on eight vertices have not yet been independently
  certified. Do not use this entry as locally reproduced proof.

## C-AFF-001 — affine \(K_{25}\) coloring

- Statement/scope: the exact artifact `artifacts/affine25.col` is a five-coloring
  of \(K_{25}\) in which every six-set sees all five colors.
- Evidence class: `machine-certified theorem` for this finite artifact;
  project level `PARTIAL-CERTIFIED`.
- Dependencies/location: `src/generate_affine25.py`, both semantic checkers,
  `docs/theory-notes.md` §3.
- Verifiers: Python and C independently checked all 177,100 six-sets; generator
  reproduction and corruption tests pass.
- Hash: `05d15bb71af3788b17c172bcdf794aa528e9f4c753904056949a616ad2dac43a`.
- Caveat/falsifier: scope is 25 vertices, not 26; a checker/spec mismatch or hash
  mismatch would invalidate certification.

## C-AFF-002 — exact affine nonextension

- Statement/scope: `C-AFF-001` cannot be extended to a balanced coloring of
  \(K_{26}\) by assigning colors to edges from one new vertex while leaving
  all old edges fixed.
- Evidence class: `proved lemma`, restricted to the exact affine artifact.
- Dependencies/location: `docs/theory-notes.md` §4,
  `src/verify_affine_nonextension.py`,
  `artifacts/affine_nonextension.json`.
- Verifier/hash: finite premises checked; JSON SHA-256
  `81ddd52a353ea1c5fd6515256d741eb8e52ab4dab360fb8d0bd0ef6ab3ac6aac`.
- Caveat: says nothing about other \(K_{25}\) colorings or unrestricted \(K_{26}\).
- Falsifier: an extension coloring, or failure of either partition premise.

## C-TRI-001 — unrestricted local Turán/triangle constraint

- Statement/scope: in any balanced five-coloring of \(K_{26}\), for every
  vertex \(v\), with color degrees \(d_c(v)\), define
  \(g(m)=\binom m2-t_4(m)\) and
  \(\delta(v)=\sum_c g(25-d_c(v))-200\). Then \(\delta(v)\ge0\), with
  equality exactly at degree profile \((5,5,5,5,5)\). If \(M,B,R\) are the
  numbers of monochromatic, exactly-two-color, and rainbow triangles, and
  \(\Delta=\sum_v\delta(v)\), then
  \[B+3R\ge5200+\Delta,\qquad 2R-M\ge2600+\Delta.\]
  Writing \(E=\frac12\sum_{v,c}(d_c(v)-5)^2\), one also has the exact identity
  \(R-2M=1300-E\), hence the necessary condition
  \[3M\ge 2E+\Delta.\]
- Evidence class: `proved lemma` with exhaustive finite arithmetic audit.
- Dependencies/location: Turán's theorem for \(K_5\), elementary triangle
  double counting, `docs/theory-notes.md` §7,
  `src/verify_triangle_bound.py`.
- Verifier/hash: all 23,751 ordered degree profiles checked; JSON SHA-256
  `bf739b59eda70c522274611b35d9ca464c6a14e1ca4faa6a0b594f95f381a4e4`.
- Caveat: necessary but not yet contradictory; the script audits arithmetic,
  while the theorem-to-arithmetic reduction is a human proof.
- Strengthening: `C-EQ-001`, `C-LOC-002`, and `C-EQ-002` successively improve
  the local and global bounds.
- Falsifier: a balanced coloring violating any displayed inequality, or an error
  in the Turán/equality argument.

## C-EQ-001 — certified exclusion of local equality

- Statement/scope: in any balanced five-coloring of \(K_{26}\), the local count
  `L(v)` from `C-TRI-001` is never 200 and hence is at least 201 at every
  vertex. More precisely, let \(Z=|\{v:\delta(v)=0\}|\). Then
  \[
  B+3R\ge5200+\Delta+Z\ge5226,
  \quad 2R-M\ge2600+\Delta+Z\ge2626,
  \]
  and, using the exact identity in `C-TRI-001`,
  \[
  3M\ge2E+\Delta+Z\ge2E+26.
  \]
- Evidence class: finite incidence obstruction `machine-certified theorem`;
  mathematical reduction and symmetry completeness `proved lemma`. Overall
  project level remains `PARTIAL-CERTIFIED`.
- Dependencies/location: Turán equality in `C-TRI-001`, the block-system bridge
  and encoding proof in `docs/theory-notes.md` §8,
  `src/generate_local_equality_cnf.py`, and
  `certificates/local_equality.lrat`.
- Verifiers: exact CNF regeneration; pinned upstream `lrat-check.c` at drat-trim
  commit `2e5e29cb0019d5cfd547d4208dca1b3ec290349f`; independent RUP-only
  `src/check_lrat.py`; two corrupted-certificate cases rejected by each checker.
- Hashes: CNF
  `5d07eba75a940fc84632fccb79abbf05caa56a786d245f40d814188926b6b22b`;
  LRAT
  `0e29cf03c74f1a47e90dad423bfe851c399a6d718a431cf00ebbc4372e4f033c`.
- Caveat: the 400-variable CNF represents only necessary local conditions for
  equality. Its UNSAT certificate excludes equality but does not decide whether
  a balanced \(K_{26}\) coloring exists. There is no proof-assistant kernel in
  the bridge or checker chain.
- Falsifier: a valid equality configuration, a satisfying assignment of the
  committed CNF, an unsound symmetry break, a checker failure, or a hash mismatch.

## C-LOC-002 — non-four-partite local color and bound 204

- Statement/scope: at every vertex of a hypothetical balanced five-coloring of
  \(K_{26}\), at least one of the five \(K_5\)-free local complements
  \(H_c[B_c]\) is non-four-partite, and every complement of order at least 21
  is non-four-partite. Applying the Kang--Pikhurko penalty to every such color
  gives \(L(v)\ge204\). Equality in this strengthened arithmetic is uniquely
  \((5,5,5,5,5)\); the next value 205 has sorted profile
  \((4,5,5,5,6)\). Consequently
  \[
  B+3R\ge5304,\qquad2R-M\ge2704,\qquad3M\ge2E+104.
  \]
- Evidence class: four-partite exclusion `proved lemma` using the certified
  incidence obstruction `C-EQ-001`; numerical extremal bound
  `externally reviewed theorem`; profile enumeration independently audited.
- Dependencies/location: `docs/theory-notes.md` §9, Kang--Pikhurko (2005)
  Theorems 1 and 4, `src/verify_triangle_bound.py`, and
  `artifacts/triangle_bound.json`.
- Verifier/hash: all 23,751 ordered profiles checked; minimum 204 with one
  ordered minimizer, next value 205 with 20 ordered profiles, and following
  value 206 with 50 ordered profiles of two sorted types. JSON SHA-256
  `bf739b59eda70c522274611b35d9ca464c6a14e1ca4faa6a0b594f95f381a4e4`.
- Caveat/falsifier: the Kang--Pikhurko proof is imported rather than locally
  formalized. A four-partite configuration evading the `C-EQ-001` bridge, a
  theorem-hypothesis error, or an arithmetic mismatch falsifies the claim.

## C-EQ-002 — certified exclusion of local count 204

- Statement/scope: the unique equality profile from `C-LOC-002` cannot occur.
  Therefore every vertex satisfies \(L(v)\ge205\), and every hypothetical
  balanced coloring obeys
  \[
  B+3R\ge5330,\qquad2R-M\ge2730,\qquad3M\ge2E+130.
  \]
- Evidence class: six relevant balanced finite incidence obstructions
  `machine-certified theorem`; equality classification, necessary-system
  bridge, and symmetry completeness `proved lemma`, conditional on the imported
  extremal characterization. E006 also certifies two now-superseded order-19
  systems from the former weaker arithmetic catalog. Overall project level
  remains `PARTIAL-CERTIFIED`.
- Dependencies/location: `C-LOC-002`; Kang--Pikhurko Theorem 4 and Lemma 5;
  `docs/theory-notes.md` §10; `src/generate_local_204_cnf.py`;
  `artifacts/local_204/`; and `certificates/local_204/`.
- Verifiers: independent reconstruction of the complete eight-case catalog;
  exhaustive truth-table tests of custom CNF primitives; byte-exact CNF
  regeneration; pinned upstream C LRAT checker; independent streaming Python
  RUP checker; four deliberate corrupted-proof rejections.
- Hashes: all sixteen CNF/certificate hashes and all eight decompressed-proof
  hashes are recorded in `experiments/E006-local-204-result.md` and protected by
  `artifacts/SHA256SUMS`.
- Caveat: each CNF is a weaker necessary local incidence system, not the full
  \(K_{26}\) coloring formula. The result rules out local count 204 but does not
  resolve the unrestricted coloring problem. There is no proof-assistant kernel.
- Falsifier: an omitted extremal isomorphism type, a valid equality
  configuration eliminated by a symmetry clause, a satisfying assignment, a
  checker/certificate failure, or a content-hash mismatch.

## C-LOC-003 — certified exclusion of local count 205

- Statement/scope: every vertex of a hypothetical balanced five-coloring of
  \(K_{26}\) satisfies \(L(v)\ge206\). Consequently
  \[
  B+3R\ge5356,\qquad2R-M\ge2756,\qquad3M\ge2E+156.
  \]
  This is an unrestricted necessary local theorem, not a decision of the full
  \(K_{26}\) coloring instance.
- Evidence class: 8 E008 and 1 E009 finite incidence obstructions
  `machine-certified theorem`; arithmetic classification, E006/E009 embedding
  split, necessary-system bridges, and symmetry completeness `proved lemma`,
  conditional on the imported Kang--Pikhurko extremal theorem. Overall project
  level remains `PARTIAL-CERTIFIED`.
- Dependencies/location: `C-LOC-002`, `C-EQ-002`; Kang--Pikhurko
  Theorems 1 and 4 and Lemma 5; `docs/theory-notes.md` §§11--12;
  `src/generate_local_204_cnf.py`;
  `src/generate_local_205_near_cnf.py`; E008 and E009 experiment records.
- Verifiers: independent extremal-catalog and CNF reconstruction; semantic
  core-subset audit; byte-exact regeneration; pinned upstream C LRAT checker;
  independent streaming Python RUP checker; truncated, forged-empty, and
  semantic-core corruptions rejected.
- Hashes: E009 full CNF
  `93dd2fe7924b16c7836a8635d21ba28ac4dbc8d25b4f31042129714a24d07629`;
  core CNF
  `83b015ff7fa51c1a500454aeb6cbcb3ff9176955b7ea347c32bab151a83340ad`;
  raw LRAT
  `914593f53d0715ebeb04a7d738c63c29487a56dbc60385aaca77a5edafabb1b1`;
  compressed LRAT
  `b114c11ee1b7b1fca3f66c979b308e76ba693ae16fa5a25b80d94b8c81ed17f7`.
  All E008 per-case hashes are recorded in
  `experiments/E008-local-205-result.md` and `artifacts/SHA256SUMS`.
- Caveat: all nine CNFs are weaker necessary local systems. The E009 proof was
  generated from a verified clause core but its LRAT is checked directly
  against the full E009 CNF, so the core extractor is not a theorem trust
  dependency. There is no proof-assistant kernel, and the imported extremal
  theorem has not been locally formalized.
- Falsifier: an omitted count-205 branch, an invalid lower-count embedding, an
  unsafe symmetry break, a valid local configuration, a satisfying assignment,
  proof/checker failure, corruption acceptance, or a content-hash mismatch.

## C-LOC-004 — certified exclusion of local count 206

- Statement/scope: every vertex of a hypothetical balanced five-coloring of
  \(K_{26}\) satisfies \(L(v)\ge207\). Consequently
  \[
  B+3R\ge5382,\qquad2R-M\ge2782,\qquad3M\ge2E+182.
  \]
  This is an unrestricted necessary local theorem, not a decision of the full
  \(K_{26}\) coloring instance.
- Evidence class: 12 fixed order-22 obstructions, one full variable order-20
  obstruction, and 13 exhaustive variable order-21 branches are
  `machine-certified theorem`; the arithmetic classification, lower-count
  embeddings, edge-deletion split, branch coverage, and symmetry completeness
  are `proved lemma`, conditional on the imported Kang--Pikhurko extremal
  characterization. Overall project level remains `PARTIAL-CERTIFIED`.
- Dependencies/location: C-LOC-002, C-EQ-002, C-LOC-003;
  Kang--Pikhurko Theorems 1 and 4 and Lemma 5;
  `docs/theory-notes.md` §13; `src/generate_local_204_cnf.py`;
  `src/generate_local_206_near_cnf.py`; and the E011 experiment record.
- Verifiers: independent reconstruction of all arithmetic and extremal
  catalogs; exhaustive graph-subset, partition, orbit-fix, incidence,
  private-witness, forced-composition, and 13-branch audits; byte-exact CNF
  regeneration; zero-RAT LRAT conversion; pinned upstream C LRAT checker;
  independent streaming Python RUP checker; and deliberate truncated and
  forged-empty proof rejections.
- Hashes: every CNF, compressed LRAT, and decompressed LRAT hash is recorded in
  `experiments/E011-local-206-result.md` and protected by
  `artifacts/SHA256SUMS`.
- Caveat: every CNF is a weaker necessary local system. The order-21 proof uses
  the already certified E008 lower-edge obstruction plus a proved deletion
  dichotomy; its 13 composition branches exhaust that reduced system but are
  not the full \(K_{26}\) formula. There is no proof-assistant kernel, and the
  imported extremal theorem has not been locally formalized.
- Falsifier: an omitted local-count-206 profile or slack allocation, a
  nonessential edge evading E008, an omitted composition vector, an unsafe
  point/block symmetry, a valid local configuration, a satisfying assignment,
  proof/checker failure, corruption acceptance, or a content-hash mismatch.

## C-LOC-005 — certified exclusion of local count 207

- Statement/scope: every vertex of a hypothetical balanced five-coloring of
  \(K_{26}\) satisfies \(L(v)\ge208\). Consequently
  \[
  B+3R\ge5408,\qquad2R-M\ge2808,\qquad3M\ge2E+208.
  \]
  This is an unrestricted necessary local theorem, not a decision of the full
  \(K_{26}\) coloring instance.
- Evidence class: two classification-free variable-graph obstructions are
  `machine-certified theorem`; the complete slack reduction,
  spoke-pigeonhole elimination, lower-edge deletion split, forced
  compositions, and point-symmetry quotients are `proved lemma`, conditional
  on the imported Kang--Pikhurko extremal characterization. Twelve additional
  fixed certificates are valid but logically redundant. Overall project level
  remains `PARTIAL-CERTIFIED`.
- Dependencies/location: C-LOC-003 and C-LOC-004; Kang--Pikhurko Theorems 1
  and 4 and Lemma 5; `docs/theory-notes.md` §14;
  `src/generate_local_204_cnf.py`; `src/generate_local_207_near_cnf.py`; and
  `experiments/E012-local-207-result.md`.
- Verifiers: independent enumeration of all 23,751 profiles and every slack
  allocation; independent order-22/order-23 catalog reconstruction; exhaustive
  graph-subset, partition, private-witness, composition, branch, and orbit-fix
  clause audits; byte-exact regeneration; zero-RAT conversion; pinned upstream
  C LRAT checker; independent streaming Python RUP checker; and deliberate
  truncated and forged-empty proof rejections.
- Hashes: balanced canonical CNF
  `a89ecfe717b8c8d6690c170707ab849d7879305ac282a73082a9005f296d17aa`,
  raw LRAT
  `27f587864be207b81c140f3d723105104384a8b46d1ea87450726cb3da5d857d`,
  compressed LRAT
  `55ca21fb3d8376184dfe7560bf6f09086596c5bed898803717bb6f0ef5646e24`;
  unbalanced canonical CNF
  `b44f86f7184ec2556f61a51b29eb760b673a3cb1f394731747354f17215835e0`,
  raw LRAT
  `0452d08f44bca7e10c3fb662fb027148b56dee5e94427536fa707a062d4dd5ec`,
  compressed LRAT
  `7b729d5d33899aadb94f9f455f0e1572c0aa215b2229814895610d9c70b3b83f`.
  Every redundant fixed-CNF/proof hash is recorded in the E012 result and all
  committed hashes are protected by `artifacts/SHA256SUMS`.
- Caveat: both selected CNFs are weaker necessary local systems. Their use of
  edge-minimality depends on the already certified E011 lower-edge theorem;
  the unbalanced monolith additionally depends on the proved tight-block
  composition lemma. There is no proof-assistant kernel, and the imported
  extremal theorem has not been locally formalized.
- Falsifier: an omitted count-207 slack family, a degree-two or degree-three
  case evading the spoke lemma, a deletable edge evading E011, an unsafe point
  or block quotient, a valid local configuration, a satisfying assignment,
  proof/checker failure, corruption acceptance, or a content-hash mismatch.

## C-LOC-006 — certified exclusion of local count 208

- Statement/scope: every vertex of a hypothetical balanced five-coloring of
  \(K_{26}\) satisfies \(L(v)\ge209\). Consequently
  \[
  B+3R\ge5434,\qquad2R-M\ge2834,\qquad3M\ge2E+234.
  \]
  This is an unrestricted necessary local theorem, not a decision of the full
  \(K_{26}\) coloring instance.
- Evidence class: two classification-free one-exception obstructions and
  fourteen exhaustive classified double-exception obstructions are
  `machine-certified theorem`; the complete slack reduction,
  spoke-pigeonhole elimination, lower-edge deletion splits, equality-template
  coverage, and all representation/point quotients are `proved lemma`,
  conditional on the imported Kang--Pikhurko extremal characterization.
  Overall project level remains `PARTIAL-CERTIFIED`.
- Dependencies/location: C-LOC-003 through C-LOC-005; Kang--Pikhurko Theorems
  1 and 4 and Lemma 5; `docs/theory-notes.md` §15; the
  `src/generate_local_208_*` generators; and
  `experiments/E013-local-208-result.md`.
- Verifiers: independent enumeration of all 23,751 profiles and every slack
  allocation; complete graph, block, deletion-witness, composition,
  equality-template, true-twin, and hard-quotient clause audits; byte-exact
  regeneration; zero-RAT conversion; pinned upstream C LRAT checker;
  independent streaming Python RUP checker; exact metadata/raw/compressed
  hashes; and deliberate truncation and forged-empty rejection.
- Hashes: balanced one-exception CNF
  `1378d0e8d83b41c085ccfa248fc4d656395598888e04120dcce471fc12eb7686`
  and compressed LRAT
  `907b581039deb8c4e853f0aafa3032a39a119e6019525d899aa3e36c5adceb63`;
  unbalanced one-exception CNF
  `ebbb2adeb16dd20ffa83f305ff7b349989e7a80fd14606acadb28b843c41d707`
  and compressed LRAT
  `208281c73ddaac0ac8f7f8c34d617cb939613b1df12a3ed9975b5818ef3f2b84`;
  hard-branch CNF
  `4fd22bad0590d3b8ad611e303f8202cd8a6eb06c3d832d07dadf2eb6b66844da`
  and compressed LRAT
  `cc723764eb8e080518381d3f5820b8fa8834874a2bafb29ae2a6f35212637e99`.
  Every classified branch hash is in its adjacent metadata file, the E013
  result, and `artifacts/SHA256SUMS`.
- Caveat: every CNF is a weaker necessary local system. The classified double
  proof depends on the imported equality characterization; the hard quotient
  orders only two proved-interchangeable auxiliary class labels. Neither the
  four classification-free double monolith timeouts nor the original hard
  branch timeout is evidence. There is no proof-assistant kernel, and the
  imported theorem has not been locally formalized.
- Falsifier: an omitted count-208 slack allocation, a low-spoke case evading
  the spoke lemma, an invalid lower-edge embedding, an omitted equality type,
  a removed size-six template without a color \(K_6\), an unsafe color/point/
  class quotient, a valid local configuration, a satisfying assignment,
  proof/checker failure, corruption acceptance, or a content-hash mismatch.

## C-LOC-007 — certified exclusion of local count 209

- Statement/scope: every vertex of a hypothetical balanced five-coloring of
  \(K_{26}\) satisfies \(L(v)\ge210\). Consequently
  \[
  B+3R\ge5460,\qquad2R-M\ge2860,\qquad3M\ge2E+260.
  \]
  This is an unrestricted necessary local theorem, not a decision of the full
  \(K_{26}\) coloring instance.
- Evidence class: the complete exact-value-209 reduction, deletion bridges,
  equality-template coverage, quotients, and neighbor-color availability lemma
  are `proved lemma`, conditional on the imported Kang--Pikhurko theorem. The
  balanced target, all sixteen classified double branches, and the unbalanced
  target are covered by independently checked zero-RAT LRATs and are
  `machine-certified theorem`. Overall project level remains
  `PARTIAL-CERTIFIED`.
- Dependencies/location: `C-LOC-006`; Kang--Pikhurko Theorems 1 and 4 and
  Lemma 5; `docs/theory-notes.md` §16;
  `experiments/E014-local-209-result.md`; the
  `src/generate_local_209_*availability_cnf.py` generators;
  `artifacts/local_209_*availability/`; and
  `certificates/local_209_*availability/`.
- Verifiers: independent enumeration of all 23,751 profiles, 175 exact
  allocations, seventeen order-24 constructions, ten directed deletion
  bridges, and sixteen classified branches; exact reconstruction of 3,542,000
  availability clauses across the four final targets; byte-exact
  regeneration; zero-RAT conversion; pinned upstream C checker; independent
  streaming Python checker; sixteen deliberate corruption rejections; and XZ
  round-trip hashing.
- Hashes: the four final availability CNFs have SHA-256
  `6ad466ecc42f0f89ed4fb3a1a1b92be88f7d1de62125a20f0b3c67461611d501`,
  `cab6f6b1f6327b895505c9ba0bfcb2ca965ed0d3371382e6d6c65cf3fed39eb3`,
  `328a7f9fb5352176606baf61bcae1d80ef78cbb3367bad18aa2d160be2cb5ed8`,
  and `43dbcc7b6c66343483aedf5f99a79f3141121d76c3ae42ae6d557748f5314da6`.
  Their compressed LRAT SHA-256 values are
  `9f9c9ab1a1cbe23790c3d33187a8a24d7cc8bd89a3bef0bb227ffbb031f5b02a`,
  `29985d25d86c68932e3498a868c24cbbd79bc0b2f7b63f2ea66e16050f3bb30c`,
  `aa421f3b8ca6bff18204438f3e14406c05dea7a1383b551fe338fa2ea6df8e52`,
  and `a9b818efbda58bcfee50234fd16ff0ff7f3eb0e73ab63b78cc32ccd2ce5033b9`.
  Earlier target hashes are preserved in the E014 result and adjacent metadata.
- Caveat: every availability CNF is a weaker necessary local system, not the
  full coloring formula. The reduction depends on an imported extremal
  characterization, and neither that bridge nor the availability lemma has a
  proof-assistant kernel. The checked SAT model of the old hard child refutes
  only the old relaxation and is explicitly not a coloring. Deep split leaves
  and `UNKNOWN` runs are not theorem premises.
- Falsifier: an omitted profile, allocation, deletion direction, equality type,
  or branch; an unsafe quotient; an edge whose possible color evades the
  counted/unforced dichotomy; a satisfying assignment of a final availability
  CNF; a clause/hash mismatch; checker disagreement; or corruption acceptance.

## C-EDGE-001 — certified exclusion of 59-edge color classes

- Statement/scope: every color class in a hypothetical balanced five-coloring
  of \(K_{26}\) has at least 60 edges. Equivalently, every complement has at
  most 265 edges. This is an unrestricted necessary theorem coupling directly
  to the 325-edge partition; it is not a decision of the full instance.
- Evidence class: the 59-edge lower bound and equality reduction are `proved
  lemma`, conditional on the externally reviewed Kang--Pikhurko Theorems 1
  and 4 and Lemma 5. The final target-part six-set contradiction is a `proved
  lemma`. The two exact full-coloring branches are additionally a
  `machine-certified theorem` with zero-RAT LRATs. Overall project level
  remains `PARTIAL-CERTIFIED`.
- Dependencies/location: `C-RED-001`; Kang--Pikhurko Theorems 1 and 4 and
  Lemma 5; `docs/theory-notes.md` §17;
  `experiments/E018-unrestricted-minority59-result.md`;
  `src/generate_full_k26_minority59_cnf.py`;
  `artifacts/full_k26_minority59/`; and
  `certificates/full_k26_minority59/`.
- Verifiers: exhaustive positive-composition optimization; independent
  reconstruction of all four raw templates and both subset-complement
  isomorphisms; 920,920 template/six-set graph checks; complete independent
  clause reconstruction for both 1,155,051-clause exact formulas; zero-RAT
  conversion; pinned C and independent Python LRAT checkers; eight deliberate
  corruption rejections; exact regeneration; and four XZ round trips.
- Hashes: raw CNFs
  `1b5306ca48d37f1b4875898403a8ec733026b5629d7bf7691d67cd4e37808b77`
  and
  `d35a0234a9b1d4fdb414c2832bc75b7a7edcc02cb103783b7969f3809b2dfb9b`;
  compressed LRATs
  `2a98e31708e14858f08acadb81e52377b5e6e5305b10b48b981b5d5130e6f637`
  and
  `de59382c4ce544eaac06730de794b5df6ca1262a3a299e226a927ea559f4a739`.
- Caveat: the equality classification is imported from a peer-reviewed theorem
  whose proof is not locally formalized. There is no proof-assistant kernel.
  Counts 60 through 65 remain possible, so this does not resolve \(r=5\).
- Falsifier: a valid color graph with at most 59 edges; an omitted equality
  construction or subset orbit; a size-six part without a color \(K_6\); a
  surviving target-part six-set; unsafe remaining-color symmetry; a satisfying
  branch model; checker failure; corruption acceptance; or a hash mismatch.

## C-EDGE-002 — certified exclusion of 60-edge color classes

- Statement/scope: every color class in a hypothetical balanced five-coloring
  of (K_{26}) has at least 61 edges. Equivalently, every color complement has
  at most 264 edges. This is an unrestricted necessary theorem, not a decision
  of the full instance; counts 61 through 65 remain open.
- Evidence class: the deletion-to-criticality bridge, degree-three
  contradiction, three-level (K_5)-component recursion, equality-case
  eliminations, and final reconstruction are `proved lemma`, conditional on
  the imported Kang--Pikhurko Theorems 1 and 4 and Lemma 5. The order-11
  residual classification and exact four-color extension obstruction are
  `machine-certified theorem` with zero-RAT LRATs. Overall project level
  remains `PARTIAL-CERTIFIED`.
- Dependencies/location: `C-EDGE-001`; Kang--Pikhurko Theorems 1 and 4 and
  Lemma 5; Brooks' theorem; `docs/theory-notes.md` §18;
  `experiments/E024-minority60-candidate-extension-result.md`;
  `experiments/E027-minority60-recursive-reduction-result.md`;
  `experiments/E028-residual11-classification-result.md`; and the corresponding
  generators, artifacts, and certificates.
- Verifiers: complete enumeration of the degree-three and nine recursive
  degree-four edge allocations; 1,540 equality-transversal pair checks;
  independent enumeration of exactly 300 fixed-neighborhood residual graphs;
  exact reconstruction of the sole final 60-edge candidate; independent clause
  audits for the 9,128-clause residual counterexample CNF and the 1,156,025-
  clause exact extension CNF; zero-RAT conversion; pinned C and independent
  Python LRAT checkers; eight deliberate corruption rejections; exact
  regeneration; and four XZ round trips.
- Hashes: exact-extension raw CNF
  `452730027079db672ca49d3392acbbfdf335b3f3907dd5de12520da67fd794ec`,
  compressed LRAT
  `4fb5933925f28d1cab6f6e957e7b917eefd36670a44424461f813f889993c9bb`;
  residual-classification raw CNF
  `ccaf814291d3d1c3547a477ec3e6da670f9d3947b9d0e0b59f8a79131d8f5bdb`,
  compressed LRAT
  `399d97fabfbbb0e94893ce63dae2061a0cbacf5d3c7215033c4a1c79a9afb596`.
- Caveat: the extremal equality characterization is imported rather than
  formalized locally, and there is no proof-assistant kernel. The exploratory
  E019--E023, E025, and E026 timeouts and relaxation model are not theorem
  premises. The result excludes only edge count 60 beyond `C-EDGE-001`; it is
  not a certified UNSAT result for unrestricted (K_{26}).
- Falsifier: an edge deletable without producing a missing-color six-set; an
  omitted degree/edge allocation; an equality graph without the claimed part
  structure or avoiding transversal; failure of criticality inheritance; a
  second residual isomorphism class; a valid extension of the final candidate;
  checker disagreement; corruption acceptance; or a content-hash mismatch.

## C-EDGE-003 — certified exclusion of 61-edge color classes

- Statement/scope: every color class in a hypothetical balanced five-coloring
  of (K_{26}) has at least 62 edges. Equivalently, every color complement has
  at most 263 edges. This is an unrestricted necessary theorem, not a decision
  of the full instance; counts 62 through 65 remain open.
- Evidence class: the criticality bridge, degree-three route, recursive
  degree-four route, four-avoidance lemma, Turan deletion arguments, and
  residual reductions are `proved lemma`, conditional on the imported
  Kang--Pikhurko extremal theorem and equality description. Elimination of the
  16-vertex minimum-degree-five branch is a `proved lemma` conditional on
  Dirac's imported critical-graph edge theorem. The two-class residual
  exhaustiveness proof and both exact unrestricted extension obstructions are
  `machine-certified theorem` with RUP-only LRATs. Overall project level
  remains `PARTIAL-CERTIFIED`.
- Dependencies/location: `C-EDGE-002`; Kang--Pikhurko Theorems 1 and 4 and
  Lemma 5; Dirac's 1957 critical-graph edge theorem;
  `docs/theory-notes.md` section 19;
  `experiments/E029-minority61-recursive-reduction-result.md`; and the
  corresponding generators, graph descriptions, compressed CNFs, and
  certificates.
- Verifiers: every exact allocation in the degree-three, (K_4), and
  three-level (K_5) routes; 42,492 equality-template forbidden-set checks;
  independent semantic checking of both residual representatives; disjoint
  fixed-neighborhood orbits of sizes 600 and 300; exact independent
  reconstruction of all 9,609 residual-classification clauses; exhaustive
  six-set and edge-criticality checks of both 61-edge graphs; independent
  fixed-color and remaining-color canonical suffix audits for both 1,156,025-
  clause formulas; three RUP-only LRAT conversions; pinned C and independent
  Python LRAT checkers; twelve deliberate corruption rejections; exact
  regeneration; and six XZ round trips.
- Hashes: residual-classification raw CNF
  `c68186a346e06fa80fb14bd2c8e3f82a539d78fbe23fcb4c243a0b010ef5f5de`
  and compressed LRAT
  `f9c89420f60dde5c9ef26f72eb3d0db5c9be95467aa0360d17fcdc2b97d062de`;
  exact-extension raw CNFs
  `b2b8b55cefbd8dd56588dd8bd0019b0cdd0a4b5a4dda25fdace8c52b18202e71`
  and
  `034d480322a80cb204d6349451a535e3b2927159893e42a66545ee46babdcb1b`;
  compressed LRATs
  `b5a91ea0389bd46c3ee25b485e98e0510c5c572ac69e30c462ffb68b583985af`
  and
  `01d9c65216eb77ed0fcfee737757c6509c7b1775070ff0e048b95a7f82547559`.
- Caveat: neither imported extremal theorem is formalized locally, and there is
  no proof-assistant kernel. The incomplete independent enumerator, exploratory
  12-vertex raw UNSAT, and 16-vertex `UNKNOWN` run are explicitly not premises.
  This excludes only edge count 61 beyond `C-EDGE-002`; it is not a certified
  UNSAT result for unrestricted (K_{26}).
- Falsifier: a noncritical edge; an omitted allocation or equality attachment;
  failure of four-avoidance or criticality inheritance; a valid 16-vertex
  Dirac branch; a third residual isomorphism class; a valid exact extension of
  either candidate; unsafe remaining-color naming; a clause/hash mismatch;
  checker disagreement; corruption acceptance; or an XZ round-trip failure.

## C-EDGE-004 — certified exclusion of 62-edge color classes

- Statement/scope: every color class in a hypothetical balanced five-coloring
  of (K_{26}) has at least 63 edges. Equivalently, every color complement has
  at most 262 edges. This is an unrestricted necessary theorem, not a decision
  of the full instance; least-color counts 63, 64, and 65 remain open.
- Evidence class: the criticality bridge, complete degree-three route,
  recursive degree-four route, equality and slack attachment lemmas, Turan
  deletion arguments, final regular-complement lemma, and critical-subgraph
  case split are `proved lemma`, conditional on the imported Kang--Pikhurko,
  Dirac, and Kostochka--Yancey theorems. The four-class residual exhaustiveness
  proof and all four exact unrestricted extension obstructions are
  `machine-certified theorem` with RUP-only LRATs. Overall project level
  remains `PARTIAL-CERTIFIED`.
- Dependencies/location: `C-EDGE-003`; Kang--Pikhurko Theorems 1 and 4 and
  Lemma 5; Dirac's 1957 critical-graph edge theorem; Kostochka--Yancey (2014),
  Theorem 3; `docs/theory-notes.md` section 20;
  `experiments/E030-minority62-critical-frontier-result.md`; and the
  corresponding generators, graph descriptions, compressed CNFs, and
  certificates.
- Verifiers: all top and recursive edge allocations; 140 equality attachment
  checks; complete (K_4-e), paw, and deletion-template audits; all five
  16-vertex critical-subgraph orders; the six labeled final stars; independent
  semantic checking of four residual representatives; disjoint fixed-vertex
  orbits of sizes 4,800, 5,400, 2,400, and 1,800; exact independent
  reconstruction of all 22,986 residual-classification clauses; exhaustive
  six-set and edge-criticality checks of all four 62-edge graphs; independent
  fixed-color and remaining-color suffix audits for all four 1,156,025-clause
  formulas; five RUP-only LRAT conversions; pinned C and independent Python
  LRAT checkers; 20 deliberate corruption rejections; exact regeneration; and
  ten XZ round trips.
- Hashes: residual-classification raw CNF
  `a2003ca60b633cdc0856d63969fcc57e6f6e65bc39fa272d127ea812c432e720`
  and compressed LRAT
  `84588ea0b002325f5dc01ce22cb7fa185fcb35b50d2dbd29571b460c9cf135b5`;
  exact-extension raw CNFs
  `96a0f8907aed23aa6e12d1cccbd047e414aef9114ff7f0683504d8fbfed4feaa`,
  `7c076c1f601cf3ff5d87f9408eb39090fd42904327483c531af0436ca9c8ee2d`,
  `9fe9d28787dcaa622afde8aac738f577fd32c655f1813ca7ce754cbdf0dc28fd`,
  and
  `2fd5cbf41af716fe3875634cc608b6639d21e20b8533e2cb1d5f5a2927ce9df0`;
  compressed LRATs
  `db19cafc29d5e611c40ea16415208d7bed02317912f61fae7bc587e84edfe852`,
  `059e4617c56d13c310eeb26fdd98ca028ee49a48ade7c60621a5abfe0cc9d2fe`,
  `c20ec3196d2491efb6e2d888c97f665ddbe38467182c045ef0ec75dd081d4883`,
  and
  `5a503cca49974447093a27d6b581a1a4536217fba89eaeb2d58dc71599860a36`.
- Caveat: the imported extremal and critical-graph theorems are not formalized
  locally, and there is no proof-assistant kernel. Raw solver and nauty results
  are explicitly not premises. This excludes only edge count 62 beyond
  `C-EDGE-003`; it is not a certified UNSAT result for unrestricted (K_{26}).
- Falsifier: a noncritical edge; an omitted allocation or attachment orbit; an
  invalid deletion or critical-subgraph case; a fifth residual isomorphism
  class; a valid exact extension of any candidate; unsafe remaining-color
  naming; a clause/hash mismatch; checker disagreement; corruption acceptance;
  or an XZ round-trip failure.

## C-EDGE-005 — certified exclusion of 63-edge color classes

- Statement/scope: every color class in a hypothetical balanced five-coloring
  of \(K_{26}\) has at least 64 edges. Equivalently, every color complement has
  at most 261 edges. This is an unrestricted necessary theorem, not a decision
  of the full instance; least-color counts 64 and 65 remain open.
- Evidence class: the criticality bridge; complete degree-zero-through-four,
  recursive component, equality/slack attachment, avoidance, and critical-core
  reductions; and the derivation that the final 16-vertex residual is itself
  6-critical are `proved lemma`, conditional on the imported
  Kang--Pikhurko, Dirac, and Kostochka--Yancey theorems. Exhaustiveness of the
  one residual-12 class, five residual-11 classes, and 48 order-16 6-Ore
  classes, together with all exact unrestricted extension obstructions, is a
  `machine-certified theorem` with RUP-only LRATs and independently audited
  enumeration. Overall project level remains `PARTIAL-CERTIFIED`.
- Dependencies/location: `C-EDGE-004`; Kang--Pikhurko Theorems 1 and 4 and
  Lemma 5; Dirac's 1957 critical-graph edge theorem; Kostochka--Yancey (2014),
  Theorem 3; Kostochka--Yancey, *A Brooks-Type Result for Sparse Critical
  Graphs*, Theorem 6; `docs/theory-notes.md` section 21;
  `experiments/E031-minority63-critical-frontier-result.md`; and the E031
  generators, graph catalogs, compressed CNFs, and certificates.
- Verifiers: fresh exact allocation and physical-attachment enumeration; all
  residual minimum-degree branches; one 420-label residual-12 orbit; five
  residual-11 orbits of sizes 2,520, 11,340, 7,560, 3,780, and 8,640; 2,700
  raw order-11 and 25,620 raw order-16 DHGO compositions; exact independent
  isomorphism checking; an independent nauty count of 48 order-16 classes;
  direct 6-criticality and private-set checks; independent reconstruction of
  every theorem-bearing clause; 13 RUP-only LRAT conversions; pinned C and
  independent Python LRAT checkers; 52 deliberate corruption rejections;
  exact regeneration; and 26 XZ round trips.
- Hashes: the 6-Ore catalog is
  `4ce8ecf036d6686c0b8af26c762877896b2bbcab41cee96fea09474ebb87ff48`;
  the final selector-disjunction raw CNF is
  `83707a0c46e24697ae7e4589612b08a38393ae5448c8ea22f060c3bbf0d0c6b4`,
  its raw LRAT is
  `6be3d182cc47ec2d8afa2da09cd4b5a53226c5d2925634fc6509a64d0c7cb109`,
  and its checker-combined digest is
  `dd119b564f9dd9ed3a5659223f3cf20ab44e7dc26c9311197ce2e55b8f65a01a`.
  All 13 raw/compressed CNF and LRAT hashes are recorded in
  `tests/test_minority63_certificates.py`, `experiments/manifest.json`, and
  `artifacts/SHA256SUMS`; the E031 result records the proof statistics and
  checker-combined digests.
- Caveat: the imported extremal and critical-graph theorems are not formalized
  locally, and there is no proof-assistant kernel. Broad and strengthened
  `UNKNOWN` runs, incomplete proof traces, a graph-only SAT model, and the raw
  nauty result are explicitly not theorem premises. This excludes only exact
  count 63 beyond `C-EDGE-004`; it is not a certified UNSAT result for the
  unrestricted \(K_{26}\) formula.
- Falsifier: a noncritical edge; an omitted allocation, attachment, component,
  or minimum-degree branch; a proper 6-critical core surviving the excess
  audit; a non-Ore equality graph; an omitted DHGO composition or isomorphism
  class; a valid unrestricted extension of any residual class; unsafe
  remaining-color naming; a clause/hash mismatch; checker disagreement;
  corruption acceptance; or an XZ round-trip failure.

## C-R5-001 — historical independently audited r=5 proof candidate

- Statement/scope: every five-coloring of \(E(K_{26})\) has six vertices whose
  induced \(K_6\) omits a color. Together with the independently checked
  affine-plane construction on 25 vertices, this gives the candidate equality
  \(R(6;5,4)=26\). This statement concerns only fixed \(r=5\) and does not
  resolve the all-\(r\) Erdős Problem 617 conjecture.
- Current status: `HISTORICAL`, superseded by the independent E058
  machine-verification claim `C-R5-002`.
- Evidence class at the E033 checkpoint: `CANDIDATE-RESOLUTION`. The complete external TeX source at
  pinned commit `735c2eeffcb5c8abe92f8a6be04be2fa3c8bb6ab` was read and rebuilt; every
  deduction was reconstructed line by line; the complete Kang--Pikhurko source
  and exact hypotheses were re-audited; and independent finite enumeration
  corroborates every order-10/order-11 classification. No gap was found. The
  whole proof is not proof-assistant checked and has no complete theorem-level
  certificate chain, so it is not `MACHINE-VERIFIED-RESOLUTION`. The manuscript
  has not completed qualified external review.
- Dependencies/location: Brooks's theorem; Kang--Pikhurko (2005), Theorems 1
  and 4 and Lemma 5; the external manuscript with TeX SHA-256
  `47ce42a3c7116f125bada1416e90d4f40a25ce5284362c98de3077bc51fcc769`;
  `experiments/E033-external-fixed-cases-audit-plan.md`;
  `experiments/E033-external-fixed-cases-audit-result.md`; and
  `tests/test_external_r5_proof_audit.py`.
- Verifiers: clean 15-page TeX build with no final warnings; independent
  optimization and reconstruction of all 20 relevant Kang--Pikhurko equality
  templates; semantic checking of all 12,172 nonisomorphic triangle-free
  graphs on ten vertices and all 6,153 relevant graphs on eleven vertices;
  independent verification of the balanced two-fold \(C_5\) blow-up and its
  minimum covers; recomputation of every degree table and equality split; and
  exhaustive checking of all 177,100 six-sets in the affine construction.
- Hashes: source snapshot
  `40f0a215414941acb9e0f7aa5d65db9bfd1f1db0d519d97cbc8ac1c0c663045a`;
  order-10 raw catalog
  `162cd507b93e74307ed9e88052da7bfb6f68e6cfeae6ccd2254c949c84ce0214`;
  order-11 raw catalog
  `ce477f7ec1b99986993dd8386b7484dfd6378181eb29c292cf4b1a67157b7e61`;
  independent checker
  `273478d11c6ca37d2212eeebb79869649058e248229eb44a1d1645c7a8141eb4`.
- Caveat: the machine catalogs corroborate the manuscript's finite lemmas but
  are not themselves a formalization of the complete proof. The imported
  Kang--Pikhurko proof is peer-reviewed but not locally kernel-checked. The
  r=6,7,8,9 claims in the same external repository were not audited in E033 and
  receive no verification upgrade from this claim.
- Falsifier: an incorrect imported hypothesis; a counterexample to any
  independence-two, independence-three, independence-four, order-10, or
  order-15 lemma; an omitted minimum-degree or equality branch; failure of the
  edge equalization; a source/hash mismatch; a catalog completeness failure;
  or a valid balanced five-coloring of \(K_{26}\).

## C-FORMAL-001 — kernel-checked partial r=5 foundation

- Statement/scope: in the exact unordered-edge Lean model, the fixed r=5
  statement is equivalent to absence of a balanced coloring; missing a color
  is equivalent to an independent six-set in its color graph and a
  complementary `K₆`; the five color graphs partition all 325 edges; the
  affine construction gives a balanced five-coloring on 25 vertices; distinct
  color complements satisfy the chromatic-product bound; every hypothetical
  balanced coloring on 26 vertices has local color counts from one through
  eleven, every color graph has at least 55 edges, some has at most 65 edges,
  and such a sparse graph has no isolated vertex.
- Evidence class: `machine-certified theorem` for exactly the exported Lean
  lemmas, hence project verification level `PARTIAL-CERTIFIED`. No exported
  theorem proves the r=5 upper statement, so this does not promote
  `C-R5-001` and does not concern the full all-r conclusion.
- Dependencies/location: Lean 4 `v4.32.0` commit
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`; mathlib `v4.32.0` commit
  `81a5d257c8e410db227a6665ed08f64fea08e997`;
  `formal/lean/`; `experiments/E034-r5-lean-formalization-plan.md`; and
  `experiments/E034-r5-lean-formalization-result.md`.
- Verifiers: warning-clean fresh-directory build of all 1,249 jobs; assumption
  audit of all 43 exported theorems; source scan for placeholders, axiom and
  unsafe declarations, and unchecked native computation. Every theorem query
  reports exactly `propext`, `Classical.choice`, and `Quot.sound`, with no
  project-defined assumption.
- Hashes: exact Lake manifest
  `acfc19d483c350eb6dad0e0d02681ccc167db7e44446e3c3f4ef74067d2b4267`;
  build-and-audit log
  `e51059e2721316630c0bc28783e0a013092d4c4c0c0e8eab30ce4c7164d6b39e`;
  per-module hashes are recorded in `artifacts/SHA256SUMS` and the E034
  manifest entry.
- Caveat: the clean project build reused the official cache for the pinned
  mathlib commit rather than rebuilding mathlib from source. The specialized
  Brooks application, Kang--Pikhurko theorem and equality cases, endpoint
  classifications, edge equalization, and final contradiction are not in the
  checked dependency graph.
- Falsifier: a clean-build failure from the pinned manifest; an unordered-edge
  or quantifier mismatch; an unexpected project axiom or placeholder; unsafe
  computation; a theorem counterexample; or a source/hash mismatch.

## C-FORMAL-002 — neighborhood reduction and complete finite Brooks certificate

- Statement/scope: in the pinned Lean graph model, the open-neighborhood
  crossing and internal edge counts satisfy the exact degree-sum identity. At
  a minimum-degree vertex of degree (d), they obey
  (X+2Y\ge d(d-1)), (Y\le\binom d2), and
  (X+Y\ge\binom d2). At degree five, admissibility gives (Y\le6) and
  (X+Y\ge14), and the extreme equality case gives an isolated clique on the
  closed neighborhood. The kernel also checks the independent-six/five-
  colorability bridge and that a 26-vertex graph with at most 65 edges and
  minimum degree at least five is 5-regular.
- Finite certified scope: for the exact special-Brooks obstruction needed by
  E035 (admissible and 5-regular on 26 vertices, no independent six-set, no
  six-clique), the 26 open-neighborhood isomorphism branches and safe exterior-
  pattern, cross-pattern, residual-anchor, and zero-anchor quotients are
  independently reconstructed. Each branch formula is a safe relaxation using
  proved local consequences of admissibility. E038 certifies branches 00--18;
  E042--E043 certify branch 19 through 17 direct and 47 residual LRATs; E045
  certifies branches 20--25. The union of all 89 zero-RAT certificates proves
  that no graph satisfies the finite special-Brooks hypotheses.
- Evidence class: the exported Lean lemmas and the complete finite obstruction
  are `machine-certified theorem`, hence this exact layer is
  `PARTIAL-CERTIFIED` toward fixed r=5. The external LRAT theorem is not
  imported into the Lean kernel, so the source theorem taking special Brooks
  as a parameter remains syntactically conditional. Kang--Pikhurko, later
  endpoints, and the final r=5 contradiction are still absent; `C-R5-001`
  remains `CANDIDATE-RESOLUTION`.
- Dependencies/location: `formal/lean/Erdos617/NeighborhoodAccounting.lean`;
  `formal/lean/Erdos617/DegreeReduction.lean`;
  `experiments/E035-r5-initial-structural-formalization-result.md`;
  `experiments/E038-r5-brooks-exterior-pattern-symmetry-result.md`;
  `experiments/E042-r5-brooks-branch19-cross-pattern-result.md`;
  `experiments/E043-r5-brooks-zero-pattern-neighborhood-result.md`;
  `experiments/E045-r5-brooks-zero-anchor-quotient-result.md`; and the E038,
  E042, E043, and E045 artifact/certificate directories.
- Verifiers: warning-clean fresh-directory Lean build; all 64 exported-theorem
  assumption queries; independent CNF, counter, orbit, and lex-recurrence
  reconstruction; exact regeneration of all 89 formulas; pinned C and
  independent Python LRAT checkers; zero-RAT audit; 356 deliberate corruption
  rejections; and compressed/raw hash round trips.
- Hashes: Lean build/audit log
  `3e1986b89a7b6d8cbafc79868d6ef18867937c478d621e5b978cd53f6d125b67`;
  neighborhood module
  `98bcd9810f9f3f6d05fa9ab71762fee35abee4c5fbb2268c53d35f55be0925f5`;
  degree-reduction module
  `ea100b36d80f381c14987d4d4484ed39a24f65d7e3e35e59b6dcf00007c859e2`;
  E038 receipt
  `4dc9b52aa30c321f14a8be873cf61b09cd53400dd29aac0f78288da9fa8c32af`;
  E042 receipt
  `f1a42f4ebe2c3ccd28e5e050e52e494800e210e473458cd1466146e05bdd9319`;
  E043 receipt
  `fd60b220ab27b19a221eaebaa7893b3c1b0c3293cfd484da602dc06eb0f95a1d`;
  and E045 receipt
  `9481c920cb33de9afb20eac982fd517fd8bac5ebbd5986f91d67459f5cd0fdde`;
  combined replay log
  `ae39396770fb20f28cf6dfd00af46978c7881d5f002f8af36f159bd3ab41bd25`.
- Caveat: the Lean clean build reused downloaded packages for the exact pinned
  mathlib commit. The LRAT branch results are not imported into Lean. Capped
  `UNKNOWN` searches on the monolithic formula, unsorted samples, and E044
  strengthened formulas are non-evidence. The Kang--Pikhurko theorem, later
  endpoint arguments, and final contradiction remain outside the checked
  dependency graph.
- Falsifier: an incorrect graph-cardinality bridge; an unsafe neighborhood or
  exterior orbit; an omitted branch; a formula/regeneration mismatch; an
  unexpected Lean assumption; an accepted certificate corruption; a checker
  failure; or a source/artifact hash mismatch.

## C-KP-001 — four broad extremal specializations by finite certificates

- Statement/scope: for a simple graph `F` with clique number at most five and
  independence number at most three, orders 19, 20, 21, and 22 force at least
  56, 62, 69, and 76 edges respectively. These statements do not assume
  admissibility and replace four numerical Kang--Pikhurko invocations at
  certificate level.
- Evidence class: `machine-certified theorem` for the four anchored CNFs plus
  a `proved lemma` orbit bridge. Under the contradictory edge cap, averaging
  supplies a vertex of degree at most 5, 6, 6, or 6; relabeling that vertex as
  zero and its neighbors first retains a representative of every graph orbit.
  The bridge is independently exhaustively audited but is not in Lean, so this
  remains `PARTIAL-CERTIFIED` toward fixed r=5.
- Dependencies/location: `experiments/E046-r5-kang-pikhurko-large-specializations-plan.md`;
  `experiments/E047-r5-kp-average-degree-anchor-result.md`;
  `src/generate_r5_kp_large_specialization_cnf.py`;
  `src/generate_r5_kp_average_degree_anchor_cnf.py`;
  `artifacts/e047_kp_average_degree_anchor/`; and
  `certificates/e047_kp_average_degree_anchor/`.
- Verifiers: independent reconstruction of all subset and unary-counter
  clauses; exhaustive counter and anchor truth tables; explicit graph
  canonicalization tests; exact regeneration of all six parent and all six
  anchored inputs; zero-RAT
  conversion; pinned upstream C and independent Python LRAT checkers; 16
  rejected proof corruptions; and raw/XZ hash round trips.
- Hashes: receipt
  `493faac7232d5f3286a19fb9a2d9b74da9dcb88f4353b627e94eace0e750f3b1`;
  all per-case CNF and LRAT hashes are recorded in that receipt and protected
  by `artifacts/SHA256SUMS`.
- Caveat: the order-24 and order-25 independence-four formulas returned
  `UNKNOWN` and are not evidence. The four proved formulas and their orbit
  bridge are not imported into the Lean kernel. This does not cover either
  order-10/order-15 equality endpoint or the full r=5 deduction; E051 now
  separately discharges the order-10 endpoint in Lean.
- Falsifier: an omitted graph orbit; an invalid average-degree cap or
  relabeling; a clause/counter mismatch; a satisfying anchored graph; an
  accepted corruption; checker disagreement; or a content-hash mismatch.

## C-FORMAL-003 — large admissible independence-two terminal bound

- Statement/scope: if a finite simple graph `F` is admissible and has no
  independent triple, every complement degree is at most five. If its order is
  at least twelve, every complement degree is at most four and
  `(card V).choose 2 <= #F.edgeFinset + 2 * card V`. Equivalently,
  `e(F) >= binom(n,2) - 2n`.
- Evidence class: `machine-certified theorem` in the pinned Lean kernel. This
  discharges exactly the manuscript's large independence-two terminal lemma
  and keeps the overall fixed-r=5 proof at `CANDIDATE-RESOLUTION`.
- Dependencies/location: `formal/lean/Erdos617/AlphaTwoLarge.lean`;
  `formal/lean/Erdos617/Audit.lean`;
  `experiments/E048-r5-admissible-alpha-two-formalization-result.md`; and
  `artifacts/e048_lean_build.log`.
- Verifiers: clean 1,294-job Lean 4.32.0/mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997` build; all 70 exported-theorem
  assumption queries; warning scan; and source scan for placeholders, added
  axioms, unsafe declarations, and unchecked native computation. Only subsets
  of `propext`, `Classical.choice`, and `Quot.sound` occur.
- Hashes: the module, audit source, and clean transcript are protected by
  `artifacts/SHA256SUMS`; exact values are also recorded in the E048 manifest
  entry.
- Caveat: this claim alone does not prove the order-11 or order-10 endpoints
  (now separately discharged by E050 and E051), independence-three/four
  recursion, the order-15 classifications (now separately discharged by
  E053), edge equalization, or final contradiction. E049 separately proves
  the large numerical propagation.
  External LRAT results are not Lean dependencies.
- Falsifier: a clean-build or assumption-audit failure; an induced-complement,
  subtype-cardinality, cross-edge, or handshaking error; a graph satisfying the
  hypotheses but violating either degree cap or the edge bound; or a source
  hash mismatch.

## C-FORMAL-004 — admissible independence-level propagation

- Statement/scope: for every finite admissible simple graph, the complement of
  a closed neighborhood is an admissible induced subgraph and passing to that
  exterior reduces `IndepSetFree (k+1)` to `IndepSetFree k`. The graph's edges
  split exactly across the neighborhood, exterior, and crossing parts; a
  minimum-degree vertex satisfies `n * degree(v) <= 2e`; and the checked local
  inequalities give
  `e(exterior) + degree(v) + choose(degree(v),2) <= e(F)`. Consequently, for
  `IndepSetFree 4`, orders 18--24 force respectively 54, 56, 62, 69, 76, 83,
  and 90 edges. For `IndepSetFree 5`, orders 24 and 25 force respectively 65
  and 71 edges.
- Evidence class: `machine-certified theorem` in the pinned Lean kernel. This
  replaces all six large numerical Kang--Pikhurko uses inside the admissible
  fixed-r=5 proof context. It does not assert the broader order-24/25 formulas
  without admissibility.
- Dependencies/location: `formal/lean/Erdos617/AlphaPropagation.lean`;
  `formal/lean/Erdos617/AlphaTwoLarge.lean`;
  `formal/lean/Erdos617/Audit.lean`;
  `experiments/E049-r5-admissible-alpha-propagation-result.md`; and
  `artifacts/e049_lean_build.log`.
- Verifiers: a fresh clean 1,296-job Lean 4.32.0/mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997` build; all 90 exported-theorem
  assumption queries; warning scan; source-safety scan; and exact comparison
  with a fresh project mirror. Only subsets of `propext`, `Classical.choice`,
  and `Quot.sound` occur.
- Hashes: `AlphaPropagation.lean` is 26,979 bytes with SHA-256
  `6e172bb627782d1b83569bf5b40c7cf1a2a800b373177b28aa89657830e7b21b`;
  the 71,147-byte audit transcript has SHA-256
  `ea0e9bcfa11e538f4ef17e9e63e44d08d2dfd96c9bf3e96fe2f884c38a5aeae0`;
  and the strict audit runner has SHA-256
  `739e5798cfb40548816efffc66736e0c8a374a1973e89f19f3045671088dc154`.
- Caveat: this does not by itself prove the order-11 or order-10 terminal
  endpoints (now separately discharged by E050 and E051), either order-15
  classification (now separately discharged by E053), the small
  independence-three obstruction (now separately discharged by E052), or the
  complete independence-four obstruction (now separately discharged by E054).
  It also does not prove the special-Brooks certificate-to-Lean bridge, edge equalization, or the final
  equality recursion. Fixed r=5 remains `CANDIDATE-RESOLUTION`; all-r remains
  `OPEN`.
- Falsifier: a clean-build or assumption-audit failure; an incorrect induced-
  subgraph, exterior-cardinality, edge-partition, minimum-degree, or arithmetic
  branch; a graph satisfying a stated hypothesis but violating a bound; an
  unsafe source construct; or a source/artifact hash mismatch.

## C-FORMAL-005 — order-eleven admissible independence-two endpoint

- Statement/scope: every finite admissible simple graph `F` on eleven vertices
  with `F.IndepSetFree 3` has at least 36 edges. Equivalently, its
  triangle-free complement has at most 19 edges when every six vertices span
  at least four complement edges.
- Evidence class: `machine-certified theorem` in the pinned Lean kernel. This
  discharges exactly the order-eleven terminal lower bound used by the audited
  fixed-`r=5` proof.
- Dependencies/location: `formal/lean/Erdos617/AlphaTwoEleven.lean`;
  `formal/lean/Erdos617/Audit.lean`;
  `experiments/E050-r5-order-eleven-terminal-formalization-result.md`; and
  `artifacts/e050_lean_build.log`.
- Verifiers: a source-identical clean 1,297-job Lean 4.32.0/mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997` build; all 105 exported-theorem
  assumption queries; zero-warning check; exact clean-mirror comparison; and
  source scan for placeholders, declared axioms, unsafe declarations, and
  unchecked native computation. Only subsets of `propext`,
  `Classical.choice`, and `Quot.sound` occur.
- Hashes: `AlphaTwoEleven.lean` is 50,707 bytes with SHA-256
  `7e35ae11ed4c920fbaeb7a1ed90929135520772b13a1609e0d9c014a72cb4bc4`;
  the 73,118-byte audit transcript is
  `449d5b654dbcceca45bfd82dcc998e3b73617537af54ed4ae6161d39a2df4f9b`;
  and the strict audit runner is
  `41318fbfcdfa8b164722dc651a83bce2623b094a722d987473d03b484bf28408`.
- Caveat: this claim alone does not prove the order-ten structure theorem (now
  separately discharged by E051), either order-fifteen classification (now
  separately discharged by E053), the
  small independence-three obstruction (now separately discharged by E052),
  or the complete independence-four obstruction (now separately discharged
  by E054). It also does not prove the special-Brooks
  certificate-to-Lean bridge, edge equalization, or the final coloring
  contradiction. Fixed `r=5` remains a
  `CANDIDATE-RESOLUTION`; all-`r` remains `OPEN`. The external fixed
  `r=6`--`r=9` claims are not dependencies.
- Falsifier: a clean-build, warning, source-safety, or assumption-audit
  failure; an invalid degree-five exclusion, handshaking choice, edge
  partition, exact cross-degree argument, label collision, or six-set count;
  a graph satisfying the hypotheses with at most 35 edges; or a source/artifact
  hash mismatch.

## C-FORMAL-006 — complete order-ten structure endpoint

- Statement/scope: let `G` be an admissible finite simple graph on ten
  vertices. If `Gᶜ` is bipartite, the vertices split into two five-sets that
  are cliques of `G`, with the `G`-edges across them forming a matching. If
  also `G.IndepSetFree 3` and `Gᶜ` is nonbipartite, then `Gᶜ` has at most
  twenty edges; at equality it is isomorphic to the canonical balanced
  two-fold blow-up of `C5`. At nineteen complementary edges, admissibility
  alone implies `Gᶜ.IndepSetFree 5`. The canonical blow-up has independence
  number four and vertex-cover number six; its six-vertex covers are exactly
  the five alternating unions of three two-vertex fibres, and distinct such
  covers intersect in at most four vertices.
- Evidence class: `machine-certified theorem` in the pinned Lean kernel. This
  discharges every conclusion preregistered for the order-ten endpoint used by
  the audited fixed-`r=5` proof.
- Dependencies/location: `formal/lean/Erdos617/OrderTenStructure.lean`;
  `formal/lean/Erdos617/Audit.lean`;
  `experiments/E051-r5-order-ten-structure-formalization-plan.md`;
  `experiments/E051-r5-order-ten-structure-formalization-result.md`; and
  `artifacts/e051_lean_build.log`.
- Verifiers: a fresh mirror whose local build directory was absent before the
  run; all 1,309 Lean 4.32.0/mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997` jobs; all 152 exported-theorem
  assumption queries; zero-warning check; and a fourteen-file scan for
  placeholders, declared axioms, unsafe declarations, and unchecked native
  computation. Every theorem uses only a subset of `propext`,
  `Classical.choice`, and `Quot.sound`; one Boolean helper uses no axioms.
- Hashes: `OrderTenStructure.lean` is 101,821 bytes with SHA-256
  `81676c0c075ced2b31856e24b5e7d1b15cb66c7a8c984260692db5cbe5315c12`;
  the 18,108-byte audit transcript is
  `fb4f36fa1599c7d8e9cde7eff2678ad94f5db29ffd01cebd26f7f88382cb583f`;
  and the strict audit runner is
  `61b2811003a318f317160d8acfb51fc751c3e67156e5ae7833a8355e91058001`.
- Caveat: this does not prove either order-fifteen classification (now
  separately discharged by E053), the small independence-three obstruction
  (now separately discharged by E052), the
  complete independence-four obstruction (now separately discharged by E054),
  the special-Brooks
  certificate-to-Lean bridge, edge equalization, or the final coloring
  contradiction. Fixed `r=5` remains `CANDIDATE-RESOLUTION`; the all-`r`
  conjecture remains `OPEN`, and the external fixed `r=6`--`r=9` claims are
  not dependencies.
- Falsifier: a fresh-build, warning, source-safety, or assumption-audit
  failure; an invalid degree-five bipartition, exterior classification,
  equality isomorphism, compact kernel reduction, cover transport, or
  nineteen-edge count; a graph satisfying a stated hypothesis but violating
  its conclusion; or a source/artifact hash mismatch.

## C-FORMAL-007 — complete small independence-three obstruction

- Statement/scope: every finite admissible simple graph `G` with
  `G.IndepSetFree 4` has at least 45 edges at order 16, at least 50 edges at
  order 17, and at least 54 edges at order 18. Equivalently, none exists in
  the ranges `(16, <=44)`, `(17, <=49)`, or `(18, <=53)`.
- Evidence class: `machine-certified theorem` in the pinned Lean kernel. This
  discharges the full small independence-three obstruction used by the
  audited fixed-`r=5` proof, not merely a restricted degree family.
- Dependencies/location: `formal/lean/Erdos617/AlphaThreeSmall.lean`;
  `formal/lean/Erdos617/Audit.lean`;
  `experiments/E052-r5-small-alpha-three-obstruction-formalization-plan.md`;
  `experiments/E052-r5-small-alpha-three-obstruction-formalization-result.md`;
  `artifacts/e052_lean_build.log`; and E048--E051's previously audited
  theorems. The order-18 conclusion is reused from E049.
- Verifiers: a fresh mirror whose local build directory was absent before the
  run; all 1,310 Lean 4.32.0/mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997` jobs; all 159 exported-theorem
  assumption queries; zero-warning check; and a fifteen-file scan for
  placeholders, declared axioms, unsafe declarations, and unchecked native
  computation. Every theorem uses only a subset of `propext`,
  `Classical.choice`, and `Quot.sound`; one Boolean helper uses no axioms.
- Hashes: `AlphaThreeSmall.lean` is 34,329 bytes with SHA-256
  `69071945fe7ca000cbb1e6982fcf5df6ebb69ecac87c5efc1f406bd96e5ffdaa`;
  the 19,059-byte audit transcript is
  `29f5bc8330cfa105f4b3b4bb2e615f5bbba45486335f284ad550d2486527b74c`;
  and the strict audit runner is
  `bd8a4cfea0e0e29ff0f71d44b0af88734956c097e15474759e9fe8a1f37fec0d`.
- Caveat: this does not prove either order-fifteen near-extremal
  classification (now separately discharged by E053), or the complete
  independence-four obstruction (now separately discharged by E054). It also
  does not prove the
  special-Brooks certificate-to-Lean bridge, edge equalization, or the final
  coloring contradiction. Fixed `r=5` remains `CANDIDATE-RESOLUTION`; the
  all-`r` conjecture remains `OPEN`, and external fixed `r=6`--`r=9` claims
  are not dependencies.
- Falsifier: a fresh-build, warning, source-safety, or assumption-audit
  failure; an omitted minimum-degree branch; an invalid common-avoider,
  equality-accounting, pointwise-degree, vertex-cover, or cardinality step; a
  graph in a stated forbidden range satisfying the hypotheses; or a
  source/artifact hash mismatch.

## C-FORMAL-008 — complete order-fifteen near-extremal classifications

- Statement/scope: let `G` be an admissible finite simple graph on fifteen
  vertices with `G.IndepSetFree 4` and non-three-colorable complement. At 35
  edges, some five-set is an isolated clique and the complement induced on
  its complement is isomorphic to the canonical balanced two-fold `C5`
  blow-up. At 36 edges, exactly one of two structures holds: a five-clique
  has exactly one edge leaving it and the same canonical residual complement,
  or an isolated five-clique has a residual complement that is triangle-free,
  has nineteen edges, and has no independent five-set. The two 36-edge
  structures are proved incompatible, not merely exhaustive.
- Evidence class: `machine-certified theorem` in the pinned Lean kernel. This
  discharges both order-fifteen classifications used by the audited fixed-
  `r=5` proof.
- Dependencies/location:
  `formal/lean/Erdos617/OrderFifteenStructure.lean`;
  `formal/lean/Erdos617/Audit.lean`;
  `experiments/E053-r5-order-fifteen-classification-formalization-plan.md`;
  `experiments/E053-r5-order-fifteen-classification-formalization-result.md`;
  `artifacts/e053_lean_build.log`; and E048--E052's previously audited
  theorems.
- Verifiers: a fresh mirror whose local build directory was absent before the
  run; all 1,311 Lean 4.32.0/mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997` jobs; all 175 exported-theorem
  assumption queries; zero-warning check; a sixteen-file source-safety scan;
  and a byte-identical post-run source comparison. Every theorem uses only a
  subset of `propext`, `Classical.choice`, and `Quot.sound`; one Boolean helper
  uses no axioms.
- Hashes: `OrderFifteenStructure.lean` is 58,729 bytes with SHA-256
  `985ac581e9bc8eaf03c01c77a406b8a3ce2c2f4e673dbaf4f7c28f6a42071324`;
  the 21,125-byte audit transcript is
  `1103a990aa6d3eb4638848c4d7050d355625ba007ace27d3b11167708dfb6b6a`;
  and the strict audit runner is
  `6000ce825353d63269c29c604833f611534ff1d9b208a5b6a2c4e6f7bcb999d6`.
- Caveat: this does not prove the complete independence-four obstruction
  (now separately discharged by E054), import the special-Brooks certificates
  into Lean, or prove edge equalization unconditionally (now separately
  kernel-checked by E055 from the explicit special-Brooks proposition),
  or establish the final coloring contradiction. Fixed `r=5` remains a
  `CANDIDATE-RESOLUTION`; the all-`r` conjecture remains `OPEN`, and external
  fixed `r=6`--`r=9` claims are not dependencies.
- Falsifier: a fresh-build, warning, source-safety, or assumption-audit
  failure; an incorrect minimum-degree exclusion, exterior edge split,
  explicit three-coloring, equality propagation, cover-number contradiction,
  exact crossing count, residual transport, or incompatibility argument; a
  graph satisfying the stated hypotheses but violating a classification; or
  a source/artifact hash mismatch.

## C-FORMAL-009 — complete small independence-four obstruction

- Statement/scope: every finite admissible simple graph `G` with
  `G.IndepSetFree 5` has at least 62 edges at order 23, at least 59 edges at
  order 22, and at least 55 edges at order 21. Equivalently, none exists in
  the ranges `(23, <=61)`, `(22, <=58)`, or `(21, <=54)`.
- Evidence class: `machine-certified theorem` in the pinned Lean kernel. This
  discharges the complete small independence-four obstruction used by the
  audited fixed-`r=5` proof, not merely a restricted minimum-degree or
  exterior-chromatic family.
- Dependencies/location: `formal/lean/Erdos617/AlphaFourSmall.lean`;
  `formal/lean/Erdos617/Audit.lean`;
  `experiments/E054-r5-small-alpha-four-obstruction-formalization-plan.md`;
  `experiments/E054-r5-small-alpha-four-obstruction-formalization-result.md`;
  `artifacts/e054_lean_build.log`; and E048--E053's previously audited
  theorems.
- Verifiers: a fresh mirror whose local build directory was absent before the
  run; all 1,312 Lean 4.32.0/mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997` jobs; all 186 exported-theorem
  assumption queries; zero-warning check; a seventeen-file source-safety
  scan; and a byte-identical post-run source comparison. Every theorem uses
  only a subset of `propext`, `Classical.choice`, and `Quot.sound`; one Boolean
  helper uses no axioms.
- Hashes: `AlphaFourSmall.lean` is 46,530 bytes with SHA-256
  `7b97758e9150e3e67b36c78712128bb284dcff3151ad4f8d691690d44762614f`;
  the 22,678-byte audit transcript is
  `9fd72183504e12a2a405ff2212dc952736aceb2d24494535ee6aab07b803e8e4`;
  and the strict audit runner is
  `05da44f50d0e45b5e673efa51a9214da0c2d31d08dee1ffdb11ab9ae508f2ed0`.
- Caveat: this does not import the special-Brooks certificates into Lean,
  prove edge equalization unconditionally (now separately kernel-checked by
  E055 from the explicit special-Brooks proposition), eliminate the later recursive residual branches,
  or establish the final coloring contradiction. Fixed `r=5` remains a
  `CANDIDATE-RESOLUTION`; the all-`r` conjecture remains `OPEN`, and external
  fixed `r=6`--`r=9` claims are not dependencies.
- Falsifier: a fresh-build, warning, source-safety, or assumption-audit
  failure; an omitted minimum-degree or complementary-chromatic branch; an
  invalid common-avoider, equality-accounting, pointwise-degree,
  cover-number, or residual-transport argument; a graph in one of the stated
  forbidden ranges satisfying the hypotheses; or a source/artifact hash
  mismatch.

## C-FORMAL-010 — conditional edge equalization and low-degree reduction

- Statement/scope: assume `R5SpecialBrooksObstruction`, the exact proposition
  that no admissible, `CliqueFree 6`, `IndepSetFree 6`, 5-regular graph exists
  on `Fin 26`. Then every color graph of a hypothetical fixed-`r=5`
  counterexample has exactly 65 edges and minimum degree four. At a minimum
  vertex its closed neighborhood is an isolated `K5`; the exterior induced
  graph is admissible, has order 21, exactly 55 edges, no independent five-
  set, and minimum degree at least four.
- Evidence class: `machine-certified conditional theorem` in the pinned Lean
  kernel. E038/E042--E045 certificate-check every finite branch of the sole
  hypothesis, but that external LRAT result is not yet a theorem premise
  constructed inside Lean.
- Dependencies/location: `formal/lean/Erdos617/EdgeEqualization.lean`;
  `formal/lean/Erdos617/Audit.lean`;
  `experiments/E055-r5-edge-equalization-low-degree-formalization-plan.md`;
  `experiments/E055-r5-edge-equalization-low-degree-formalization-result.md`;
  `artifacts/e055_lean_build.log`; and E035 plus E048--E054's previously
  audited theorems.
- Verifiers: a fresh mirror whose local build directory was absent before the
  run; all 1,313 Lean 4.32.0/mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997` jobs; all 195 exported-theorem
  assumption queries; zero-warning check; an eighteen-file source-safety
  scan; and a byte-identical post-run source comparison. Every theorem uses
  only a subset of `propext`, `Classical.choice`, and `Quot.sound`; one Boolean
  helper uses no axioms.
- Hashes: `EdgeEqualization.lean` is 30,006 bytes with SHA-256
  `9c7105d7c12e31de458efb2b0f8a3e96708b963188379e2d81419450c3d21a98`;
  the 23,911-byte audit transcript is
  `d65ea6533a21efca3712fc96fac108fd1a2dcd45a194f1a0d2499e9dfe6b1077`;
  and the strict audit runner is
  `45a60f670b7313f8ac6a9ac6346bad2e9a935f5b3429401c143c4d5ab42072bb`.
- Caveat: the finite special-Brooks proposition remains an explicit theorem
  hypothesis until the external LRAT certificates are bridged into Lean. The
  order-21 residual minimum-degree-four branch is now separately kernel-
  checked by E056; E057 now separately checks the minimum-degree-five branch
  and final conditional coloring contradiction. Fixed `r=5` remains a
  `CANDIDATE-RESOLUTION`; the all-`r` conjecture remains `OPEN`, and external
  fixed `r=6`--`r=9` claims are not dependencies.
- Falsifier: a fresh-build, warning, source-safety, or assumption-audit
  failure; an invalid degree-zero/one exclusion; an omitted minimum degree or
  nested residual branch; an invalid accounting equality, isolated-clique
  inference, edge-sum equalization, or neighbor-set equivalence; a graph
  satisfying the hypotheses but violating a stated conclusion; or a
  source/artifact hash mismatch.

## C-FORMAL-011 — residual minimum-degree-four recursion

- Statement/scope: every finite admissible simple graph `G` with
  `G.IndepSetFree 5`, exactly 21 vertices, exactly 55 edges, and all degrees at
  least four in fact has all degrees at least five. Equivalently, a degree-
  four vertex under these exact residual hypotheses is impossible. The proof
  includes the complete nested order-16, 45-edge recursion and every
  bipartite/19-edge/20-edge order-ten complement branch.
- Evidence class: `machine-certified theorem` in the pinned Lean kernel. This
  graph theorem itself has no special-Brooks premise; composing it with E055's
  coloring reduction remains conditional on E055's explicit proposition.
- Dependencies/location: `formal/lean/Erdos617/ResidualDegreeFour.lean`;
  `formal/lean/Erdos617/Audit.lean`;
  `experiments/E056-r5-residual-degree-four-formalization-plan.md`;
  `experiments/E056-r5-residual-degree-four-formalization-result.md`;
  `artifacts/e056_lean_build.log`; and E048--E055's previously audited
  theorems.
- Verifiers: a fresh mirror whose local build directory was absent before the
  run; all 1,314 Lean 4.32.0/mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997` jobs; all 208 exported-theorem
  assumption queries; zero-warning check; a nineteen-file source-safety scan;
  and a byte-identical post-run source comparison. Every theorem uses only a
  subset of `propext`, `Classical.choice`, and `Quot.sound`; one previously
  existing Boolean helper uses no axioms. The new 1,024-code finite check uses
  transparent kernel reduction rather than `native_decide`.
- Hashes: `ResidualDegreeFour.lean` is 50,971 bytes with SHA-256
  `9bebfec6adb1cfa18f30cdc3ac88691d710ba8078741c656fce401002e55b2aa`;
  the 25,574-byte audit transcript is
  `2ba29e88cabc093ec3e49ddbc83e8075e3497e3e36f341d5535d6878dffe637e`;
  and the strict audit runner is
  `5a2281af859f920db302c1c73a2421641825ddc9046efeb23f3ff81922e39cb9`.
- Caveat: E056 does not itself eliminate the residual minimum-degree-five
  branch or compose the final conditional coloring contradiction; E057 now
  checks both. Neither result bridges the external special-Brooks certificates
  into Lean, proves fixed `r=5` unconditionally, verifies the external fixed
  `r=6`--`r=9` claims, or resolves the all-`r`
  conjecture. Fixed `r=5` remains a `CANDIDATE-RESOLUTION`; the all-`r`
  conjecture remains `OPEN`.
- Falsifier: a fresh-build, warning, source-safety, or assumption-audit
  failure; an omitted order-ten edge-count case; an invalid isolated-clique or
  degree-inheritance step; incorrect complement/cross-edge accounting; an
  unproved pointwise equality or unique-excess claim; an invalid cover
  construction or isomorphism transport; an unchecked finite enumeration; an
  invalid final six-set edge count; a graph satisfying the stated hypotheses
  with a degree-four vertex; or a source/artifact hash mismatch.

## C-FORMAL-012 — final residual recursion and conditional fixed-r=5 upper theorem

- Statement/scope: no finite admissible simple graph with exactly 21
  vertices, exactly 55 edges, no independent five-set, and minimum degree at
  least four exists. The proof exhausts the three-colorable exterior and all
  35/36-edge order-fifteen structures. Consequently
  `R5ColorGraphResidualStructure G` is impossible for every color graph. As a
  separate composition, `R5SpecialBrooksObstruction` implies nonexistence of
  a `Fin 26` five-color counterexample, `R5Upper`, and `Problem617At 5`.
- Evidence class: `machine-certified theorem` for the graph-level residual
  impossibility and `machine-certified conditional theorem` for the fixed-
  `r=5` coloring statements. The sole mathematical premise of the latter is
  visible in their types as `R5SpecialBrooksObstruction`.
- Dependencies/location: `formal/lean/Erdos617/ResidualDegreeFive.lean`;
  `formal/lean/Erdos617/Audit.lean`;
  `experiments/E057-r5-residual-degree-five-formalization-plan.md`;
  `experiments/E057-r5-residual-degree-five-formalization-result.md`;
  `artifacts/e057_lean_build.log`; and E048--E056's previously audited
  theorems.
- Verifiers: a fresh mirror whose local build directory was absent before the
  run; all 1,315 Lean 4.32.0/mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997` jobs; all 223 exported-theorem
  assumption queries; zero-warning check; a twenty-file source-safety scan;
  and a byte-identical post-run source comparison. Every theorem uses only a
  subset of `propext`, `Classical.choice`, and `Quot.sound`; one previously
  existing Boolean helper uses no axioms.
- Hashes: `ResidualDegreeFive.lean` is 52,585 bytes with SHA-256
  `ab284c3e0f493fb61d4d467469da4d883b7feb40cb792f08b1feaaca90843c2f`;
  the 27,439-byte audit transcript is
  `328d40d482fcc8b5bce6b52f2c7bbeef4f7ca49e207531bffbd17c0ee7e410ce`;
  and the strict audit runner is
  `eb35541c4272abb099f8075f51359f5c9da530c205863733c95cbd684949fc07`.
- Caveat: E057 does not prove `R5SpecialBrooksObstruction`. E038 and
  E042--E045 separately certificate-check all its finite branches, but a
  kernel-checkable bridge has not yet constructed that proposition in Lean.
  Fixed `r=5` therefore remains a `CANDIDATE-RESOLUTION`, external fixed
  `r=6`--`r=9` claims remain unverified here, and the all-`r` conjecture
  remains `OPEN`.
- Falsifier: a fresh-build, warning, source-safety, or assumption-audit
  failure; an omitted 35/36-edge or E053 structural alternative; an invalid
  common-avoider, unique-cross-endpoint, pointwise equality, unique-excess,
  cover-transport, or six-set argument; a graph satisfying the exact residual
  hypotheses; a conditional coloring theorem whose type hides an additional
  premise; or a source/artifact hash mismatch.

## C-FORMAL-013 — E058 special-Brooks certificate-to-Lean bridge

- Statement/scope: the complete 26-branch E038/E042--E045 special-Brooks
  obstruction is a theorem in the pinned Lean kernel. In particular,
  `e058R5SpecialBrooksObstruction : R5SpecialBrooksObstruction` has no
  project-defined premise. The bridge covers exactly the finite obstruction
  required by E055--E057; it does not certify E047's broader order-24/25
  formulas or any fixed \(r=6,\ldots,9\) claim.
- Evidence class: `machine-certified theorem`.
- Dependencies/location:
  `formal/lean/E058SpecialBrooksCoverage.lean`;
  `formal/lean/E058E038Coverage.lean`;
  `formal/lean/E058E042Coverage.lean`;
  `formal/lean/E058E042DirectCoverage.lean`;
  `formal/lean/E058E043P04Coverage.lean`;
  `formal/lean/E058E043P09Coverage.lean`;
  `formal/lean/E058E043P19Coverage.lean`;
  `formal/lean/E058E045Coverage.lean`;
  `formal/lean/Erdos617/Sat/`;
  `formal/lean/generated/e058_fresh_kernel/`;
  `formal/lean/generated/e058_fresh_semantic/`;
  `artifacts/e058_special_brooks_kernel_bridge/fresh_audit/`;
  `artifacts/e058_special_brooks_kernel_bridge/exact_head_fresh_audit/`; and
  `REPRODUCE_E058.md`.
- Verifiers: deterministic regeneration of all 89 source unit CNFs; exact
  extraction of 89 RUP-only cores; independent acceptance by the pinned C
  checker and Python checker; 356 negative certificate checks; all 89 staged
  kernel imports; all 89 semantic closures; eight final coverage modules; and
  192 explicit theorem-assumption queries. The final source and output scans
  report zero warnings and zero forbidden constructs. The terminal assumption
  set is exactly `propext`, `Classical.choice`, and `Quot.sound`.
- Hashes: clean-start audit receipt
  `d1b00435407e6811bb5e128bb5dbdc953e0a71ba01dacacc2b999b7b7a1bbddd`;
  validated clean-start sequence receipt
  `fe098ddd671c090586fe17d1d719e82edc3d4be8bc6b625234d78107b328d665`;
  hardened final-source audit receipt
  `7aa6cf6d38d3a38f1fa42867d15c1ebd48a8d6e191a35e69c37aff0fac6c0326`;
  uninterrupted exact-HEAD final-source audit receipt
  `789acb2bc829fcba0a5656fabca5a37d9d4fdd2b493858039ad0081cc37032d1`;
  exact-HEAD kernel aggregate receipt
  `57f39d08fb019d2d211c3e95013d6a998ad8aa9b17e8e65f04866ba84c7ec29d`;
  exact-HEAD semantic aggregate receipt
  `5e366f024444474f74483baa257661819a279263e8ee57d71f1d9350c9abe6b4`;
  51-file final source-inventory SHA-256
  `6a14c6b7443e13d2a2769c013825beddee54e53d07c493e1306638d05cc1371d`;
  466-file generated-Lean combined SHA-256
  `c79bbd0b3deea2af4ed0c95cd15566c8c708b146ee2f5100b8256230dcb04b8e`;
  historical evidence-collection receipt
  `3a6613e93d4620d9a66b0fd1fe97405062d977d53a5aa335dff45afc05cd0a1b`;
  and exact-HEAD evidence-collection receipt
  `2f9a1d9e4027998eb3405a2db92f2130886f4eac7fd3137c4db36325eee7c047`.
- Reproduction qualification: the raw clean-start audit passed. The hardened
  final-source driver first completed its proof checks and then failed while
  assembling its JSON receipt because of a `NameError`; that failure and
  driver are retained. After the receipt bug was fixed, the final run resumed
  after the expensive core replay and repeated source/object validation,
  coverage compilation, semantic validation, and all assumption queries. Its
  receipt explicitly records `fresh_local_build=false` and
  `resumed_after_core_replay=true`. A later run from the exact committed final
  source compiled the C checker before launch, began with no local Lean build,
  and completed in one uninterrupted process. Its receipt records
  `fresh_local_build=true`, `resumed_after_core_replay=false`, all 89
  core/kernel/semantic checks, all 192 assumption queries, zero warnings, and
  zero forbidden hits. Two preceding exact-source attempts are retained as
  infrastructure diagnostics: one was externally terminated at the
  command-session boundary, and one stopped before core replay because the C
  checker prerequisite had not been built. Neither produced a terminal
  receipt.
- Diagnostic caveat: the separate preregistered raw branch-02 timing run hit
  the fixed 300-second timeout (status 124), at 310.08 user seconds, 7.57
  system seconds, and 5,924,372 KiB maximum RSS. The reduced side was not run
  and no speedup ratio is claimed. This is a failed performance diagnostic,
  not a theorem premise; branch 02 is included among the 89 dual-checked,
  kernel-imported cores.
- Falsifier: a regenerated source-CNF, core, staged-module, semantic-closure,
  assumption-output, or inventory mismatch; acceptance of a deliberate
  corruption; a hidden project axiom or unsafe construct; failure of any
  coverage theorem; or a source/artifact hash mismatch.

## C-R5-002 — machine-verified fixed-r=5 theorem

- Statement/scope: every five-coloring of the edges of \(K_{26}\) has six
  vertices whose induced \(K_6\) omits a color. In the repository's exact
  formulation:

  ```lean
  theorem e058Problem617AtFive : Problem617At 5
  ```

  This is an unconditional theorem in the pinned Lean environment and supports
  `MACHINE-VERIFIED-RESOLUTION` for fixed \(r=5\) only.
- Evidence class: `machine-certified theorem`; not an externally reviewed
  theorem.
- Mathematical attribution: the proof architecture and original mathematical
  argument are attributed to Robert Sneiderman's pinned Robby955 preprint at
  commit `735c2eeffcb5c8abe92f8a6be04be2fa3c8bb6ab`. This project's contribution
  is an independent formalization, certificate replay, kernel bridge,
  assumption audit, and reproducibility record.
- Dependencies/location: `C-FORMAL-001` through `C-FORMAL-013`;
  `formal/lean/E058SpecialBrooksCoverage.lean`;
  `experiments/E058-r5-special-brooks-kernel-bridge-result.md`;
  `paper/main.tex`; and `REPRODUCE_E058.md`.
- Verifiers: the E058 verifier inventory in `C-FORMAL-013`, plus the
  previously audited E034--E057 dependency chain and the definitional
  identification `Problem617At 5 ↔ R5Upper`.
- Caveat: this does not prove `Problem617`, does not verify fixed
  \(r=6,\ldots,9\), and has not received qualified independent human review.
  Codex provided material AI assistance; the exact disclosure is in
  `AI_USAGE.md`. The failed branch-02 performance benchmark is disclosed but
  does not weaken the logical theorem.
- Falsifier: any falsifier of `C-FORMAL-001` through `C-FORMAL-013`; a hidden
  premise in the final theorem's type; an assumption-audit mismatch; an
  invalid identification of `Problem617At 5` with the fixed five-color upper
  statement; or a reproducibility/hash failure.
