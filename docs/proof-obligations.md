# Proof obligations

## Decisive obligations

- `PO-001 DISCHARGED AT FIXED-r=5 MACHINE-VERIFIED SCOPE`: E033
  independently audited the complete unrestricted r=5 manuscript and E058
  completed the kernel-checkable certificate bridge. Lean now exports
  `Erdos617.e058Problem617AtFive : Problem617At 5` unconditionally. This does
  not discharge the all-r conjecture and is not an external-review claim.
- `PO-002 OPEN`: prove that any decomposition or symmetry break used by a future
  exact search retains an orbit representative and audit branch coverage with an
  independent implementation.
- `PO-003 DISCHARGED`: kernel-check the E033 r=5 proof, including
  its original coloring statement, every graph translation, the specialized
  Kang--Pikhurko dependency, all endpoint lemmas, and the final theorem, without
  `sorry`, `admit`, accidental axioms, or unchecked native computation.
  E034--E035 have kernel-checked the exact statement, graph translations,
  affine lower construction, local and Turán bounds, degree-zero exclusion,
  neighborhood accounting/equality, and the reduction to a finite special-
  Brooks hypothesis. E048 adds the large independence-two terminal lemma, and
  E049 kernel-checks its propagation through all six large numerical
  independence-three/four bounds used under admissibility. E050 directly
  kernel-checks the order-eleven 36-edge endpoint, and E051 kernel-checks the
  complete order-ten structure endpoint. E052 kernel-checks the complete
  small independence-three obstruction at orders 16--18, and E053
  kernel-checks both order-fifteen near-extremal classifications. E054
  kernel-checks the complete small independence-four obstruction at orders
  21--23. Conditional on the explicit finite special-Brooks proposition, E055
  kernel-checks edge equalization, both low-degree exclusions, and the first
  isolated-`K5` residual reduction. E056 then kernel-checks the complete
  residual minimum-degree-four branch and proves that the exact order-21,
  55-edge residual has minimum degree at least five. E057 kernel-checks the
  complete minimum-degree-five branch, makes the exact residual impossible,
  and proves `R5Upper` and `Problem617At 5` conditional only on the explicit
  special-Brooks proposition.
  E038 and E042--E045 certify all 26 exact neighborhood branches. E058 imports
  all 89 zero-RAT cores through staged Lean theorems, proves all 89 exact graph
  semantics, checks the complete relabeling/orbit/sorting coverage, derives
  `R5SpecialBrooksObstruction`, and composes the unconditional fixed-r=5
  theorem. The clean-start and hardened final audits report 89 kernel imports,
  89 semantic closures, eight coverage modules, 192 assumption queries, zero
  warnings, and zero forbidden-source hits.
- `PO-023 DISCHARGED AND IMPORTED INTO LEAN`: the explicit E035 finite special-Brooks hypothesis is
  certificate-checked. The 26-neighborhood orbit split is independently
  exhaustive. E038 certifies branches 00--18; E042--E043 certify branch 19;
  and E045 certifies branches 20--25. All 89 formulas regenerate, all LRATs
  are zero-RAT and pass two independent checkers, and all 356 deliberate
  corruptions are rejected. E058 additionally imports every reduced proof into
  Lean and proves the exact formula-to-graph and symmetry bridge; no finite
  neighborhood branch or kernel bridge remains open. E036--E041 and E044
  `UNKNOWN` runs remain non-evidence.
- `PO-024 DISCHARGED AT THE REQUIRED PROOF SCOPE`: replace the six large
  Kang--Pikhurko numerical specializations used by the r=5 manuscript. E049
  kernel-checks an admissibility-specific propagation from E048 and proves the
  four required independence-three bounds 56, 62, 69, and 76 at orders 19--22
  and the two required independence-four bounds 65 and 71 at orders 24--25.
  E047's four broader zero-RAT LRATs remain independent cross-checks rather
  than premises. Its broad order-24/25 formulas without admissibility remain
  `UNKNOWN`, but those stronger statements are not required by this proof
  route. E050 and E051 separately discharge orders eleven and ten; the
  order-15 endpoints are separately discharged by E053.
- `PO-025 DISCHARGED`: kernel-check the large admissible independence-two
  terminal bound. E048 proves complement maximum degree at most five, at most
  four from order twelve, and `choose n 2 <= e(F) + 2n`. A clean warning-free
  build audits all 70 exported theorems and finds only the allowed Lean
  foundations. E050 and E051 separately discharge orders eleven and ten.
- `PO-026 DISCHARGED`: kernel-check the order-eleven independence-two terminal
  endpoint. E050 proves directly that every admissible order-eleven graph with
  no independent triple has at least 36 edges. It formalizes degree-five
  exclusion, the degree-four handshaking choice, exact crossing and exterior
  edge counts, complementary two-subset labels, and an explicit label-collision
  six-set contradiction. A source-identical warning-free 1,297-job build and
  all 105 theorem assumption queries pass using only the three allowed Lean
  foundations. No E033 catalog, SAT result, or Kang--Pikhurko premise enters
  the theorem. E051 separately discharges the order-ten structure theorem.
- `PO-027 DISCHARGED`: kernel-check the complete order-ten structure endpoint.
  E051 proves the balanced bipartite branch, the nonbipartite twenty-edge cap,
  the unique balanced two-fold `C5` blow-up at equality, the nineteen-edge
  independence-five consequence, and the canonical blow-up's exact
  independence number and minimum-cover classification. A fresh local-build-
  free mirror completes 1,309 jobs and 152 theorem assumption queries with no
  warnings, forbidden source constructs, catalog premise, SAT result, or
  foundations beyond `propext`, `Classical.choice`, and `Quot.sound`.
- `PO-028 DISCHARGED`: kernel-check the complete small independence-three
  obstruction. E052 proves that every admissible graph with no independent
  four-set has at least 45, 50, and 54 edges at orders 16, 17, and 18. The
  order-sixteen degree-five endpoint exhausts both E051 structures: the
  bipartite branch forces a forbidden six-clique, while exact accounting in
  the nonbipartite branch produces a vertex cover of size at most five in a
  graph whose cover number is six. A fresh local-build-free mirror completes
  1,310 jobs and 159 theorem assumption queries with no warnings, forbidden
  source constructs, catalog premise, SAT result, Kang--Pikhurko premise, or
  foundations beyond `propext`, `Classical.choice`, and `Quot.sound`.
- `PO-029 DISCHARGED`: kernel-check both order-fifteen near-extremal
  classifications. E053 proves the exact 35-edge isolated-five-clique and
  canonical doubled-`C5` residual structure. At 36 edges it proves an
  exclusive alternative between exactly one edge leaving such a five-clique
  and an isolated five-clique with a triangle-free nineteen-edge residual
  complement having no independent five-set. A separate theorem proves the
  alternatives incompatible. A fresh local-build-free mirror completes 1,311
  jobs and 175 theorem assumption queries with no warnings, forbidden source
  constructs, catalog premise, SAT result, Kang--Pikhurko premise, or
  foundations beyond `propext`, `Classical.choice`, and `Quot.sound`.
- `PO-030 DISCHARGED`: kernel-check the complete small independence-four
  obstruction. E054 proves that every admissible graph with no independent
  five-set has at least 62, 59, and 55 edges at orders 23, 22, and 21. The
  order-21 degree-five endpoint proves the needed order-fifteen 35-edge lower
  bound directly, exhausts both complementary chromatic branches, and closes
  the exact non-three-colorable case with E053's isolated-five-clique
  structure and E051's canonical cover number six. A fresh local-build-free
  mirror completes 1,312 jobs and 186 theorem assumption queries with no
  warnings, forbidden source constructs, catalog premise, SAT result,
  Kang--Pikhurko premise, or foundations beyond `propext`,
  `Classical.choice`, and `Quot.sound`.
- `PO-031 DISCHARGED AS A KERNEL-CHECKED IMPLICATION`: conditional only on the
  explicit finite special-Brooks proposition, kernel-check edge equalization,
  exclude minimum degrees two and three, and reach the exact first residual.
  E055 proves every color has 65 edges; recursively peels the forced isolated
  `K3` and `K4` equality cases; and proves that every color graph is an
  isolated `K5` plus an admissible order-21, 55-edge residual with no
  independent five-set and minimum degree at least four. An explicit
  neighbor-set equivalence proves residual degree inheritance. A fresh local-
  build-free mirror completes 1,313 jobs and 195 theorem assumption queries
  with no warnings, forbidden source constructs, graph-catalog premise, SAT
  premise, Kang--Pikhurko premise, or foundations beyond `propext`,
  `Classical.choice`, and `Quot.sound`. This does not discharge the distinct
  certificate-to-Lean bridge for its special-Brooks hypothesis.
- `PO-032 DISCHARGED`: kernel-check the minimum-degree-four branch of E055's
  exact order-21 residual. E056 forces an isolated `K5`, reduces to an exact
  order-16, 45-edge residual, excludes its degree-four branch with E050, and
  closes the bipartite, 19-edge, and both 20-edge order-ten complement cases.
  The endpoint proof includes a transparent 1,024-code five-edge certificate,
  pointwise cross-degree equality/excess accounting, isomorphism transport of
  E051's minimum-cover intersection theorem, the forced `K1,4`, and the final
  six-set with only one complementary edge. A fresh local-build-free mirror
  completes 1,314 jobs and 208 theorem assumption queries with no warnings,
  forbidden source constructs, catalog premise, SAT premise, unchecked native
  computation, or foundations beyond `propext`, `Classical.choice`, and
  `Quot.sound`. The exact residual therefore has minimum degree at least five;
  its degree-five branch is separately discharged by E057.
- `PO-033 DISCHARGED AS A KERNEL-CHECKED IMPLICATION`: kernel-check the
  residual minimum-degree-five branch, compose it with E056, and derive the
  fixed-`r=5` upper statement conditional only on
  `R5SpecialBrooksObstruction`. E057 exhausts the three-colorable exterior,
  both 35-edge internal-neighborhood cases, and both 36-edge E053 structures.
  It checks pair-specific clique avoiders, the one-cross-edge endpoint,
  pointwise equality and unique excess, the forced `K1,4`, minimum-cover
  transport, and the final fourteen-edge six-set. A fresh local-build-free
  mirror completes 1,315 jobs and 223 theorem assumption queries with no
  warnings, forbidden source constructs, catalog premise, SAT premise,
  unchecked native computation, or foundations beyond `propext`,
  `Classical.choice`, and `Quot.sound`. The graph-level residual impossibility
  is unconditional at its stated hypotheses. The E057 coloring theorems
  visibly retain `R5SpecialBrooksObstruction`; E058 now proves that proposition
  and composes the unconditional final theorem.
- `PO-034 DISCHARGED`: bridge the complete special-Brooks certificate
  inventory into the pinned Lean kernel. E058 deterministically regenerates
  89 backward RUP cores from the committed sources, checks all 89 with the C
  and Python checkers, rejects 356 corruptions, proves 89 staged kernel
  theorems and 89 graph-semantic closures, and closes all 26 canonical
  branches through eight coverage modules. The final theorem's exact audited
  assumptions are `propext`, `Classical.choice`, and `Quot.sound`.

## Highest-value mathematical obligations

- `PO-035 OPEN — HIGHEST PRIORITY AFTER THE LOCAL E058 REVIEW GATE`: prove or
  refute the all-\(r\) conjecture. Treat the upstream fixed \(r=6,\ldots,9\)
  packages as provisional prior work and mine them only for structural lemmas
  that can support a uniform argument. Prioritize scalable reductions for
  \(r\ge10\) and arbitrary \(r\), rather than accumulating isolated
  fixed-case formalizations. No such general result is claimed in this
  checkpoint.
- `PO-004 DISCHARGED`: local counts through 209 are excluded. E006--E013 cover
  the lower profiles. E014 adds the complete exact-value-209 reduction and a
  neighbor-color availability lemma whose four final unsplit systems have
  independently checked zero-RAT LRATs. Thus `C-LOC-007` gives \(L(v)\ge210\).
- `PO-011 DISCHARGED`: local count 206 is classified and certified impossible.
  The order-21 proof uses the E008 lower-edge obstruction, a complete private-
  witness deletion split, all 13 doubled-group profiles, and a proved final
  point-label quotient for the self-symmetric branch.
- `PO-012 DISCHARGED`: local count 207 is classified and certified impossible.
  A proved spoke-pigeonhole lemma removes all degree-two/three branches.  The
  remaining balanced and unbalanced graphs are covered by the E011 lower-edge
  deletion split, complete private-witness encodings, proved point quotients,
  and two independently checked zero-RAT LRATs.
- `PO-013 DISCHARGED`: local count 208 is classified and certified impossible.
  The complete slack audit leaves four targets; two direct variable-graph
  proofs cover the one-exception targets, while thirteen direct classified
  proofs and one complete auxiliary-class quotient cover all fourteen actual
  double-exception branches.
- `PO-014 DISCHARGED`: classify local count 209. E014 independently enumerates
  all profiles and exact slack/penalty allocations, proves the spoke and
  order-24 eliminations, audits all deletion bridges and equality branches,
  and leaves six targets. Existing proofs cover `balanced49` and thirteen
  classified branches. Four unsplit availability relaxations cover
  `unbalanced53`, `45/44 large_a2`, and both `50/39` branches with zero-RAT
  LRATs accepted by both checkers and all corruption tests. Therefore
  \(L(v)\ge210\).
- `PO-015 OPEN`: classify local count 210, starting with a fresh exact profile,
  penalty, and slack audit and incorporating neighbor-color availability before
  any large search. A result here would be another local strengthening only;
  it would not decide the unrestricted \(K_{26}\) formula.
- `PO-016 DISCHARGED`: exclude a 59-edge global color class. E018 combines the
  Kang--Pikhurko maximum/equality characterization, exhaustive part-vector and
  orbit audits, a direct six-set contradiction, and two redundant checked
  zero-RAT exact-coloring certificates. Thus every color has at least 60 edges.
- `PO-017 DISCHARGED`: exclude a 60-edge global color class. E027 recursively
  forces three \(K_5\) components, E028 independently classifies the sole
  11-vertex residual with a 300-label enumeration and checked zero-RAT LRAT,
  and E024 certifies the exact remaining-color extension impossible. Thus every
  color has at least 61 edges.
- `PO-018 DISCHARGED`: classify exact global color count 61. E029 eliminates
  the degree-three route, recursively handles degree four, uses Dirac's theorem
  to eliminate the 16-vertex minimum-degree-five residual, certifies exactly
  two final residual classes, and refutes both exact unrestricted extensions.
  Thus every color has at least 62 edges.
- `PO-019 DISCHARGED`: classify exact global color count 62. E030 exhausts the
  degree-three and recursive degree-four routes, eliminates the 16-vertex
  minimum-degree-five branch using Dirac and Kostochka--Yancey, certifies
  exactly four final residual classes, and refutes all four exact unrestricted
  extensions. Thus every color has at least 63 edges.
- `PO-020 DISCHARGED`: classify exact global color count 63. E031 completes the
  fresh allocation and physical-attachment audit, certifies one residual-12
  and five residual-11 classes, proves the final 16-vertex residual is itself
  6-critical, exhaustively constructs all 48 relevant three-atom 6-Ore
  classes, and refutes every exact unrestricted extension with 13 checked
  RUP-only LRATs. Thus every color has at least 64 edges.
- `PO-021 OPEN`: classify exact global color count 64. The deletion bridge now
  makes all 64 edges critical, and the average degree still forces minimum
  degree at most four. Recompute every allocation and attachment family from
  scratch; the additional unit of slack is not covered automatically by E031.
  If one color has 64 edges, the other four have excesses above 64 summing to
  five. Counts 64 and 65 are the only remaining least-color counts in the
  independent certificate chain. E032 is paused while the stronger E033 proof
  candidate is formalized; it is not marked discharged by candidate evidence.
- `PO-022 CANDIDATE`: independently reproduce the newly located unrestricted
  r=5 manuscript. E033 pinned and rebuilt the source, audited the full proof and
  imported hypotheses, and independently exhausted all order-10/order-11
  endpoints without finding a gap. The human-style audit is complete; the
  remaining obligation is exactly the PO-003 machine-verification upgrade and
  later qualified external review.
- `PO-005 OPEN`: determine the exact maximum edge count for a 26-vertex
  \(K_6\)-free graph with chromatic number at least 7 (and higher). Check whether
  the resulting chromatic-deficit profiles can sum to 50 under pairwise union.
- `PO-006 OPEN`: find a simultaneous stability theorem using both
  \(H_i\cup H_j=K_{26}\) and exact fourfold edge coverage; one-graph stability
  alone is insufficient.

## Reproduction and audit obligations

- `PO-007 OPEN`: independently certify the final tight subcase of the published
  \(r=4\) minority-graph proof and the unique eight-vertex Ramsey graph used
  there.
- `PO-008 OPEN`: inspect full text for every direct citation in the OpenAlex list
  and repeat searches in MathSciNet/zbMATH or another expert index if accessible.
- `PO-009 OPEN`: rebuild the current artifact verification in a second toolchain
  and obtain an independent qualified review before any external-verification label.
- `PO-010 OPEN`: kernel-check both equality-to-incidence bridges, symmetry
  proofs, DIMACS semantics, and LRAT results in a proof assistant. The current
  two-checker chain is machine-certified but not formally verified.
