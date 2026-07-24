# State

Checkpoint date: 2026-07-24 (Europe/Berlin)

## Exact verification level

`MACHINE-VERIFIED-RESOLUTION` for the unrestricted fixed \(r=5\) case.

The full all-\(r\) Erdős Problem #617 conjecture remains `OPEN`. The fixed
\(r=6,\ldots,9\) claims in the pinned upstream repository remain provisional
and unverified here. This checkpoint is not
`EXTERNALLY-VERIFIED-RESOLUTION`: the work has not received independent
external review, and Codex provided material AI assistance as disclosed in
`AI_USAGE.md`.

E058 closes the final fixed-\(r=5\) kernel dependency. It imports the 89
RUP-only special-Brooks cores through generated, staged Lean proofs, checks
their semantic closures, and composes the resulting unconditional
`e058R5SpecialBrooksObstruction` into `e058NoR5Counterexample`, `e058R5Upper`,
and

```lean
theorem e058Problem617AtFive : Problem617At 5
```

The final source inventory contains 51 pinned Lean files and 466 generated
Lean stage files. All 89 source CNFs were regenerated; all 89 reduced cores
were accepted independently by the pinned C checker and the independent
Python checker; all 89 kernel imports, all 89 semantic closures, eight coverage
modules, and 192 explicit assumption queries passed. The terminal assumption
set is exactly `propext`, `Classical.choice`, and `Quot.sound`, with zero
warnings and zero forbidden-source hits. The clean-start audit receipt is
`d1b00435407e6811bb5e128bb5dbdc953e0a71ba01dacacc2b999b7b7a1bbddd`;
the independently validated clean-start sequence receipt is
`fe098ddd671c090586fe17d1d719e82edc3d4be8bc6b625234d78107b328d665`;
and the hardened final-source receipt is
`7aa6cf6d38d3a38f1fa42867d15c1ebd48a8d6e191a35e69c37aff0fac6c0326`.
The final hardened run resumed after the expensive core replay following a
receipt-assembly `NameError`; it then repeated the source, object, coverage,
semantic, and assumption checks. The earlier raw clean-start run and its
exact executed driver are retained, so the distinction is auditable rather
than hidden. A later uninterrupted audit of exact commit `d19a0cf` began with
no local Lean build and passed every gate in 25,497.97 seconds. Its receipt is
`789acb2bc829fcba0a5656fabca5a37d9d4fdd2b493858039ad0081cc37032d1`
and records `fresh_local_build=true` and
`resumed_after_core_replay=false`. This is the primary exact-final-source
replay; the earlier sequence remains retained with its historical
qualification.

E034--E057 remain `PARTIAL-CERTIFIED` at the exact scope of their individual
lemmas and certificates. E058 is the bridge that turns their fixed-\(r=5\)
composition into the unconditional machine-verified theorem above. E047's
broader order-24/25 formulas without admissibility remain `UNKNOWN`, and no
claim about them is needed for `e058Problem617AtFive`.

## Repository provenance

At the start of this run the repository contained only an empty `.git` directory:
there were no commits, state files, manifests, programs, logs, certificates, or
starter archive. The only supplied file was
`C:/PUBLICATION_REDACTED_WINDOWS_HOME/Downloads/erdos617_codex_research_goal.md`. It was read in full
and copied byte-for-byte to `RESEARCH_GOAL.md`; both files had SHA-256
`efcced39953ea11107e90db91628c0cd7616f66c112cda9db8afc2a78a12b6f9`.
There were therefore no prior mathematical claims to reproduce or invalidate.

The sole active working repository was migrated on 2026-07-22 from
`/PUBLICATION_REDACTED_WINDOWS_HOME/Documents/erdos` to `/PUBLICATION_REDACTED_HOME/git/erdos` to avoid the
Windows-mounted filesystem bottleneck. The transfer covered 27,329,536,523
bytes and 131,061 entries. Before new work, both copies had commit
`b78522bf7e0621b4586b3a0679189e3c167f17cd` and the same working-tree status;
`git fsck --no-dangling` passed in the destination, and a full checksum dry run
reported no semantic difference after excluding only the mutable Git index
and directory timestamps. The Windows copy remains untouched as a fallback,
but all subsequent commands and commits use `/PUBLICATION_REDACTED_HOME/git/erdos`.

## Newly certified scope

1. The executable \(r=5\) semantics and strict plain-text coloring format are
   implemented independently in Python and C.
2. `artifacts/affine25.col` is a five-coloring of \(K_{25}\) in which every
   six-set sees all five colors. Both checkers enumerated all 177,100 six-sets.
   This is a sharpness example on 25 vertices, not a \(K_{26}\) counterexample.
3. That exact affine coloring cannot be extended by adding one vertex while
   preserving the six-set property. The proof uses only colors 0 and 1 and two
   orthogonal partitions into five monochromatic \(K_5\)'s. The finite premises
   are checked in `artifacts/affine_nonextension.json`.
4. Every hypothetical balanced five-coloring of \(K_{26}\) satisfies the
   local Turán/triangle inequality in Claim `C-TRI-001`. Its finite arithmetic
   was exhaustively audited over every ordered five-part composition of 25.
5. Equality in that original local bound is impossible. A human reduction maps any
   equality configuration to a 400-variable incidence CNF; the committed LRAT
   certificate proves that weaker local incidence system UNSAT. A pinned
   upstream C checker and an independent Python RUP checker both accept the
   certificate and reject two deliberate corruptions each. Consequently every
   vertex has local count at least 201, strengthening the global triangle
   constraint to `C-EQ-001`.
6. A new four-partite escape lemma forces at least one non-four-partite local
   complement, while every local complement of order at least 21 is
   non-four-partite. Applying all forced penalties from the imported
   Kang--Pikhurko extremal theorem and auditing all 23,751 degree profiles gives
   \(L(v)\ge204\), with unique equality profile \((5,5,5,5,5)\).
7. The six relevant balanced E006 representatives exclude equality at 204 by
   deterministic necessary-incidence CNFs and RUP-only LRAT certificates,
   proving \(L(v)\ge205\). E006 also certifies two superseded order-19 systems
   from the earlier weaker arithmetic catalog.
8. E008 independently catalogs and certifies all eight exact order-21
   Kang--Pikhurko branches at unbalanced local count 205.
9. E009 leaves the remaining balanced 45-edge exceptional graph completely
   variable. Its 11,079-variable, 127,686-clause necessary system is certified
   UNSAT by a 1,443,988,824-byte RUP-only LRAT checked directly against the full
   CNF by both independent checkers. The graph/subset/block clauses, core
   inclusion, and deliberate corruptions are independently audited.
   Consequently \(L(v)\ge206\), hence \(B+3R\ge5356\),
   \(2R-M\ge2756\), and \(3M\ge2E+156\). This is not an unrestricted
   \(K_{26}\) UNSAT result.
10. E011 exhausts local count 206. Twelve fixed order-22 extremal systems, the
    full balanced 46-edge variable system, and thirteen exhaustive order-21
    edge-minimal composition branches all have RUP-only LRAT certificates. The
    order-21 deletion split reuses the certified E008 49-edge obstruction; the
    self-symmetric `0111` branch uses a proved free-`A_1` label quotient.
    Consequently \(L(v)\ge207\), hence \(B+3R\ge5382\),
    \(2R-M\ge2782\), and \(3M\ge2E+182\). This remains a local necessary
    theorem, not an unrestricted \(K_{26}\) UNSAT result.
11. E012 exhausts local count 207. A spoke-pigeonhole lemma eliminates every
    nominal degree-two and degree-three family. The remaining balanced 47-edge
    and unbalanced 51-edge variable systems are reduced by the certified E011
    lower-edge theorem to private-witness graphs; complete point quotients and
    forced compositions leave two monolithic CNFs with independently checked
    zero-RAT LRAT certificates. Consequently \(L(v)\ge208\), hence
    \(B+3R\ge5408\), \(2R-M\ge2808\), and \(3M\ge2E+208\). Twelve fixed
    certificates produced before the spoke simplification are valid but
    redundant. This remains a local theorem, not an unrestricted \(K_{26}\)
    UNSAT result.
12. E013 exhausts local count 208. Exact profile arithmetic has no value 208;
    complete slack allocation and a strengthened spoke-pigeonhole use leave
    two one-exception and two double-exception targets. The one-exception
    variable systems have direct certificates. The actual double targets split
    exhaustively into fourteen Kang--Pikhurko equality-template branches after
    eight templates with an immediate color \(K_6\) are removed; thirteen
    direct branches and one complete true-twin representation quotient have
    independently checked zero-RAT LRATs. Consequently \(L(v)\ge209\), hence
    \(B+3R\ge5434\), \(2R-M\ge2834\), and \(3M\ge2E+234\). This remains a
    local theorem conditional on the imported extremal characterization, not
    an unrestricted \(K_{26}\) UNSAT result.
13. E014 has a certified complete reduction of local count 209 to six targets.
    The balanced 49-edge one-exception target and thirteen of the sixteen
    exhaustive classified double branches have independently checked zero-RAT
    LRATs. A new neighbor-color availability lemma supplies necessary clauses
    for all 885,500 neighbor-six-set/color pairs. Four unsplit availability
    systems cover the unbalanced 53-edge target, the `45/44 large_a2` branch,
    and both `50/39` branches. Their zero-RAT LRATs have 5,077, 5,328, 10,936,
    and 2,462 additions; both independent checkers accept every proof, all
    sixteen corruptions are rejected, and all compressed round trips pass.
    Consequently \(L(v)\ge210\), hence \(B+3R\ge5460\),
    \(2R-M\ge2860\), and \(3M\ge2E+260\). This remains a local theorem
    conditional on the imported extremal characterization, not an unrestricted
    \(K_{26}\) UNSAT result. The deep counter trees are redundant corroboration,
    not theorem premises.
14. The exact unrestricted E007 \(K_{26}\) CNF was generated and independently
    clause-audited, but its capped CaDiCaL run returned `UNKNOWN/TIMEOUT`.
    It supplies no existence or nonexistence evidence.
15. The elementary simultaneous-complement reductions are independently proved.
16. The published \(r=3\) proof has been reconstructed and independently checked
   at the human-proof level. The final tight subcase of the published \(r=4\)
   proof is reconstructed but not yet independently certified; it remains an
   explicit obligation rather than trusted evidence.
17. E018 excludes every 59-edge color class. The Kang--Pikhurko maximum and
    equality characterization leave two all-five-part templates; each has a
    direct target-part six-set contradiction. Two exact full-color CNFs provide
    redundant zero-RAT LRAT corroboration. Thus every color class has at least
    60 edges.
18. E027--E028 and E024 exclude every 60-edge color class. Deletion/recoloring
    makes every edge critical. Exact degree arithmetic recursively forces three
    isolated \(K_5\)'s; an independent 300-label enumeration and a zero-RAT
    classification certificate leave one 11-vertex \(C_5\)-blow-up residual.
    The exact full-color extension of the resulting sole graph class has a
    second zero-RAT LRAT. Consequently every color class has at least 61 edges.
    This is a global necessary theorem, not a full \(K_{26}\) decision.
19. E029 excludes every 61-edge color class. Its exhaustive critical-graph
    reduction eliminates the degree-three route and forces three isolated
    \(K_5\)'s on the degree-four route. Dirac's critical-graph edge bound
    eliminates the only 16-vertex residual alternative. Independent physical-
    adjacency orbits of sizes 600 and 300 and a zero-RAT classification LRAT
    leave exactly two 11-vertex residual classes; exact unrestricted extension
    LRATs exclude both resulting 61-edge color graphs. Consequently every
    color class has at least 62 edges. This remains a global necessary theorem,
    not a full \(K_{26}\) decision.
20. E030 excludes every 62-edge color class. Its degree-three reduction ends
    in an elementary 5-regular triangle-free complement contradiction. Its
    recursive degree-four reduction audits every equality and slack attachment
    template; Dirac and Kostochka--Yancey eliminate the 16-vertex
    minimum-degree-five branch. Four disjoint fixed-vertex residual orbits,
    totaling 14,400 labeled graphs, are exhaustive by a checked zero-RAT LRAT,
    and four further zero-RAT LRATs exclude their exact unrestricted
    extensions. Consequently every color class has at least 63 edges. This is
    still a global necessary theorem, not a full \(K_{26}\) decision.
21. E031 excludes every 63-edge color class. A fresh critical-attachment
    reduction leaves one variable-component family, one residual-12 class,
    five residual-11 classes, and a final 16-vertex minimum-degree-five branch.
    An exact excess audit proves the whole final residual is 6-critical;
    Kostochka--Yancey equality then makes it 6-Ore. Exhaustive DHGO composition
    gives exactly 48 relevant order-16 classes, independently matched by
    nauty. Thirteen zero-RAT LRATs certify all residual catalogs and exact
    unrestricted extensions. Both checkers accept every proof, all 52
    deliberate corruptions are rejected, and all 26 compressed round trips
    pass. Consequently every color class has at least 64 edges. Counts 64 and
    65 and the complete \(K_{26}\) decision remain open.
22. E033 pins and audits `Robby955/erdos-617-fixed-cases` at commit
    `735c2eeffcb5c8abe92f8a6be04be2fa3c8bb6ab`. The complete r=5 TeX source and
    Kang--Pikhurko dependency were read, every proof step and degree table was
    reconstructed, and the source rebuilt cleanly. An independent checker
    exhausts all 12,172 nonisomorphic triangle-free order-10 graphs, all 6,153
    relevant order-11 graphs, all 20 endpoint equality templates, the cover
    facts, and all 177,100 affine six-sets. No gap was found. At that E033
    checkpoint the unrestricted r=5 theorem was a `CANDIDATE-RESOLUTION`
    because no complete kernel proof was yet present; E058 later supersedes
    that fixed-case label. The external r=6--9 claims remain unaudited here,
    and the all-r problem remains open.
23. E034 pins Lean 4/mathlib `v4.32.0`, rebuilds all project modules cleanly,
    and audits all 43 exported theorems. The kernel checks the exact finite
    coloring model, color-graph/complement bridges, relabeling invariance,
    affine `K₂₅` lower construction, complementary chromatic-product lemma,
    local one-to-eleven bound, global edge partition, Turán 55-edge bound, and
    the fact that a 55--65-edge least color graph cannot have an isolated
    vertex. The audit reports only `propext`, `Classical.choice`, and
    `Quot.sound`, and no project-defined axiom or imported Brooks or
    Kang--Pikhurko assumption. The missing Brooks/Kang--Pikhurko and later
    structural modules prevent any resolution-level promotion.
24. E035 extends the same pinned Lean project with exact open-neighborhood
    crossing/internal edge counts, the minimum-degree inequalities
    (X+2Y\ge d(d-1)), (Y\le\binom d2), and
    (X+Y\ge\binom d2), the degree-five admissibility bounds, the isolated-
    clique equality case, the independent-set/colorability bridge, and the
    5-regular handshake reduction. A fresh 1,285-job build and all 64 exported-
    theorem assumption queries pass with only Lean's standard logical
    assumptions. The special-Brooks statement remains an explicit theorem
    parameter in Lean. E038 independently audits the 26 neighborhood orbits
    and exterior-pattern quotient, then certifies branches 00--18 with 19
    exact zero-RAT LRATs, two checkers, 76 corruption rejections, and hash
    round trips.
25. E042's exact `S4 x S20` cross-pattern split and E043's complete residual
    anchor split certify neighborhood branch 19 with 17 direct and 47 residual
    zero-RAT LRATs. E045 corrects a preregistered cross-stub arithmetic error
    before search, proves a zero exterior row exists in each remaining type,
    and uses one orbit-retaining anchor quotient to certify branches 20--25
    with six more LRATs. The 70 new formulas regenerate exactly; both checkers
    accept every proof and reject 280 deliberate corruptions. Combined with
    E038, all 26 neighborhood types have 89 certificates and 356 corruption
    rejections. E044's six `UNKNOWN` searches remain non-evidence. This
    discharges only the finite special-Brooks hypothesis, not fixed r=5 or the
    all-r conjecture.
26. E046 gives independently audited unquotiented formulas for the six broad
    Kang--Pikhurko specializations used by the r=5 manuscript. All six capped
    searches returned `UNKNOWN`; the formulas and receipts are retained as an
    exact search boundary and no theorem is inferred from those runs.
27. E047 proves an orbit-retaining average-degree anchor: under the contradictory
    edge cap, a low-degree vertex may be labelled zero and its neighbors placed
    first. Four anchored formulas are certified UNSAT by zero-RAT LRATs, giving
    the broad order 19--22 bounds 56, 62, 69, and 76 for graphs with
    independence number at most three and clique number at most five. Both
    checkers accept all four proofs, reject 16 deliberate corruptions, and all
    twelve E046/E047 parent and anchored formulas regenerate exactly. The order-24 and order-25 independence-
    four searches remain `UNKNOWN`; the certificate result is not yet imported
    into Lean.
28. E048 kernel-checks the manuscript's large independence-two terminal lemma.
    For every admissible finite graph with no independent triple, its complement
    has maximum degree at most five; from order twelve it has maximum degree at
    most four, so the original graph has at least `choose n 2 - 2n` edges. A
    clean 1,294-job build and all 70 theorem assumption queries are warning-free
    and use only `propext`, `Classical.choice`, and `Quot.sound`. This proves one
    terminal layer; E050 and E051 separately handle orders eleven and ten,
    while the full r=5 theorem remains outside E048.
29. E049 kernel-checks the propagation from that terminal layer. It proves the
    exact three-way edge partition at a vertex, inheritance of admissibility by
    induced subgraphs, exterior reduction from `IndepSetFree (k+1)` to
    `IndepSetFree k`, a minimum-vertex average-degree bound, and the combined
    exterior/degree/binomial edge inequality. Consequently admissible graphs
    with no independent four-set have edge lower bounds 54, 56, 62, 69, 76,
    83, and 90 at orders 18 through 24, and admissible graphs with no
    independent five-set have lower bounds 65 and 71 at orders 24 and 25. This
    covers all six large numerical uses in the audited r=5 proof without
    Kang--Pikhurko, SAT, or the E047 LRATs. A clean 1,296-job build and all 90
    theorem assumption queries are warning-free and use only the three allowed
    Lean foundations. E050 and E051 below separately discharge orders eleven
    and ten, and E053 separately discharges the order-15 classifications; the
    later obstruction layers and final equality recursion remain open.
30. E050 kernel-checks the order-eleven endpoint directly. Every admissible
    simple graph on eleven vertices with no independent triple has at least 36
    edges. The proof excludes complement degree five, forces exact two-element
    exterior labels around a degree-four vertex, and uses a finite label
    collision to construct a forbidden six-set; it does not use nauty, SAT,
    Kang--Pikhurko, or an assumed graph classification. A source-identical
    clean 1,297-job build and all 105 theorem assumption queries pass with zero
    warnings and only `propext`, `Classical.choice`, and `Quot.sound`.
31. E051 kernel-checks the complete order-ten structure endpoint directly.
    The bipartite complement gives two five-cliques whose original cross-edges
    form a matching. A nonbipartite complement has at most twenty edges, and
    equality is isomorphic to the canonical balanced two-fold `C5` blow-up.
    Every nineteen-edge complement has no independent five-set. The canonical
    blow-up has independence number four, vertex-cover number six, exactly the
    five alternating six-covers, and distinct minimum covers intersect in at
    most four vertices. The proof reconstructs the equality graph locally and
    uses only transparent kernel `decide` for compact finite checks; it does
    not import the E033 catalog, SAT, or Kang--Pikhurko. A fresh local-build-
    free 1,309-job mirror and all 152 theorem assumption queries pass with zero
    warnings and no foundations beyond `propext`, `Classical.choice`, and
    `Quot.sound`.
32. E052 kernel-checks the complete small independence-three obstruction.
    Every admissible simple graph with no independent four-set has at least
    45, 50, and 54 edges at orders 16, 17, and 18. The order-16 degree-five
    endpoint exhausts the E051 split: the bipartite branch forces a forbidden
    six-clique, while the nonbipartite equality branch constructs a
    five-vertex cover in the balanced two-fold `C5` blow-up, contradicting its
    cover number six. No catalog, SAT result, Kang--Pikhurko premise, or
    assumed classification is used. A fresh local-build-free 1,310-job mirror
    and all 159 theorem assumption queries pass with zero warnings, zero
    forbidden constructs, and no foundations beyond `propext`,
    `Classical.choice`, and `Quot.sound`.
33. E053 kernel-checks both order-fifteen near-extremal classifications. At
    35 edges it produces an isolated five-clique with canonical balanced
    doubled-`C5` residual complement. At 36 edges it proves an exclusive
    alternative between that residual with exactly one clique attachment and
    an isolated five-clique whose residual complement is triangle-free, has
    nineteen edges, and has no independent five-set. The proof includes the
    explicit three-coloring and cover-number-six contradictions and a separate
    incompatibility theorem. A fresh local-build-free 1,311-job mirror and all
    175 theorem assumption queries pass with zero warnings, zero forbidden
    constructs, and no foundations beyond `propext`, `Classical.choice`, and
    `Quot.sound`.
34. E054 kernel-checks the complete small independence-four obstruction.
    Every admissible graph with no independent five-set has at least 62, 59,
    and 55 edges at orders 23, 22, and 21. All minimum degrees zero through
    five are checked. The order-21 endpoint exhausts three-colorable and
    non-three-colorable order-fifteen exterior complements, replaces the last
    specialized Kang--Pikhurko endpoint with a direct Lean lower bound, and
    closes the equality case using E053 and the canonical cover number six. A
    fresh local-build-free 1,312-job mirror and all 186 theorem assumption
    queries pass with zero warnings, zero forbidden constructs, and no
    foundations beyond `propext`, `Classical.choice`, and `Quot.sound`.
35. E055 kernel-checks edge equalization and the complete low-degree reduction
    as an implication from the explicit finite special-Brooks proposition.
    Any color graph at or below 65 edges has exactly 65; the exact five-color
    edge sum equalizes all colors. Minimum degrees two and three are excluded
    through forced isolated `K3`/`K4` peelings and the E048--E054 bounds. Every
    color graph consequently contains an isolated closed-neighborhood `K5`
    whose exterior is admissible, has order 21, exactly 55 edges, no
    independent five-set, and minimum degree at least four. Degree inheritance
    is proved by an explicit neighbor-set equivalence. A fresh local-build-free
    1,313-job mirror and all 195 theorem assumption queries pass with zero
    warnings, zero forbidden constructs, and no foundations beyond `propext`,
    `Classical.choice`, and `Quot.sound`. The special-Brooks proposition remains
    a theorem hypothesis until its external LRAT certificates are bridged into
    Lean.
36. E056 kernel-checks the complete minimum-degree-four branch of the exact
    order-21 residual. Equality isolates a second `K5` and leaves an exact
    order-16, 45-edge graph. E050 excludes residual degree four. At degree
    five, E052 excludes the bipartite order-ten complement; E051 leaves the
    19- and 20-edge complement cases. Exact pointwise cross-degree accounting,
    a transparent 1,024-code five-edge certificate, and the canonical minimum-
    cover intersection theorem close every case, including the unique-excess
    `K1,4` branch and its six-set with fourteen graph edges. Thus every vertex
    of the exact order-21 residual has degree at least five. A fresh local-
    build-free 1,314-job mirror and all 208 theorem assumption queries pass
    with zero warnings, zero forbidden constructs, and no foundations beyond
    `propext`, `Classical.choice`, and `Quot.sound`.
37. E057 kernel-checks the complete minimum-degree-five branch and the final
    conditional composition. The fifteen-vertex exterior is split into its
    three-colorable branch and exact 35/36-edge noncolorable structures. The
    kernel checks pair-specific five-clique avoiders, both internal-edge
    cases, the unique-excess `K1,4`, the one-cross-edge endpoint, both cover-
    number-six contradictions, and the final six-set with fourteen graph
    edges. Together with E056, no exact admissible order-21, 55-edge
    independent-five-free graph of minimum degree at least four exists.
    Together with E055, Lean proves no 26-vertex five-color counterexample,
    `R5Upper`, and `Problem617At 5`, with `R5SpecialBrooksObstruction` as the
    sole explicit premise. A fresh local-build-free 1,315-job mirror and all
    223 theorem assumption queries pass with zero warnings, zero forbidden
    constructs, and no foundations beyond `propext`, `Classical.choice`, and
    `Quot.sound`.
38. E058 imports the complete special-Brooks certificate obstruction into
    Lean. It deterministically extracts and stages all 89 RUP-only cores,
    replays every source CNF with two independent checkers, checks all 89
    kernel imports and all 89 semantic closures, compiles eight coverage
    modules, and audits 192 theorem assumptions. The final source proves
    `e058R5SpecialBrooksObstruction`, `e058NoR5Counterexample`, `e058R5Upper`,
    and the unconditional theorem `e058Problem617AtFive : Problem617At 5`.
    The 466 generated Lean stage files have combined SHA-256
    `c79bbd0b3deea2af4ed0c95cd15566c8c708b146ee2f5100b8256230dcb04b8e`;
    the final 51-file source inventory has combined SHA-256
    `6a14c6b7443e13d2a2769c013825beddee54e53d07c493e1306638d05cc1371d`.
    The retained evidence collection has receipt SHA-256
    `3a6613e93d4620d9a66b0fd1fe97405062d977d53a5aa335dff45afc05cd0a1b`.
    A later uninterrupted no-local-build replay of the exact committed source
    at `d19a0cf786a0fa714289830f276cf406408ab65b` also passed. Its receipt
    SHA-256 is
    `789acb2bc829fcba0a5656fabca5a37d9d4fdd2b493858039ad0081cc37032d1`;
    it records `fresh_local_build=true`,
    `resumed_after_core_replay=false`, all 89 core/kernel/semantic checks,
    all 192 assumption queries, zero warnings, and zero forbidden hits. Its
    collected-evidence receipt SHA-256 is
    `2f9a1d9e4027998eb3405a2db92f2130886f4eac7fd3137c4db36325eee7c047`.
    Two preceding exact-source attempts are retained and explicitly labeled:
    one was terminated by the command-session boundary, and one stopped
    before core replay because the fresh mirror lacked the separately built C
    checker. Neither produced a terminal receipt.
    A preregistered raw branch-02 performance comparison did not complete:
    the raw Lean import timed out at 300 seconds with timeout status 124,
    310.08 user seconds, 7.57 system seconds, and 5,924,372 KiB maximum RSS.
    No reduced-side timing or speedup ratio is claimed. This failed diagnostic
    performance gate is retained and disclosed; it is not a logical premise
    of the theorem.

## Literature frontier

The 1999 Erdős–Gyárfás paper was read from the authors' hosted PDF and its bytes
were streamed through SHA-256. A 2023 publication by Gyárfás restates the same
all-\(r\) assertion as Conjecture 2.4. A newly located GitHub repository dated
2026-07-18--21 claims the fixed cases r=5 through r=9 and labels them unreviewed
preprints. E033 independently audited only r=5 and found no gap; E058 now
independently machine-verifies that fixed case through an unconditional Lean
theorem.
The same commit was re-cloned on 2026-07-22; its Git object database and the
top-level, r7-r8, and r9 in-repository SHA-256 manifests pass. This is an
integrity check, not a proof replay. The r6 manuscript, r7 enumeration, r8
LRATs, and r9 release assets and implication chain remain unaudited here.
The Erdős
Problems database page, accessed again on 2026-07-22, still marks #617
`FALSIFIABLE` and open, reports no claimed partial solution in its comments,
and was last edited 2026-04-01. The current Formal
Conjectures Lean file contains `sorry` for the all-\(r\), \(r=3\), \(r=4\), and
\(r^2\) declarations, so it supplies statements but no proofs. Details and
search caveats are in `docs/literature.md`.

## Verification run

The aggregate computational command is `./repro/verify.sh`. The checkpoint
verification inventory below combines that target with the separately pinned
Lean clean-build commands recorded through E052:

- a warning-clean C11 build with `-Wall -Wextra -Werror -pedantic`;
- exact regeneration and byte comparison of the affine artifact;
- exhaustive Python and C semantic checks;
- structural nonextension-premise verification;
- exhaustive arithmetic verification for 23,751 degree profiles;
- exact regeneration of the 400-variable, 18,630-clause equality-case CNF;
- verification of a 10,879,227-byte LRAT certificate by independent C and
  Python checkers;
- independent reconstruction of all eight E006 and all eight E008 extremal
  types;
- exhaustive small truth-table tests for the new cardinality and lexicographic
  encodings and byte-exact regeneration of sixteen CNFs;
- decompression and two-checker validation of sixteen E006/E008 RUP-only LRAT
  certificates, totaling 78,491,040 compressed bytes and 347,428,327 raw bytes;
- exact regeneration and independent structural audit of the 11,079-variable,
  127,686-clause E009 CNF, plus semantic inclusion of its 30,104-clause search
  core and rejection of a corrupted core;
- decompression and two-checker validation of the 303,095,076-byte compressed
  E009 certificate (1,443,988,824 raw bytes and 2,331,242 derived clauses);
- independent reconstruction of the 12 order-22 E011 extremal types and
  two-checker validation of their 12 RUP-only LRAT certificates;
- exact regeneration and exhaustive clause audits for the balanced 46-edge
  CNF, the order-21 private-witness reduction, all 13 composition branches, and
  the final free-`A_1` orbit fix;
- decompression and two-checker validation of all 14 E011 variable-graph
  certificates, totaling 7,297,711,045 raw and 1,467,400,160 compressed LRAT
  bytes;
- independent reconstruction of E012's complete profile/slack catalog, the
  spoke-pigeonhole reduction, all graph, private-witness, composition, branch,
  and point-quotient clauses, plus byte-exact regeneration of 33 near inputs;
- decompression and two-checker validation of 12 redundant E012 fixed
  certificates and the two theorem-bearing variable certificates, totaling
  1,462,151,090 raw and 283,749,072 compressed LRAT bytes;
- independent reconstruction of E013's complete profile/slack catalog, four
  irreducible targets, both classification-free graph systems, all fourteen
  equality-template branches, eight eliminated color-\(K_6\) templates, and
  the sole hard-branch true-twin quotient;
- decompression and two-checker validation of the two E013 one-exception
  certificates, totaling 2,160,118,765 raw and 416,507,868 compressed LRAT
  bytes, plus all fourteen exhaustive double-branch certificates, totaling
  3,715,897,000 raw and 818,878,252 compressed LRAT bytes;
- independent reconstruction of E014's 23,751-profile exact-value catalog,
  five spoke eliminations, five order-24 color-\(K_6\) eliminations, six
  irreducible targets, ten directed deletion bridges, and all sixteen
  classified double branches;
- two-checker validation of the balanced-49 certificate and thirteen direct
  E014 classified branches, totaling 4,456,127,537 raw and 902,738,648
  compressed LRAT bytes;
- independent exact reconstruction of all 3,542,000 neighbor-color
  availability clauses across the four formerly open targets, plus clean
  regeneration, dual-checker validation, sixteen corruption rejections, and
  XZ round-trip checks for their four unsplit zero-RAT LRATs;
- exact unit-extension audits, split-lifter corruption tests, full-LRAT/RAT
  cross-check tests, complete-model-checker corruption tests for the E014
  search and composition infrastructure, and validation of redundant
  uncomposed counter leaves without using them as theorem premises;
- 44 negative LRAT outcomes using truncated and forged-empty certificates
  across all eleven certificate families;
- independent reconstruction of all 1,154,966 clauses in the unrestricted E007
  CNF generator;
- E029's complete allocation and 42,492-case transversal audit, exact residual
  clause reconstruction, two 61-edge graph audits, three exact CNF
  regenerations, dual-checker validation of three RUP-only LRATs, twelve
  corruption rejections, and six XZ round trips;
- E030's complete allocation, equality/slack attachment, five-case
  critical-subgraph, and final-star audits; four disjoint residual orbits;
  independent reconstruction of all 22,986 classification clauses; four
  exact 62-edge graph and CNF-suffix audits; dual-checker validation of five
  zero-RAT LRATs; 20 corruption rejections; and ten XZ round trips;
- E031's fresh degree/allocation and physical-attachment audit; complete
  minimum-degree component recursion; one residual-12 and five residual-11
  classes; exhaustive reconstruction of 2,700 order-11 and 25,620 order-16
  DHGO compositions into 2 and 48 classes; all 48 full-graph semantic audits;
  independent reconstruction of all theorem-bearing clauses; dual-checker
  validation of 13 zero-RAT LRATs; 52 corruption rejections; and 26 XZ round
  trips;
- E033's pinned external-source receipt, complete arithmetic reconstruction,
  independent semantic checking of 12,172 order-10 and 6,153 order-11
  triangle-free graph representatives, 20 Kang--Pikhurko equality templates,
  balanced-blow-up minimum covers, and all 177,100 affine six-sets;
- E034's warning-clean 1,249-job Lean build from a fresh project directory and
  transitive assumption audit of all 43 then-exported theorems;
- E035's warning-clean fresh 1,285-job build, source safety scan, and
  transitive assumption audit of all 64 then-exported theorems;
- independent reconstruction of E036's 473,771-clause finite graph formula,
  all 26 E037 neighborhood orbits, E038's 19 exterior-pattern comparisons,
  E039's exact 32-way split, and E040's 19,404 local admissibility clauses;
- exact regeneration and dual-checker validation of E038 branches 00--18,
  with 19 zero-RAT LRATs, 76 deliberate corruption rejections, and 38
  compressed/raw hash round trips;
- independent reconstruction of E042's 20 cross-pattern orbits, E043's
  26/16/5 residual-anchor orbits, E044's 413,721 clauses and 2,048 truth rows,
  and E045's corrected cross-stub/zero-anchor quotient;
- exact regeneration and dual-checker validation of 70 E042/E043/E045
  formulas and zero-RAT LRATs, with 280 deliberate corruption rejections and
  complete combined coverage of all 26 finite special-Brooks neighborhood
  branches;
- E046--E047 independent reconstruction of six broad extremal formulas, all
  125 anchor clauses and 29,097,984 anchor neighborhoods, exact regeneration
  of all twelve parent/anchored formulas, and dual-checker validation of four zero-RAT LRATs with
  16 deliberate corruption rejections; the two `UNKNOWN` formulas remain
  non-evidence;
- E049's clean warning-free 1,296-job Lean build and transitive assumption
  audit of all 90 exported theorems, including E048 and all admissible
  independence-level propagation theorems;
- E050's source-identical clean warning-free 1,297-job Lean build, source
  safety scan, and transitive assumption audit of all 105 exported theorems,
  including the direct order-eleven 36-edge endpoint;
- E051's fresh-mirror warning-free 1,309-job Lean build, fourteen-file source
  safety scan, and transitive assumption audit of all 152 exported theorems,
  including every order-ten structure and canonical-cover conclusion;
- E052's fresh local-build-free warning-free 1,310-job Lean build, fifteen-file
  source safety scan, and transitive assumption audit of all 159 exported
  theorems, including every order-16/17 branch and the combined three-range
  independence-three obstruction;
- E053's fresh local-build-free warning-free 1,311-job Lean build, sixteen-file
  source safety scan, and transitive assumption audit of all 175 exported
  theorems, including both order-fifteen classifications and their
  incompatibility;
- E054's fresh local-build-free warning-free 1,312-job Lean build,
  seventeen-file source safety scan, and transitive assumption audit of all
  186 exported theorems, including all three small independence-four ranges;
- E055's fresh local-build-free warning-free 1,313-job Lean build,
  eighteen-file source safety scan, and transitive assumption audit of all 195
  exported theorems, including edge equalization, both low-degree exclusions,
  and the exact first residual structure;
- E056's fresh local-build-free warning-free 1,314-job Lean build,
  nineteen-file source safety scan, and transitive assumption audit of all 208
  exported theorems, including the complete residual minimum-degree-four
  recursion and every order-ten cover branch;
- E057's fresh local-build-free warning-free 1,315-job Lean build,
  twenty-file source safety scan, and transitive assumption audit of all 223
  exported theorems, including every residual minimum-degree-five branch and
  the conditional fixed-`r=5` upper theorem;
- E058's 89 regenerated unit CNFs, 89 dual-checker RUP core replays, 89 kernel
  imports, 89 semantic closures, eight coverage modules, 192 explicit
  assumption queries, 466 retained generated Lean stage files, zero warnings,
  and zero forbidden-source hits, culminating in the unconditional
  `e058Problem617AtFive : Problem617At 5`;
- the 25 focused E058 regression tests covering the audit runner, semantic
  closure audit, orbit certificates, LRAT minimization, and staged RUP
  splitting;
- ten positive/negative/format/record-boundary/scope test cases;
- SHA-256 verification of all committed computational artifacts.

Fresh `make test` and the complete `make verify` target both exited successfully
on 2026-07-21 after the E014 availability proofs and integrity ledger were
added.

The E018, E024/E027/E028, E029, and E030 targeted suites pass, including exact
regeneration, two independent LRAT checkers, 28 total deliberate certificate-
corruption rejections across the 59-, 60-, and 61-edge families, and all
compressed round trips. E030 adds 20 deliberate rejections for the 62-edge
family.
A fresh complete post-E030 `make test` run exited successfully on 2026-07-22,
including all five new certificates and their 20 deliberate corruption checks.
The complete E031 targeted suite and its certificate regression exited
successfully on 2026-07-22. The E035 clean Lean audit and all E036--E040 formula
audits passed on 2026-07-22; the complete E038 certificate regression also
passed. The E042--E045 structural audits and the complete 70-certificate
residual regression passed on 2026-07-22, with all 70 exact regenerations, 140
positive checker runs, and 280 negative checks accepted at their expected
status. The E046--E050 structural, certificate, and clean Lean audits also
passed on 2026-07-22; E051's through E057's fresh-mirror Lean audits passed on
2026-07-23. E058's raw clean-start audit, validated resume sequence, and
hardened final-source audit passed on 2026-07-23--24. A later uninterrupted
no-local-build replay of exact commit `d19a0cf` passed on 2026-07-24 after
25,497.97 seconds. Its separate raw branch-02 performance benchmark failed the
fixed 300-second cap and produced no speedup claim. The
multi-hour `make verify`
target has not been rerun since E014; its later steps are included or recorded
as targeted commands, but the exact reported level does not rely on an unrun
aggregate command.

## Trust boundaries

The elementary lemmas and all bridges from mathematics to finite instances have
human proofs. The finite obstructions depend on deterministic CNF generators,
the committed LRAT inventory, two checkers with different implementations, the
C compiler, Python interpreter, operating system, LZMA implementation, and
SHA-256. The E014 availability formulas are necessary relaxations rather than
the full coloring formula; their counted/unforced bridge is independently
clause-audited but not kernel-checked. E014's uncomposed split leaves are valid
only for their named unit extensions and are not counted as parent
obstructions. The E009 search used an
extracted clause core, but its final LRAT is checked directly against the full regenerated CNF; the core
extractor is not a theorem trust dependency. Solver UNSAT returns are not
trusted; only checked certificates are evidence. E034--E057 add a proof-
assistant kernel for their explicitly listed partial lemmas. E038's finite
certificate chain together with E042--E045 covers all 26 special-Brooks
neighborhood branches. E058 regenerates those source instances, independently
checks the 89 RUP-only reduced cores, translates each retained RUP step into a
generated Lean proof term, kernel-checks every staged import, and separately
checks the semantic closure back to the original finite proposition. The same
bridge has not been applied to E047's four broader extremal LRATs;
E049's admissible propagation, E050's order-eleven theorem, E051's order-ten
theorem, E052's small independence-three theorem, and E053's order-fifteen
classifications and E054's small independence-four obstruction do not depend
on them. E055 depends on the special-Brooks proposition explicitly. E058
supplies that proposition as a kernel-checked theorem rather than silently
trusting an external checker result. E056 is an
unconditional graph theorem at its stated residual hypotheses and does not
depend on those certificates. E057 completes the residual recursion
unconditionally at its stated graph hypotheses and proves the fixed-`r=5`
upper statement conditional only on `R5SpecialBrooksObstruction`. E058 joins
that implication to the staged certificate proof and yields one unconditional
kernel-checked theorem. The trusted execution boundary includes Lean and its
kernel, the generated proof sources, the pinned source/CNF generators, the C
compiler and Python interpreter used for independent replay, the operating
system, XZ/LZMA, and SHA-256. The failed branch-02 timing comparison is not in
the theorem dependency graph. The remaining imported
Kang--Pikhurko extremal
theorem and characterization, Dirac's critical-graph edge theorem, and
Kostochka--Yancey's critical-graph lower bound and 6-Ore equality
characterization are peer-reviewed, but their full proofs have not been locally
formalized.

Exact E011--E014 per-instance dimensions, raw and compressed proof hashes,
converter statistics, failed-search records, and reproduction commands are in
their corresponding result records under `experiments/`.

## Terminal release obligation

The fixed-\(r=5\) verification obligation is discharged by E058. Ramazan Kara
cross-checked the theorem, evidence, paper, release payloads, exact scope, AI
disclosure, and publication metadata and explicitly approved public release on
24 July 2026. The approved target is
`RamazanKara/erdos-617-r5-formal-verification`, and the approved
repository-wide license is Apache-2.0.

The sole remaining obligation for this terminal goal is to push the exact
license-bearing checkpoint, publish the five-file GitHub release, and
independently download and hash-check every published asset. No \(r\ge10\),
all-\(r\), or additional fixed-case research is authorized by this goal. The
all-\(r\) conjecture remains open, and the pinned \(r=6,\ldots,9\) claims
remain provisional and unverified here.
