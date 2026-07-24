# Formal verification status

E034--E058 establish an unconditional Lean 4 proof of the fixed-\(r=5\)
case. The project in `formal/lean/` pins Lean 4.32.0 and mathlib revision
`81a5d257c8e410db227a6665ed08f64fea08e997`; the audited source contains no
placeholders, added axioms, unsafe declarations, or unchecked native
computation.

The checked modules currently provide:

- the exact unordered-edge statement for fixed r=5 and a separate all-r
  statement;
- the missing-color, independent-set, and complement-clique translations;
- color-graph partition and relabeling lemmas;
- a kernel-checked affine `K₂₅` lower construction;
- the complementary colorability product bound;
- the exact local one-to-eleven bound and admissibility bridge;
- the global edge partition, Turán 55-edge lower bound, and a 65-edge sparse
  color class;
- exclusion of an isolated vertex in that sparse class;
- exact open-neighborhood crossing/internal accounting and the three minimum-
  degree inequalities;
- degree-five admissibility bounds and the isolated-clique equality case;
- the independent-six/five-colorability bridge and 5-regular handshake
  reduction;
- a degree-at-most-four conclusion conditional on the explicit finite
  obstruction to an admissible, 5-regular, six-clique-free, independent-six-
  free graph on 26 vertices; and
- the large independence-two terminal lemma: an admissible graph with no
  independent triple has complement maximum degree at most five, at most four
  from order twelve onward, and hence at least
  `choose n 2 - 2 * n` edges;
- exact induced-subgraph admissibility, exterior independence reduction,
  three-way edge decomposition, and minimum-vertex average-degree bridges; and
- the complete large numerical propagation: admissible `IndepSetFree 4`
  graphs at orders 18--24 have at least 54, 56, 62, 69, 76, 83, and 90 edges,
  while admissible `IndepSetFree 5` graphs at orders 24 and 25 have at least 65
  and 71 edges; and
- the order-eleven endpoint: every admissible order-eleven graph with no
  independent triple has at least 36 edges, proved by a direct two-subset label
  collision rather than a graph catalog;
- the complete order-ten structure, both order-fifteen classifications, and
  the complete small independence-three/four obstructions;
- conditional edge equalization, exclusion of minimum degrees two and three,
  and the first isolated-`K5` order-21 residual; and
- the unconditional residual minimum-degree-four recursion, including every
  19/20-edge order-ten cover case, proving that the exact order-21 residual has
  minimum degree at least five; and
- the unconditional residual minimum-degree-five contradiction, all 35/36-
  edge order-fifteen subcases, and the fixed-`r=5` upper statement conditional
  only on `R5SpecialBrooksObstruction`; and
- 89 staged kernel LRAT theorems, 89 graph-semantic closures, exhaustive
  relabeling/orbit/sorting/branch coverage, an unconditional
  `R5SpecialBrooksObstruction`, and the final declaration
  `Erdos617.e058Problem617AtFive : Problem617At 5`.

The E058 clean-start/resume sequence and hardened final replay are retained
under `artifacts/e058_special_brooks_kernel_bridge/fresh_audit/`. A later
uninterrupted no-local-build replay of the exact committed final source is
retained under
`artifacts/e058_special_brooks_kernel_bridge/exact_head_fresh_audit/`.
Its receipt SHA-256 is
`789acb2bc829fcba0a5656fabca5a37d9d4fdd2b493858039ad0081cc37032d1`
and records no resume. It validates 89 kernel imports, 89 semantic closures,
eight coverage modules, and 192 assumption queries. The final theorem reports
exactly Lean's standard logical foundations `propext`, `Classical.choice`,
and `Quot.sound`, with no project-defined axiom or `sorryAx`.

From this directory, reproduce with:

```sh
lake exe cache get
lake build
lake env lean Erdos617/Audit.lean
```

This is a `MACHINE-VERIFIED-RESOLUTION` only for fixed \(r=5\). It does not
verify the upstream fixed \(r=6,\ldots,9\) claims and does not resolve the
all-\(r\) conjecture. Independent expert review has not yet been completed.
OpenAI Codex materially assisted the formalization and verification workflow;
see `AI_USAGE.md`.

The upstream Formal Conjectures declarations still contain placeholders and
are not used as evidence here. The E058 LRAT artifacts become theorem premises
only through the checked staged imports and graph-semantic bridge; solver
returns and external checker agreement alone are not used as the proof.
