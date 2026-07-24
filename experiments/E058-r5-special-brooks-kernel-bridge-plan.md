# E058 — kernel bridge for the finite special-Brooks obstruction

Status before implementation: `PLANNED`.

## Question

Can the complete E038/E042--E045 zero-RAT certificate chain be imported into
the pinned Lean kernel and connected, without an unproved encoding or symmetry
premise, to `R5SpecialBrooksObstruction`?

## Exact input space

The mathematical input is every simple graph `G` on `Fin 26` satisfying

- `G.degree v = 5` for every vertex `v`;
- `Admissible G`;
- `G.CliqueFree 6`; and
- `G.IndepSetFree 6`.

The finite certificate inventory is exactly the 89 checked RUP-only LRATs
already committed for the exhaustive E038/E042/E043/E045 split:

- 19 E038 neighborhood branches `00,...,18`;
- 17 directly certified E042 cross-pattern children of branch `19`;
- 47 E043 residual anchor-neighborhood children of the three open E042
  parents; and
- 6 E045 quotient branches `20,...,25`.

No solver return, uncertified branch, omitted quotient representative, or
external fixed-case claim is a theorem premise.

## Certificate representation

Mathlib's `Mathlib.Tactic.Sat.FromLRAT` is the proof-producing checker.  Its
standard command reifies a roughly 474,000-clause input as one enormous
proposition.  A proof-only command may instead retain the generated
`Sat.Fmla.proof []` theorem.  The original E038 branch-02 benchmark must be
recorded before optimization.

Because each committed proof is RUP-only and begins by deleting unused input
clauses, a deterministic backward slicer may replace it by an equivalent
proof core.  The slicer must:

1. parse the exact DIMACS and LRAT grammars used here and reject comments in
   the kernel input, duplicate/nonincreasing additions, missing antecedents,
   RAT/negative hints, a missing final empty clause, or malformed records;
2. start at the final empty-clause addition, traverse every referenced
   antecedent backward, and retain every and only reachable original and
   derived clause;
3. emit the reachable original clauses in original-ID order, preserve all
   clause literals, deterministically renumber every retained addition and
   hint, omit deletions only after proving them semantically irrelevant, and
   write a complete old-to-new clause-ID map;
4. hash the original CNF/LRAT, reduced CNF/LRAT, map, and receipt; and
5. reproduce byte-for-byte from the committed compressed inputs.

The reduction is not evidence by itself.  Every reduced pair must be accepted
by the pinned compiled C checker and the independent Python checker.  Both
must reject at least a truncated proof and a forged empty-clause proof.
Selected parser, dependency, and renumbering corruptions must also be rejected
by unit tests.

## Lean obligations

### LRAT kernel check

For every theorem-bearing core, the pinned Lean 4.32.0/mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997` environment must construct and
kernel-check a theorem of the form `Sat.Fmla.proof core []`.  The generated
theorems may depend only on `propext`, one of the three already allowed logical
foundations.  No `sorry`, `admit`, project axiom, `native_decide`,
`ofReduceBool`, or unchecked runtime Boolean result is permitted.

### CNF semantic bridge

Lean must define the 325 edge variables and every auxiliary sequential-counter
and exterior-pattern variable used by the generators.  From a graph satisfying
the exact branch hypotheses it must construct a valuation and prove every
retained input clause.  Reusing a generic, kernel-proved correctness theorem
for a deterministic cardinality or sorting encoding is allowed.  Trusting the
Python generator, a receipt, clause hashes, or checker agreement in place of
this theorem is not allowed.

### Symmetry and coverage bridge

Lean must prove that relabeling a putative graph can fix the neighborhood of
vertex zero to `1,...,5`, place its induced five-vertex graph in one of the 26
E037 orbit representatives, sort the 20 exterior five-bit rows, and enter the
complete E042/E043/E045 refinement assigned to that representative.  All
permutations must transport regularity, admissibility, clique-freeness, and
independent-set-freeness.  Transparent finite orbit checks are allowed only
when their enumerated domains and coverage theorems are visible to the kernel.

## Exported conclusions

Full success requires exporting and auditing at least:

1. a theorem that each of the 89 named reduced CNFs is unsatisfiable;
2. complete branch-coverage and encoding-soundness theorems;
3. an unconditional proof of `R5SpecialBrooksObstruction`;
4. unconditional `no_r5_counterexample`, `R5Upper`, and `Problem617At 5` by
   composition with E055--E057.

If only the core transformer or a strict subset of branch theorems is checked,
the result is `PARTIAL-CERTIFIED` and fixed `r=5` remains a
`CANDIDATE-RESOLUTION`.

## Verification plan

- Unit-test the core extractor on hand-written positive, deletion, unreachable
  addition, missing-hint, RAT-hint, malformed, truncated, and forged-empty
  examples.
- On E038 branch 02, compare the raw proof-only Mathlib import against the
  reduced import under a five-minute wall cap and 8 GiB memory cap; retain
  wall time and peak RSS.
- Regenerate all reduced cores from the committed `.xz` inputs in a clean
  temporary directory, compare hashes, and run both external LRAT checkers
  plus deliberate corruptions.
- Build the complete pinned Lean project from a fresh local-build-free mirror;
  audit every exported theorem with `#print axioms`, reject warnings and
  forbidden source constructs, and compare all source bytes after the run.
- Retain exact tool versions, commands, inventories, hashes, transcripts,
  resource records, and the original-to-core clause maps.

## Falsifiers and scope boundary

Any omitted reachable antecedent, clause-literal change, bad ID remap,
accepted corruption, checker disagreement, nonzero RAT step, Lean import
failure, hidden axiom, unproved auxiliary-variable interpretation, incomplete
orbit, invalid relabeling transport, or graph satisfying the hypotheses
falsifies full promotion.

Even full E058 success would prove only the fixed `r=5` case.  It would not
verify the external `r=6`--`r=9` repository claims and would not settle the
all-`r` Erdos 617 conjecture.
