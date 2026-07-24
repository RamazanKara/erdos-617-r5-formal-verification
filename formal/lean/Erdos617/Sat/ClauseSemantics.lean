/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.Sat.SpecialBrooksVariables

/-!
# Semantic clauses for the E058 bridge

Mathlib's LRAT reifier exports an ordinary proposition asserting that some
input clause is falsified.  This file gives a safe, transparent counterpart
for clauses written with semantic variable names and proves the reusable
degree-counter clauses.
-/

@[expose] public section

open Finset

namespace Erdos617

/-- A positive or negative occurrence of a semantically named variable. -/
inductive R5NamedLiteral where
  | pos (name : R5VariableName)
  | neg (name : R5VariableName)
  deriving DecidableEq, Repr

abbrev R5NamedClause := List R5NamedLiteral

/-- Truth of a named literal. -/
def r5NamedLiteralTrue
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] :
    R5NamedLiteral → Prop
  | .pos name => r5InterpretVariable G name
  | .neg name => ¬r5InterpretVariable G name

/-- Falsity of a named literal. -/
def r5NamedLiteralFalse
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] :
    R5NamedLiteral → Prop
  | .pos name => ¬r5InterpretVariable G name
  | .neg name => r5InterpretVariable G name

/-- Right-associated conjunction, with a singleton represented by the
proposition itself.  This is the exact shape used by Mathlib's LRAT reifier
for a nonempty clause. -/
def rightAssociatedAnd : List Prop → Prop
  | [] => True
  | [p] => p
  | p :: q :: rest => p ∧ rightAssociatedAnd (q :: rest)

/-- Every member of a right-associated conjunction follows from the
conjunction. -/
theorem rightAssociatedAnd_member {propositions : List Prop}
    (h : rightAssociatedAnd propositions) {p : Prop}
    (hp : p ∈ propositions) : p := by
  induction propositions with
  | nil => simp at hp
  | cons head tail ih =>
      cases tail with
      | nil =>
          have hp' : p = head := List.mem_singleton.mp hp
          subst p
          exact h
      | cons next rest =>
          simp only [rightAssociatedAnd] at h
          rcases List.mem_cons.mp hp with rfl | hp
          · exact h.1
          · exact ih h.2 hp

/-- Exact falsification proposition for a named clause. -/
def R5NamedClause.Falsified
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (clause : R5NamedClause) : Prop :=
  rightAssociatedAnd (clause.map (r5NamedLiteralFalse G))

/-- Semantic validity of a named clause. -/
def R5NamedClause.Valid
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (clause : R5NamedClause) : Prop :=
  ∃ literal ∈ clause, r5NamedLiteralTrue G literal

/-- Every literal in a finite branch assignment has its asserted truth
value.  Certificate-specific bridge theorems expose their retained unit
clauses through this predicate. -/
def R5NamedClause.AllTrue
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (literals : List R5NamedLiteral) : Prop :=
  ∀ literal ∈ literals, r5NamedLiteralTrue G literal

/-- The exterior rows are lexicographically nondecreasing along every
comparison in the requested quotient. -/
def R5ComparisonsSorted
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (comparisons : List (ℕ × ℕ)) : Prop :=
  ∀ comparison ∈ comparisons,
    propLexicographicLE
      (r5ExteriorPatternBit G comparison.1)
      (r5ExteriorPatternBit G comparison.2) 5

/-- Exact semantic assumptions under which one branch core was generated.
The unit list is certificate-specific; keeping it in the theorem type makes
every retained primary assignment visible to later coverage proofs. -/
structure R5CoreAssumptions
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (comparisons : List (ℕ × ℕ))
    (units : List R5NamedLiteral) : Prop where
  regular : ∀ v, G.degree v = 5
  admissible : Admissible G
  cliqueFree : G.CliqueFree 6
  indepSetFree : G.IndepSetFree 6
  sorted : R5ComparisonsSorted G comparisons
  unitsTrue : R5NamedClause.AllTrue G units

/-- A semantically valid named clause cannot be falsified. -/
theorem R5NamedClause.not_falsified_of_valid
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    {clause : R5NamedClause} (hvalid : clause.Valid G) :
    ¬clause.Falsified G := by
  rintro hfalsified
  obtain ⟨literal, hmem, htrue⟩ := hvalid
  have hfalse : r5NamedLiteralFalse G literal :=
    rightAssociatedAnd_member hfalsified (List.mem_map.mpr
      ⟨literal, hmem, rfl⟩)
  cases literal with
  | pos name => exact hfalse htrue
  | neg name => exact htrue hfalse

/-- A true singleton literal is a valid unit clause. -/
theorem R5NamedClause.valid_singleton
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (literal : R5NamedLiteral)
    (htrue : r5NamedLiteralTrue G literal) :
    R5NamedClause.Valid G [literal] :=
  ⟨literal, by simp, htrue⟩

/-- Semantic helper for a binary implication clause `¬a ∨ b`. -/
theorem r5NamedClause_valid_neg_pos_of_imp
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (a b : R5VariableName)
    (himp : r5InterpretVariable G a → r5InterpretVariable G b) :
    R5NamedClause.Valid G [.neg a, .pos b] := by
  by_cases ha : r5InterpretVariable G a
  · exact ⟨.pos b, by simp, himp ha⟩
  · exact ⟨.neg a, by simp, ha⟩

/-- Semantic helper for `¬a ∨ b ∨ c`. -/
theorem r5NamedClause_valid_neg_pos_pos_of_imp
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (a b c : R5VariableName)
    (himp : r5InterpretVariable G a →
      r5InterpretVariable G b ∨ r5InterpretVariable G c) :
    R5NamedClause.Valid G [.neg a, .pos b, .pos c] := by
  by_cases ha : r5InterpretVariable G a
  · rcases himp ha with hb | hc
    · exact ⟨.pos b, by simp, hb⟩
    · exact ⟨.pos c, by simp, hc⟩
  · exact ⟨.neg a, by simp, ha⟩

/-- Semantic helper for `¬a ∨ ¬b ∨ c`. -/
theorem r5NamedClause_valid_neg_neg_pos_of_imp
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (a b c : R5VariableName)
    (himp : r5InterpretVariable G a →
      r5InterpretVariable G b → r5InterpretVariable G c) :
    R5NamedClause.Valid G [.neg a, .neg b, .pos c] := by
  by_cases ha : r5InterpretVariable G a
  · by_cases hb : r5InterpretVariable G b
    · exact ⟨.pos c, by simp, himp ha hb⟩
    · exact ⟨.neg b, by simp, hb⟩
  · exact ⟨.neg a, by simp, ha⟩

/-- Semantic edge name with endpoints in the generator's increasing order. -/
def r5EdgeName (u v : Fin 26) : R5VariableName :=
  if u < v then .edge u v else .edge v u

/-- An edge name denotes exactly graph adjacency. -/
theorem r5InterpretVariable_edgeName
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (u v : Fin 26) (hne : u ≠ v) :
    r5InterpretVariable G (r5EdgeName u v) ↔ G.Adj u v := by
  by_cases huv : u < v
  · simp [r5EdgeName, huv, r5InterpretVariable]
  · have hvu : v < u :=
      lt_of_le_of_ne (le_of_not_gt huv) (Ne.symm hne)
    simp [r5EdgeName, huv, r5InterpretVariable, G.adj_comm]

/-- Canonical edge names do not depend on endpoint orientation. -/
theorem r5EdgeName_comm (u v : Fin 26) :
    r5EdgeName u v = r5EdgeName v u := by
  by_cases huv : u < v
  · have hnvu : ¬v < u := not_lt_of_ge (le_of_lt huv)
    simp [r5EdgeName, huv, hnvu]
  · by_cases hvu : v < u
    · simp [r5EdgeName, huv, hvu]
    · have huvEq : u = v :=
        le_antisymm (le_of_not_gt hvu) (le_of_not_gt huv)
      subst v
      simp [r5EdgeName]

/-- Ordered generation of all unordered pairs in a list. -/
def listUnorderedPairs {α : Type*} : List α → List (α × α)
  | [] => []
  | head :: tail =>
      tail.map (fun other => (head, other)) ++ listUnorderedPairs tail

/-- Two distinct members of a list occur in one orientation among its
generated unordered pairs. -/
theorem mem_listUnorderedPairs_or_swap
    {α : Type*} (vertices : List α)
    {u v : α} (hu : u ∈ vertices) (hv : v ∈ vertices) (hne : u ≠ v) :
    (u, v) ∈ listUnorderedPairs vertices ∨
      (v, u) ∈ listUnorderedPairs vertices := by
  classical
  induction vertices generalizing u v with
  | nil => simp at hu
  | cons head tail ih =>
      rcases List.mem_cons.mp hu with rfl | huTail
      · rcases List.mem_cons.mp hv with rfl | hvTail
        · exact False.elim (hne rfl)
        · exact Or.inl (by
            simp only [listUnorderedPairs, List.mem_append,
              List.mem_map]
            exact Or.inl ⟨v, hvTail, rfl⟩)
      · rcases List.mem_cons.mp hv with rfl | hvTail
        · exact Or.inr (by
            simp only [listUnorderedPairs, List.mem_append,
              List.mem_map]
            exact Or.inl ⟨u, huTail, rfl⟩)
        · rcases ih huTail hvTail hne with hp | hp
          · exact Or.inl (by
              simp only [listUnorderedPairs, List.mem_append]
              exact Or.inr hp)
          · exact Or.inr (by
              simp only [listUnorderedPairs, List.mem_append]
              exact Or.inr hp)

/-- Positive all-pairs clause generated from a vertex list. -/
def r5PositivePairClause (vertices : List (Fin 26)) : R5NamedClause :=
  (listUnorderedPairs vertices).map fun pair =>
    .pos (r5EdgeName pair.1 pair.2)

/-- Negative all-pairs clause generated from a vertex list. -/
def r5NegativePairClause (vertices : List (Fin 26)) : R5NamedClause :=
  (listUnorderedPairs vertices).map fun pair =>
    .neg (r5EdgeName pair.1 pair.2)

/-- Unordered induced edges named by pairs of vertices already carrying their
membership proofs in a fixed six-set. -/
abbrev R5VertexIn (vertices : Finset (Fin 26)) :=
  {vertex : Fin 26 // vertex ∈ vertices}

def r5InducedPairEdgeFinset (vertices : Finset (Fin 26))
    (pairs : List (R5VertexIn vertices × R5VertexIn vertices)) :
    Finset (Sym2 (R5VertexIn vertices)) :=
  (pairs.map fun pair => s(pair.1, pair.2)).toFinset

/-- Negative edge clause obtained by forgetting the membership proofs on an
induced endpoint-pair list. -/
def r5NegativeInducedPairClause (vertices : Finset (Fin 26))
    (pairs : List (R5VertexIn vertices × R5VertexIn vertices)) :
    R5NamedClause :=
  pairs.map fun pair =>
    .neg (r5EdgeName pair.1.1 pair.2.1)

/-- Every pair in an induced endpoint list has distinct endpoints. -/
def r5InducedPairsLoopless (vertices : Finset (Fin 26))
    (pairs : List (R5VertexIn vertices × R5VertexIn vertices)) : Prop :=
  ∀ pair ∈ pairs, pair.1 ≠ pair.2

instance instDecidableR5InducedPairsLoopless
    (vertices : Finset (Fin 26))
    (pairs : List (R5VertexIn vertices × R5VertexIn vertices)) :
    Decidable (r5InducedPairsLoopless vertices pairs) := by
  unfold r5InducedPairsLoopless
  infer_instance

/-- Every fixed induced pair has its positive edge literal among a supplied
branch assignment. -/
def r5FixedPairsCoveredByUnits (vertices : Finset (Fin 26))
    (fixedPairs : List (R5VertexIn vertices × R5VertexIn vertices))
    (units : List R5NamedLiteral) : Prop :=
  ∀ pair ∈ fixedPairs,
    .pos (r5EdgeName pair.1.1 pair.2.1) ∈ units

instance instDecidableR5FixedPairsCoveredByUnits
    (vertices : Finset (Fin 26))
    (fixedPairs : List (R5VertexIn vertices × R5VertexIn vertices))
    (units : List R5NamedLiteral) :
    Decidable (r5FixedPairsCoveredByUnits vertices fixedPairs units) := by
  unfold r5FixedPairsCoveredByUnits
  infer_instance

/-- Edge name at one position of a degree counter. -/
def r5IncidentEdgeName (vertex : Fin 26) (position : Fin 25) :
    R5VariableName :=
  r5EdgeName vertex (vertex.succAbove position)

/-- The incident edge name and the degree-counter input agree. -/
theorem r5InterpretVariable_incidentEdgeName
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (vertex : Fin 26) (position : Fin 25) :
    r5InterpretVariable G (r5IncidentEdgeName vertex position) ↔
      r5IncidentProp G vertex position := by
  unfold r5IncidentEdgeName
  rw [r5InterpretVariable_edgeName G vertex (vertex.succAbove position)
    (Fin.succAbove_ne vertex position).symm]
  simp [r5IncidentProp, position.isLt]

/-- An independent-set-free graph has an edge in every finset of the
forbidden cardinality. -/
theorem exists_adj_in_finset_of_indepSetFree
    (G : SimpleGraph (Fin 26)) {n : ℕ}
    (hfree : G.IndepSetFree n) (vertices : Finset (Fin 26))
    (hcard : #vertices = n) :
    ∃ u ∈ vertices, ∃ v ∈ vertices, u ≠ v ∧ G.Adj u v := by
  classical
  by_contra hnone
  have hpair :
      ∀ u ∈ vertices, ∀ v ∈ vertices, u ≠ v → ¬G.Adj u v := by
    intro u hu v hv huv hadj
    exact hnone ⟨u, hu, v, hv, huv, hadj⟩
  apply hfree vertices
  refine ⟨?_, hcard⟩
  intro u hu v hv huv
  exact hpair u hu v hv huv

/-- A clique-free graph has a nonedge in every finset of the forbidden
cardinality. -/
theorem exists_nonadj_in_finset_of_cliqueFree
    (G : SimpleGraph (Fin 26)) {n : ℕ}
    (hfree : G.CliqueFree n) (vertices : Finset (Fin 26))
    (hcard : #vertices = n) :
    ∃ u ∈ vertices, ∃ v ∈ vertices, u ≠ v ∧ ¬G.Adj u v := by
  classical
  by_contra hnone
  have hpair :
      ∀ u ∈ vertices, ∀ v ∈ vertices, u ≠ v → G.Adj u v := by
    intro u hu v hv huv
    by_contra hnonadj
    exact hnone ⟨u, hu, v, hv, huv, hnonadj⟩
  apply hfree vertices
  refine ⟨?_, hcard⟩
  intro u hu v hv huv
  exact hpair u hu v hv huv

/-- Any clause containing a true positive edge literal is valid. -/
theorem r5NamedClause_valid_of_pos_edge
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (clause : R5NamedClause) (u v : Fin 26) (hne : u ≠ v)
    (hmem : R5NamedLiteral.pos (r5EdgeName u v) ∈ clause)
    (hadj : G.Adj u v) :
    clause.Valid G :=
  ⟨.pos (r5EdgeName u v), hmem,
    (r5InterpretVariable_edgeName G u v hne).2 hadj⟩

/-- Any clause containing a true negative edge literal is valid. -/
theorem r5NamedClause_valid_of_neg_edge
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (clause : R5NamedClause) (u v : Fin 26) (hne : u ≠ v)
    (hmem : R5NamedLiteral.neg (r5EdgeName u v) ∈ clause)
    (hnonadj : ¬G.Adj u v) :
    clause.Valid G :=
  ⟨.neg (r5EdgeName u v), hmem,
    fun h => hnonadj
      ((r5InterpretVariable_edgeName G u v hne).1 h)⟩

/-- A clause covering all pairs of a forbidden independent set is valid. -/
theorem r5PositiveSixSetClause_valid
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hfree : G.IndepSetFree 6) (vertices : Finset (Fin 26))
    (hcard : #vertices = 6) (clause : R5NamedClause)
    (hcover : ∀ u ∈ vertices, ∀ v ∈ vertices, u ≠ v →
      R5NamedLiteral.pos (r5EdgeName u v) ∈ clause) :
    clause.Valid G := by
  obtain ⟨u, hu, v, hv, huv, hadj⟩ :=
    exists_adj_in_finset_of_indepSetFree G hfree vertices hcard
  exact r5NamedClause_valid_of_pos_edge G clause u v huv
    (hcover u hu v hv huv) hadj

/-- A clause covering all pairs of a forbidden clique is valid. -/
theorem r5NegativeSixSetClause_valid
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hfree : G.CliqueFree 6) (vertices : Finset (Fin 26))
    (hcard : #vertices = 6) (clause : R5NamedClause)
    (hcover : ∀ u ∈ vertices, ∀ v ∈ vertices, u ≠ v →
      R5NamedLiteral.neg (r5EdgeName u v) ∈ clause) :
    clause.Valid G := by
  obtain ⟨u, hu, v, hv, huv, hnonadj⟩ :=
    exists_nonadj_in_finset_of_cliqueFree G hfree vertices hcard
  exact r5NamedClause_valid_of_neg_edge G clause u v huv
    (hcover u hu v hv huv) hnonadj

/-- The generator's positive all-pairs clause for six distinct listed
vertices is valid in an independent-six-free graph. -/
theorem r5PositivePairClause_valid
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hfree : G.IndepSetFree 6) (vertices : List (Fin 26))
    (hcard : vertices.length = 6) (hnodup : vertices.Nodup) :
    (r5PositivePairClause vertices).Valid G := by
  let vertexFinset := vertices.toFinset
  apply r5PositiveSixSetClause_valid G hfree vertexFinset
  · simpa [vertexFinset, List.toFinset_card_of_nodup hnodup] using hcard
  · intro u hu v hv huv
    have huList : u ∈ vertices := by simpa [vertexFinset] using hu
    have hvList : v ∈ vertices := by simpa [vertexFinset] using hv
    rcases mem_listUnorderedPairs_or_swap vertices huList hvList huv with
      hp | hp
    · exact List.mem_map.mpr ⟨(u, v), hp, rfl⟩
    · exact List.mem_map.mpr
        ⟨(v, u), hp, by simp [r5EdgeName_comm u v]⟩

/-- The generator's negative all-pairs clause for six distinct listed
vertices is valid in a six-clique-free graph. -/
theorem r5NegativePairClause_valid
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hfree : G.CliqueFree 6) (vertices : List (Fin 26))
    (hcard : vertices.length = 6) (hnodup : vertices.Nodup) :
    (r5NegativePairClause vertices).Valid G := by
  let vertexFinset := vertices.toFinset
  apply r5NegativeSixSetClause_valid G hfree vertexFinset
  · simpa [vertexFinset, List.toFinset_card_of_nodup hnodup] using hcard
  · intro u hu v hv huv
    have huList : u ∈ vertices := by simpa [vertexFinset] using hu
    have hvList : v ∈ vertices := by simpa [vertexFinset] using hv
    rcases mem_listUnorderedPairs_or_swap vertices huList hvList huv with
      hp | hp
    · exact List.mem_map.mpr ⟨(u, v), hp, rfl⟩
    · exact List.mem_map.mpr
        ⟨(v, u), hp, by simp [r5EdgeName_comm u v]⟩

/-- An admissibility clause is valid when its negative literals, together
with fixed true edges, would otherwise exhibit twelve edges on six vertices.
All finite distinctness obligations remain explicit arguments;
the generated bridge discharges them by kernel reduction for each concrete
clause. -/
theorem r5NegativeInducedPairClause_valid_of_admissible
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hG : Admissible G)
    (vertices : Finset (Fin 26))
    (fixedPairs variablePairs :
      List (R5VertexIn vertices × R5VertexIn vertices))
    (hverticesCard : #vertices = 6)
    (hpairsNe :
      r5InducedPairsLoopless vertices (fixedPairs ++ variablePairs))
    (hwitnessCard :
      #(r5InducedPairEdgeFinset vertices
        (fixedPairs ++ variablePairs)) = 12)
    (units : List R5NamedLiteral)
    (hunits : R5NamedClause.AllTrue G units)
    (hfixedCovered :
      r5FixedPairsCoveredByUnits vertices fixedPairs units) :
    (r5NegativeInducedPairClause vertices variablePairs).Valid G := by
  classical
  by_contra hnotValid
  have hvariable : ∀ pair ∈ variablePairs,
      G.Adj pair.1.1 pair.2.1 := by
    intro pair hpair
    have hpairNe :=
      hpairsNe pair (List.mem_append_right fixedPairs hpair)
    by_contra hnonadj
    apply hnotValid
    refine ⟨.neg (r5EdgeName pair.1.1 pair.2.1), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨pair, hpair, rfl⟩
    · intro hinterpret
      exact hnonadj
        ((r5InterpretVariable_edgeName
          G pair.1.1 pair.2.1
            (fun h => hpairNe (Subtype.ext h))).1 hinterpret)
  have hfixed : ∀ pair ∈ fixedPairs, G.Adj pair.1.1 pair.2.1 := by
    intro pair hpair
    have hpairNe :=
      hpairsNe pair (List.mem_append_left variablePairs hpair)
    exact (r5InterpretVariable_edgeName
      G pair.1.1 pair.2.1
        (fun h => hpairNe (Subtype.ext h))).1
      (hunits (.pos (r5EdgeName pair.1.1 pair.2.1))
        (hfixedCovered pair hpair))
  have hwitnessSubset :
      r5InducedPairEdgeFinset vertices
          (fixedPairs ++ variablePairs) ⊆
        (G.induce (vertices : Set (Fin 26))).edgeFinset := by
    intro edge hedge
    rw [r5InducedPairEdgeFinset, List.mem_toFinset] at hedge
    obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hedge
    have hpairAdj : G.Adj pair.1 pair.2 := by
      rcases List.mem_append.mp hpair with hfixedPair | hvariablePair
      · exact hfixed pair hfixedPair
      · exact hvariable pair hvariablePair
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact SimpleGraph.induce_adj.mpr hpairAdj
  have hcardLE :
      #(r5InducedPairEdgeFinset vertices
        (fixedPairs ++ variablePairs)) ≤
        #(G.induce (vertices : Set (Fin 26))).edgeFinset :=
    Finset.card_le_card hwitnessSubset
  have hadmissible := hG vertices hverticesCard
  omega

/-- Semantic name of one exterior-row bit.  The finite bridge only uses
exterior vertices `6, ..., 25` and positions `0, ..., 4`, so this is already
in the edge allocator's increasing-endpoint order. -/
def r5ExteriorPatternName (exterior position : ℕ) : R5VariableName :=
  .edge (position + 1) exterior

/-- Semantic name of one prefix-equality proposition. -/
def r5LexPrefixName (left right position : ℕ) : R5VariableName :=
  .lexPrefix left right position

/-- An exterior-row bit name denotes exactly the corresponding graph bit. -/
theorem r5InterpretVariable_exteriorPatternName
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (exterior position : ℕ) (he : exterior < 26)
    (_hext : 6 ≤ exterior) (hp : position < 5) :
    r5InterpretVariable G (r5ExteriorPatternName exterior position) ↔
      r5ExteriorPatternBit G exterior position := by
  have hleft : position + 1 < 26 := by omega
  simp [r5ExteriorPatternName, r5InterpretVariable,
    r5ExteriorPatternBit, he, hp, hleft]

/-- A prefix name denotes the corresponding semantic prefix equality. -/
theorem r5InterpretVariable_lexPrefixName
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (left right position : ℕ) :
    r5InterpretVariable G (r5LexPrefixName left right position) ↔
      propPrefixEqual
        (r5ExteriorPatternBit G left)
        (r5ExteriorPatternBit G right)
        (position + 1) := by
  rfl

/-- The first lexicographic-order clause `¬left[0] ∨ right[0]`. -/
theorem r5LexClause_zero_order
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (left right : ℕ) (hl : left < 26) (hlext : 6 ≤ left)
    (hr : right < 26) (hrext : 6 ≤ right)
    (hlex : propLexicographicLE
      (r5ExteriorPatternBit G left)
      (r5ExteriorPatternBit G right) 5) :
    R5NamedClause.Valid G
      [.neg (r5ExteriorPatternName left 0),
       .pos (r5ExteriorPatternName right 0)] := by
  by_cases hleft : r5ExteriorPatternBit G left 0
  · refine ⟨.pos (r5ExteriorPatternName right 0), by simp, ?_⟩
    exact (r5InterpretVariable_exteriorPatternName
      G right 0 hr hrext (by omega)).2
        (propLexicographicLE_zero _ _ hlex (by omega) hleft)
  · refine ⟨.neg (r5ExteriorPatternName left 0), by simp, ?_⟩
    intro h
    exact hleft ((r5InterpretVariable_exteriorPatternName
      G left 0 hl hlext (by omega)).1 h)

/-- A later lexicographic-order clause
`¬prefix[i-1] ∨ ¬left[i] ∨ right[i]`. -/
theorem r5LexClause_succ_order
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (left right position : ℕ)
    (hl : left < 26) (hlext : 6 ≤ left)
    (hr : right < 26) (hrext : 6 ≤ right)
    (hposition : 0 < position) (hp : position < 5)
    (hlex : propLexicographicLE
      (r5ExteriorPatternBit G left)
      (r5ExteriorPatternBit G right) 5) :
    R5NamedClause.Valid G
      [.neg (r5LexPrefixName left right (position - 1)),
       .neg (r5ExteriorPatternName left position),
       .pos (r5ExteriorPatternName right position)] := by
  let leftBit := r5ExteriorPatternBit G left
  let rightBit := r5ExteriorPatternBit G right
  by_cases hprefix : propPrefixEqual leftBit rightBit position
  · by_cases hleftBit : leftBit position
    · refine ⟨.pos (r5ExteriorPatternName right position), by simp, ?_⟩
      exact (r5InterpretVariable_exteriorPatternName
        G right position hr hrext hp).2
          (propLexicographicLE_at _ _ hlex hp hprefix hleftBit)
    · refine ⟨.neg (r5ExteriorPatternName left position), by simp, ?_⟩
      intro h
      exact hleftBit ((r5InterpretVariable_exteriorPatternName
        G left position hl hlext hp).1 h)
  · refine ⟨.neg (r5LexPrefixName left right (position - 1)),
      by simp, ?_⟩
    intro h
    apply hprefix
    have hpred : position - 1 + 1 = position := by omega
    simpa [leftBit, rightBit, hpred] using
      (r5InterpretVariable_lexPrefixName
        G left right (position - 1)).1 h

/-- A current prefix implies the preceding prefix. -/
theorem r5LexClause_current_previous
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (left right position : ℕ) (hposition : 0 < position) :
    R5NamedClause.Valid G
      [.neg (r5LexPrefixName left right position),
       .pos (r5LexPrefixName left right (position - 1))] := by
  apply r5NamedClause_valid_neg_pos_of_imp
  intro hcurrent
  have hsemantic :=
    (r5InterpretVariable_lexPrefixName G left right position).1 hcurrent
  apply (r5InterpretVariable_lexPrefixName
    G left right (position - 1)).2
  have hpred : position - 1 + 1 = position := by omega
  simpa [hpred] using
    propPrefixEqual_previous
      (r5ExteriorPatternBit G left)
      (r5ExteriorPatternBit G right) hsemantic

/-- A current prefix equality implies the forward bit implication. -/
theorem r5LexClause_current_forward
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (left right position : ℕ)
    (hl : left < 26) (hlext : 6 ≤ left)
    (hr : right < 26) (hrext : 6 ≤ right)
    (hp : position < 5) :
    R5NamedClause.Valid G
      [.neg (r5LexPrefixName left right position),
       .neg (r5ExteriorPatternName left position),
       .pos (r5ExteriorPatternName right position)] := by
  apply r5NamedClause_valid_neg_neg_pos_of_imp
  intro hcurrent hleftBit
  apply (r5InterpretVariable_exteriorPatternName
    G right position hr hrext hp).2
  exact propPrefixEqual_current_forward _ _
    ((r5InterpretVariable_lexPrefixName
      G left right position).1 hcurrent)
    ((r5InterpretVariable_exteriorPatternName
      G left position hl hlext hp).1 hleftBit)

/-- A current prefix equality implies the reverse bit implication. -/
theorem r5LexClause_current_reverse
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (left right position : ℕ)
    (hl : left < 26) (hlext : 6 ≤ left)
    (hr : right < 26) (hrext : 6 ≤ right)
    (hp : position < 5) :
    R5NamedClause.Valid G
      [.neg (r5LexPrefixName left right position),
       .pos (r5ExteriorPatternName left position),
       .neg (r5ExteriorPatternName right position)] := by
  by_cases hcurrent :
      r5InterpretVariable G (r5LexPrefixName left right position)
  · by_cases hrightBit :
        r5InterpretVariable G (r5ExteriorPatternName right position)
    · refine ⟨.pos (r5ExteriorPatternName left position), by simp, ?_⟩
      apply (r5InterpretVariable_exteriorPatternName
        G left position hl hlext hp).2
      exact propPrefixEqual_current_reverse _ _
        ((r5InterpretVariable_lexPrefixName
          G left right position).1 hcurrent)
        ((r5InterpretVariable_exteriorPatternName
          G right position hr hrext hp).1 hrightBit)
    · exact ⟨.neg (r5ExteriorPatternName right position),
        by simp, hrightBit⟩
  · exact ⟨.neg (r5LexPrefixName left right position),
      by simp, hcurrent⟩

/-- Equal true bits extend the first (empty) prefix. -/
theorem r5LexClause_zero_both_true
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (left right : ℕ)
    (hl : left < 26) (hlext : 6 ≤ left)
    (hr : right < 26) (hrext : 6 ≤ right) :
    R5NamedClause.Valid G
      [.neg (r5ExteriorPatternName left 0),
       .neg (r5ExteriorPatternName right 0),
       .pos (r5LexPrefixName left right 0)] := by
  by_cases hleftBit :
      r5InterpretVariable G (r5ExteriorPatternName left 0)
  · by_cases hrightBit :
        r5InterpretVariable G (r5ExteriorPatternName right 0)
    · refine ⟨.pos (r5LexPrefixName left right 0), by simp, ?_⟩
      apply (r5InterpretVariable_lexPrefixName G left right 0).2
      exact propPrefixEqual_succ_of_both_true _ _
        (propPrefixEqual_zero _ _)
        ((r5InterpretVariable_exteriorPatternName
          G left 0 hl hlext (by omega)).1 hleftBit)
        ((r5InterpretVariable_exteriorPatternName
          G right 0 hr hrext (by omega)).1 hrightBit)
    · exact ⟨.neg (r5ExteriorPatternName right 0), by simp, hrightBit⟩
  · exact ⟨.neg (r5ExteriorPatternName left 0), by simp, hleftBit⟩

/-- Equal false bits extend the first (empty) prefix. -/
theorem r5LexClause_zero_both_false
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (left right : ℕ)
    (hl : left < 26) (hlext : 6 ≤ left)
    (hr : right < 26) (hrext : 6 ≤ right) :
    R5NamedClause.Valid G
      [.pos (r5ExteriorPatternName left 0),
       .pos (r5ExteriorPatternName right 0),
       .pos (r5LexPrefixName left right 0)] := by
  by_cases hleftBit :
      r5InterpretVariable G (r5ExteriorPatternName left 0)
  · exact ⟨.pos (r5ExteriorPatternName left 0), by simp, hleftBit⟩
  · by_cases hrightBit :
        r5InterpretVariable G (r5ExteriorPatternName right 0)
    · exact ⟨.pos (r5ExteriorPatternName right 0), by simp, hrightBit⟩
    · refine ⟨.pos (r5LexPrefixName left right 0), by simp, ?_⟩
      apply (r5InterpretVariable_lexPrefixName G left right 0).2
      exact propPrefixEqual_succ_of_both_false _ _
        (propPrefixEqual_zero _ _)
        (fun h => hleftBit
          ((r5InterpretVariable_exteriorPatternName
            G left 0 hl hlext (by omega)).2 h))
        (fun h => hrightBit
          ((r5InterpretVariable_exteriorPatternName
            G right 0 hr hrext (by omega)).2 h))

/-- Equal true bits extend a nonempty previous prefix. -/
theorem r5LexClause_succ_both_true
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (left right position : ℕ)
    (hl : left < 26) (hlext : 6 ≤ left)
    (hr : right < 26) (hrext : 6 ≤ right)
    (hposition : 0 < position) (hp : position < 5) :
    R5NamedClause.Valid G
      [.neg (r5LexPrefixName left right (position - 1)),
       .neg (r5ExteriorPatternName left position),
       .neg (r5ExteriorPatternName right position),
       .pos (r5LexPrefixName left right position)] := by
  by_cases hprefix :
      r5InterpretVariable G
        (r5LexPrefixName left right (position - 1))
  · by_cases hleftBit :
        r5InterpretVariable G (r5ExteriorPatternName left position)
    · by_cases hrightBit :
          r5InterpretVariable G (r5ExteriorPatternName right position)
      · refine ⟨.pos (r5LexPrefixName left right position), by simp, ?_⟩
        apply (r5InterpretVariable_lexPrefixName
          G left right position).2
        have hpred : position - 1 + 1 = position := by omega
        exact propPrefixEqual_succ_of_both_true _ _
          (by
            simpa [hpred] using
              (r5InterpretVariable_lexPrefixName
                G left right (position - 1)).1 hprefix)
          ((r5InterpretVariable_exteriorPatternName
            G left position hl hlext hp).1 hleftBit)
          ((r5InterpretVariable_exteriorPatternName
            G right position hr hrext hp).1 hrightBit)
      · exact ⟨.neg (r5ExteriorPatternName right position),
          by simp, hrightBit⟩
    · exact ⟨.neg (r5ExteriorPatternName left position),
        by simp, hleftBit⟩
  · exact ⟨.neg (r5LexPrefixName left right (position - 1)),
      by simp, hprefix⟩

/-- Equal false bits extend a nonempty previous prefix. -/
theorem r5LexClause_succ_both_false
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (left right position : ℕ)
    (hl : left < 26) (hlext : 6 ≤ left)
    (hr : right < 26) (hrext : 6 ≤ right)
    (hposition : 0 < position) (hp : position < 5) :
    R5NamedClause.Valid G
      [.neg (r5LexPrefixName left right (position - 1)),
       .pos (r5ExteriorPatternName left position),
       .pos (r5ExteriorPatternName right position),
       .pos (r5LexPrefixName left right position)] := by
  by_cases hprefix :
      r5InterpretVariable G
        (r5LexPrefixName left right (position - 1))
  · by_cases hleftBit :
        r5InterpretVariable G (r5ExteriorPatternName left position)
    · exact ⟨.pos (r5ExteriorPatternName left position),
        by simp, hleftBit⟩
    · by_cases hrightBit :
          r5InterpretVariable G (r5ExteriorPatternName right position)
      · exact ⟨.pos (r5ExteriorPatternName right position),
          by simp, hrightBit⟩
      · refine ⟨.pos (r5LexPrefixName left right position), by simp, ?_⟩
        apply (r5InterpretVariable_lexPrefixName
          G left right position).2
        have hpred : position - 1 + 1 = position := by omega
        exact propPrefixEqual_succ_of_both_false _ _
          (by
            simpa [hpred] using
              (r5InterpretVariable_lexPrefixName
                G left right (position - 1)).1 hprefix)
          (fun h => hleftBit
            ((r5InterpretVariable_exteriorPatternName
              G left position hl hlext hp).2 h))
          (fun h => hrightBit
            ((r5InterpretVariable_exteriorPatternName
              G right position hr hrext hp).2 h))
  · exact ⟨.neg (r5LexPrefixName left right (position - 1)),
      by simp, hprefix⟩

/-- Semantic name of one unary degree-counter proposition. -/
def r5DegreeCounterName
    (vertex : Fin 26) (prefixLength threshold : ℕ) :
    R5VariableName :=
  .degreeCounter vertex prefixLength threshold

/-- A reached threshold remains reached after adding an input. -/
theorem r5DegreeClause_previous_current
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (vertex : Fin 26) (prefixLength threshold : ℕ) :
    R5NamedClause.Valid G
      [.neg (r5DegreeCounterName vertex prefixLength threshold),
       .pos (r5DegreeCounterName vertex (prefixLength + 1) threshold)] := by
  apply r5NamedClause_valid_neg_pos_of_imp
  exact unaryCounter_of_previous (r5IncidentProp G vertex)

/-- Threshold one at the enlarged prefix comes from its previous value or the
new incident edge. -/
theorem r5DegreeClause_current_one_elim
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (vertex : Fin 26) (position : Fin 25) :
    R5NamedClause.Valid G
      [.neg (r5DegreeCounterName vertex (position + 1) 1),
       .pos (r5DegreeCounterName vertex position 1),
       .pos (r5IncidentEdgeName vertex position)] := by
  apply r5NamedClause_valid_neg_pos_pos_of_imp
  intro hcurrent
  rcases unaryCounter_one_elim (r5IncidentProp G vertex) hcurrent with
    hprevious | hinput
  · exact Or.inl hprevious
  · exact Or.inr
      ((r5InterpretVariable_incidentEdgeName G vertex position).2 hinput)

/-- A true new incident edge reaches threshold one. -/
theorem r5DegreeClause_input_current_one
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (vertex : Fin 26) (position : Fin 25) :
    R5NamedClause.Valid G
      [.neg (r5IncidentEdgeName vertex position),
       .pos (r5DegreeCounterName vertex (position + 1) 1)] := by
  apply r5NamedClause_valid_neg_pos_of_imp
  intro hinput
  exact unaryCounter_one_of_input (r5IncidentProp G vertex)
    ((r5InterpretVariable_incidentEdgeName G vertex position).1 hinput)

/-- A successor threshold comes from the same previous threshold or the
preceding previous threshold. -/
theorem r5DegreeClause_current_elim_previous
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (vertex : Fin 26) (position : Fin 25) (threshold : ℕ) :
    R5NamedClause.Valid G
      [.neg (r5DegreeCounterName vertex (position + 1) (threshold + 1)),
       .pos (r5DegreeCounterName vertex position (threshold + 1)),
       .pos (r5DegreeCounterName vertex position threshold)] := by
  apply r5NamedClause_valid_neg_pos_pos_of_imp
  exact unaryCounter_succ_elim_previous (r5IncidentProp G vertex)

/-- If the new successor threshold was not already present, its input edge is
true. -/
theorem r5DegreeClause_current_elim_input
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (vertex : Fin 26) (position : Fin 25) (threshold : ℕ) :
    R5NamedClause.Valid G
      [.neg (r5DegreeCounterName vertex (position + 1) (threshold + 1)),
       .pos (r5DegreeCounterName vertex position (threshold + 1)),
       .pos (r5IncidentEdgeName vertex position)] := by
  apply r5NamedClause_valid_neg_pos_pos_of_imp
  intro hcurrent
  by_cases hprevious :
      unaryCounter (r5IncidentProp G vertex) position (threshold + 1)
  · exact Or.inl hprevious
  · exact Or.inr
      ((r5InterpretVariable_incidentEdgeName G vertex position).2
        (unaryCounter_succ_elim_input
          (r5IncidentProp G vertex) hcurrent hprevious))

/-- A previous threshold and true input reach the next threshold. -/
theorem r5DegreeClause_previous_input_current
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (vertex : Fin 26) (position : Fin 25) (threshold : ℕ) :
    R5NamedClause.Valid G
      [.neg (r5DegreeCounterName vertex position threshold),
       .neg (r5IncidentEdgeName vertex position),
       .pos (r5DegreeCounterName vertex (position + 1) (threshold + 1))] := by
  apply r5NamedClause_valid_neg_neg_pos_of_imp
  intro hprevious hinput
  exact unaryCounter_succ_of_previous_of_input
    (r5IncidentProp G vertex) hprevious
    ((r5InterpretVariable_incidentEdgeName G vertex position).1 hinput)

/-- At a diagonal threshold, the preceding diagonal threshold is necessary. -/
theorem r5DegreeClause_diagonal_previous
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (vertex : Fin 26) (position : Fin 25) :
    R5NamedClause.Valid G
      [.neg (r5DegreeCounterName vertex (position + 1) (position + 1)),
       .pos (r5DegreeCounterName vertex position position)] := by
  apply r5NamedClause_valid_neg_pos_of_imp
  exact unaryCounter_diagonal_elim_previous (r5IncidentProp G vertex)

/-- At a diagonal threshold, the new input is necessary. -/
theorem r5DegreeClause_diagonal_input
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (vertex : Fin 26) (position : Fin 25) :
    R5NamedClause.Valid G
      [.neg (r5DegreeCounterName vertex (position + 1) (position + 1)),
       .pos (r5IncidentEdgeName vertex position)] := by
  apply r5NamedClause_valid_neg_pos_of_imp
  intro hcurrent
  exact (r5InterpretVariable_incidentEdgeName G vertex position).2
    (unaryCounter_diagonal_elim_input
      (r5IncidentProp G vertex) hcurrent)

/-- Positive exact-degree terminal unit. -/
theorem r5DegreeClause_terminal_five
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ v, G.degree v = 5) (vertex : Fin 26) :
    R5NamedClause.Valid G
      [.pos (r5DegreeCounterName vertex 25 5)] :=
  ⟨.pos (r5DegreeCounterName vertex 25 5), by simp,
    (r5DegreeCounterTerminal G hregular vertex).1⟩

/-- Negative exact-degree overflow unit. -/
theorem r5DegreeClause_terminal_six
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ v, G.degree v = 5) (vertex : Fin 26) :
    R5NamedClause.Valid G
      [.neg (r5DegreeCounterName vertex 25 6)] :=
  ⟨.neg (r5DegreeCounterName vertex 25 6), by simp,
    (r5DegreeCounterTerminal G hregular vertex).2⟩

end Erdos617
