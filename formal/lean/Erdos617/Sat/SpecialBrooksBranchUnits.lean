/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.Sat.SpecialBrooksOrbitBridge

/-!
# Semantic unit assignments for the E058 neighborhood branches

The reduced LRAT cores expose their retained primary assignments in
core-dependent orders.  This file defines one canonical ordering of the same
35 graph literals and proves those literals directly from the normalized
neighborhood and its certified orbit representative.  Certificate wrappers
may use membership, rather than list order, to supply their exact unit lists.
-/

@[expose] public section

open Finset

namespace Erdos617

/-- A signed semantic edge literal with the sign selected by a Boolean. -/
def r5EdgeLiteralFromBool
    (left right : Fin 26) (value : Bool) : R5NamedLiteral :=
  if value then
    .pos (.edge left right)
  else
    .neg (.edge left right)

/-- The literal selected from an actual adjacency decision is true. -/
theorem r5EdgeLiteralFromBool_true
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (left right : Fin 26) (value : Bool)
    (hvalue : decide (G.Adj left right) = value) :
    r5NamedLiteralTrue G
      (r5EdgeLiteralFromBool left right value) := by
  cases value <;>
    simp_all [r5EdgeLiteralFromBool, r5NamedLiteralTrue,
      r5InterpretVariable]

/-- The 25 units specifying that zero has precisely neighbors `1, ..., 5`. -/
def r5CanonicalZeroNeighborhoodUnits : List R5NamedLiteral :=
  List.ofFn fun index : Fin 25 =>
    let vertex : Fin 26 := index.succ
    r5EdgeLiteralFromBool 0 vertex
      (decide (vertex ∈ r5FixedNeighbors))

/-- The ten unordered pairs in the neighborhood-certificate bit order. -/
def r5NeighborhoodPair : Fin 10 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2),
    (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

/-- Lift a zero-based neighborhood label to the graph label `1, ..., 5`. -/
def r5NeighborVertex (index : Fin 5) : Fin 26 :=
  ⟨(index : ℕ) + 1, by omega⟩

/-- The ten signed internal-neighborhood units for one orbit representative. -/
def r5CanonicalRepresentativeUnits
    (branch : Fin 26) : List R5NamedLiteral :=
  List.ofFn fun index : Fin 10 =>
    let endpoints := r5NeighborhoodPair index
    r5EdgeLiteralFromBool
      (r5NeighborVertex endpoints.1)
      (r5NeighborVertex endpoints.2)
      (edgeVectorOfCode
        (r5NeighborhoodRepresentativeCode branch) index)

/-- Canonical set and order of the 35 E038 primary branch units. -/
def r5CanonicalBranchUnits (branch : Fin 26) : List R5NamedLiteral :=
  r5CanonicalZeroNeighborhoodUnits ++
    r5CanonicalRepresentativeUnits branch

theorem r5CanonicalZeroNeighborhoodUnits_allTrue
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors) :
    R5NamedClause.AllTrue G r5CanonicalZeroNeighborhoodUnits := by
  intro literal hliteral
  rw [r5CanonicalZeroNeighborhoodUnits, List.mem_ofFn'] at hliteral
  obtain ⟨index, rfl⟩ := hliteral
  apply r5EdgeLiteralFromBool_true
  have hadj :
      G.Adj 0 index.succ ↔ index.succ ∈ r5FixedNeighbors := by
    rw [← SimpleGraph.mem_neighborFinset, hneighbor]
  by_cases hedge : G.Adj 0 index.succ
  · have hmem := hadj.mp hedge
    simp [hedge, hmem]
  · have hnotMem : index.succ ∉ r5FixedNeighbors :=
      fun hmem => hedge (hadj.mpr hmem)
    simp [hedge, hnotMem]

theorem r5CanonicalRepresentativeUnits_allTrue
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (branch : Fin 26)
    (horbit : ∀ left right : Fin 5,
      decide (G.Adj (r5NeighborVertex left) (r5NeighborVertex right)) =
        r5FiveVertexAdjacency
          (edgeVectorOfCode (r5NeighborhoodRepresentativeCode branch))
          left right) :
    R5NamedClause.AllTrue G
      (r5CanonicalRepresentativeUnits branch) := by
  intro literal hliteral
  rw [r5CanonicalRepresentativeUnits, List.mem_ofFn'] at hliteral
  obtain ⟨index, rfl⟩ := hliteral
  apply r5EdgeLiteralFromBool_true
  have hpair := horbit
    (r5NeighborhoodPair index).1
    (r5NeighborhoodPair index).2
  fin_cases index <;>
    simpa [r5NeighborhoodPair, r5FiveVertexAdjacency,
      r5NeighborVertex] using hpair

theorem r5CanonicalBranchUnits_allTrue
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (branch : Fin 26)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (horbit : ∀ left right : Fin 5,
      decide (G.Adj (r5NeighborVertex left) (r5NeighborVertex right)) =
        r5FiveVertexAdjacency
          (edgeVectorOfCode (r5NeighborhoodRepresentativeCode branch))
          left right) :
    R5NamedClause.AllTrue G (r5CanonicalBranchUnits branch) := by
  intro literal hliteral
  rw [r5CanonicalBranchUnits, List.mem_append] at hliteral
  rcases hliteral with hliteral | hliteral
  · exact r5CanonicalZeroNeighborhoodUnits_allTrue
      G hneighbor literal hliteral
  · exact r5CanonicalRepresentativeUnits_allTrue
      G branch horbit literal hliteral

/-- Truth of a canonical unit list supplies any reordered sublist. -/
theorem R5NamedClause.AllTrue.of_subset
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    {smaller larger : List R5NamedLiteral}
    (hlarger : R5NamedClause.AllTrue G larger)
    (hsubset : ∀ literal ∈ smaller, literal ∈ larger) :
    R5NamedClause.AllTrue G smaller :=
  fun literal hliteral => hlarger literal (hsubset literal hliteral)

end Erdos617
