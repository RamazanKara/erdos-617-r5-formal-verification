/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.Sat.SpecialBrooksZeroAnchorSort

/-!
# Complete graph bridge for the six E045 branches

This file composes the zero-pattern existence, anchor normalization, and
within-class sorting theorems.  It also supplies the exact 59 primary units
used by each E045 semantic closure, modulo harmless list reordering.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

def r5CanonicalAnchorFixedNeighborUnits : List R5NamedLiteral :=
  List.ofFn fun index : Fin 5 =>
    let vertex := r5NeighborVertex index
    r5EdgeLiteralFromBool vertex 6
      (decide (vertex ∈ r5FixedAnchorNeighbors))

def r5CanonicalAnchorExteriorUnits : List R5NamedLiteral :=
  List.ofFn fun index : Fin 19 =>
    let vertex : Fin 26 := ⟨(index : ℕ) + 7, by omega⟩
    r5EdgeLiteralFromBool 6 vertex
      (decide (vertex ∈ r5FixedAnchorNeighbors))

def r5CanonicalAnchorUnits : List R5NamedLiteral :=
  r5CanonicalAnchorFixedNeighborUnits ++
    r5CanonicalAnchorExteriorUnits

def r5CanonicalE045Units (branch : Fin 26) :
    List R5NamedLiteral :=
  r5CanonicalBranchUnits branch ++ r5CanonicalAnchorUnits

theorem r5AnchorEdgeLiteral_true
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hanchor :
      G.neighborFinset 6 = r5FixedAnchorNeighbors)
    (vertex : Fin 26) :
    r5NamedLiteralTrue G
      (r5EdgeLiteralFromBool 6 vertex
        (decide (vertex ∈ r5FixedAnchorNeighbors))) := by
  apply r5EdgeLiteralFromBool_true
  have hadj :
      G.Adj 6 vertex ↔ vertex ∈ r5FixedAnchorNeighbors := by
    rw [← SimpleGraph.mem_neighborFinset, hanchor]
  by_cases hedge : G.Adj 6 vertex
  · have hmem := hadj.mp hedge
    simp [hedge, hmem]
  · have hnotMem : vertex ∉ r5FixedAnchorNeighbors :=
      fun hmem => hedge (hadj.mpr hmem)
    simp [hedge, hnotMem]

theorem r5FixedNeighborAnchorEdgeLiteral_true
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hanchor :
      G.neighborFinset 6 = r5FixedAnchorNeighbors)
    (vertex : Fin 26) :
    r5NamedLiteralTrue G
      (r5EdgeLiteralFromBool vertex 6
        (decide (vertex ∈ r5FixedAnchorNeighbors))) := by
  apply r5EdgeLiteralFromBool_true
  have hadj :
      G.Adj vertex 6 ↔ vertex ∈ r5FixedAnchorNeighbors := by
    rw [G.adj_comm, ← SimpleGraph.mem_neighborFinset, hanchor]
  by_cases hedge : G.Adj vertex 6
  · have hmem := hadj.mp hedge
    simp [hedge, hmem]
  · have hnotMem : vertex ∉ r5FixedAnchorNeighbors :=
      fun hmem => hedge (hadj.mpr hmem)
    simp [hedge, hnotMem]

theorem r5CanonicalAnchorUnits_allTrue
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hanchor :
      G.neighborFinset 6 = r5FixedAnchorNeighbors) :
    R5NamedClause.AllTrue G r5CanonicalAnchorUnits := by
  intro literal hliteral
  rw [r5CanonicalAnchorUnits, List.mem_append] at hliteral
  rcases hliteral with hfixed | hexterior
  · rw [r5CanonicalAnchorFixedNeighborUnits,
      List.mem_ofFn'] at hfixed
    obtain ⟨index, rfl⟩ := hfixed
    exact r5FixedNeighborAnchorEdgeLiteral_true G hanchor _
  · rw [r5CanonicalAnchorExteriorUnits,
      List.mem_ofFn'] at hexterior
    obtain ⟨index, rfl⟩ := hexterior
    exact r5AnchorEdgeLiteral_true G hanchor _

theorem r5CanonicalE045Units_allTrue
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (branch : Fin 26)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (hanchor :
      G.neighborFinset 6 = r5FixedAnchorNeighbors)
    (horbit : ∀ left right : Fin 5,
      decide (G.Adj (r5NeighborVertex left)
        (r5NeighborVertex right)) =
      r5FiveVertexAdjacency
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode branch))
        left right) :
    R5NamedClause.AllTrue G (r5CanonicalE045Units branch) := by
  intro literal hliteral
  rw [r5CanonicalE045Units, List.mem_append] at hliteral
  rcases hliteral with hbranch | hanchorLiteral
  · exact r5CanonicalBranchUnits_allTrue
      G branch hneighbor horbit literal hbranch
  · exact r5CanonicalAnchorUnits_allTrue
      G hanchor literal hanchorLiteral

/-- Every canonical branch `20, ..., 25` can be put into the exact E045
zero-anchor quotient while preserving all graph hypotheses. -/
theorem exists_r5CanonicalE045Branch
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (branch : Fin 26) (hbranch : 20 ≤ branch)
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hG : Admissible G)
    (hclique : G.CliqueFree 6)
    (hindep : G.IndepSetFree 6)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (horbit : ∀ left right : Fin 5,
      decide (G.Adj (r5NeighborVertex left)
        (r5NeighborVertex right)) =
      r5FiveVertexAdjacency
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode branch))
        left right) :
    ∃ relabeling : Equiv.Perm (Fin 26),
      let H := relabelGraph G relabeling
      (∀ vertex, H.degree vertex = 5) ∧
      Admissible H ∧
      H.CliqueFree 6 ∧
      H.IndepSetFree 6 ∧
      H.neighborFinset 0 = r5FixedNeighbors ∧
      H.neighborFinset 6 = r5FixedAnchorNeighbors ∧
      R5ComparisonsSorted H r5ZeroAnchorComparisons ∧
      ∀ left right : Fin 5,
        decide (H.Adj (r5NeighborVertex left)
          (r5NeighborVertex right)) =
        r5FiveVertexAdjacency
          (edgeVectorOfCode
            (r5NeighborhoodRepresentativeCode branch))
          left right := by
  obtain ⟨anchor, hanchor, hzero⟩ :=
    exists_r5ZeroPatternExterior_of_final_branch
      G branch hbranch hregular hneighbor horbit
  obtain ⟨firstRelabeling, hfirstFixed, -, hfirstZero, hfirstAnchor⟩ :=
    exists_r5RelabelGraph_anchor_six
      G hregular hneighbor anchor hanchor hzero
  let firstGraph := relabelGraph G firstRelabeling
  have hfirstRegular :
      ∀ vertex, firstGraph.degree vertex = 5 := by
    intro vertex
    dsimp [firstGraph]
    rw [relabelGraph_degree]
    exact hregular _
  have hfirstOrbit (left right : Fin 5) :
      decide (firstGraph.Adj (r5NeighborVertex left)
        (r5NeighborVertex right)) =
      r5FiveVertexAdjacency
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode branch))
        left right := by
    change decide (G.Adj
      (firstRelabeling (r5NeighborVertex left))
      (firstRelabeling (r5NeighborVertex right))) = _
    rw [hfirstFixed _ (by
        change (left : ℕ) + 1 < 6
        omega),
      hfirstFixed _ (by
        change (right : ℕ) + 1 < 6
        omega)]
    exact horbit left right
  obtain ⟨secondRelabeling, hsecondFixed,
      hsecondZero, hsecondAnchor, hsecondSorted⟩ :=
    exists_r5ZeroAnchorSortedRelabel
      firstGraph hfirstRegular hfirstZero hfirstAnchor
  let finalGraph := relabelGraph firstGraph secondRelabeling
  have hfinalOrbit (left right : Fin 5) :
      decide (finalGraph.Adj (r5NeighborVertex left)
        (r5NeighborVertex right)) =
      r5FiveVertexAdjacency
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode branch))
        left right := by
    change decide (firstGraph.Adj
      (secondRelabeling (r5NeighborVertex left))
      (secondRelabeling (r5NeighborVertex right))) = _
    rw [hsecondFixed _ (by
        change (left : ℕ) + 1 < 7
        omega),
      hsecondFixed _ (by
        change (right : ℕ) + 1 < 7
        omega)]
    exact hfirstOrbit left right
  let finalRelabeling := secondRelabeling.trans firstRelabeling
  refine ⟨finalRelabeling, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro vertex
    rw [relabelGraph_degree]
    exact hregular _
  · change Admissible finalGraph
    exact (admissible_relabelGraph_iff
      firstGraph secondRelabeling).2
      ((admissible_relabelGraph_iff G firstRelabeling).2 hG)
  · change finalGraph.CliqueFree 6
    exact (cliqueFree_relabelGraph_iff
      firstGraph secondRelabeling 6).2
      ((cliqueFree_relabelGraph_iff G firstRelabeling 6).2 hclique)
  · change finalGraph.IndepSetFree 6
    exact (indepSetFree_relabelGraph_iff
      firstGraph secondRelabeling 6).2
      ((indepSetFree_relabelGraph_iff G firstRelabeling 6).2 hindep)
  · change finalGraph.neighborFinset 0 = r5FixedNeighbors
    exact hsecondZero
  · change finalGraph.neighborFinset 6 = r5FixedAnchorNeighbors
    exact hsecondAnchor
  · change R5ComparisonsSorted finalGraph r5ZeroAnchorComparisons
    exact hsecondSorted
  · exact hfinalOrbit

end Erdos617
