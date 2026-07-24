/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.Sat.NeighborhoodOrbitCertificate

/-!
# Graph bridge for the E058 neighborhood-orbit certificate

This file connects the generated ten-bit orbit certificate to a normalized
special-Brooks graph.  In particular, the ten bits are proved to count the
open-neighborhood edges exactly, so admissibility supplies the certificate's
six-edge premise.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

def r5NeighborhoodEdgeBits
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] :
    Fin 10 → Bool :=
  ![decide (G.Adj 1 2), decide (G.Adj 1 3),
    decide (G.Adj 1 4), decide (G.Adj 1 5),
    decide (G.Adj 2 3), decide (G.Adj 2 4),
    decide (G.Adj 2 5), decide (G.Adj 3 4),
    decide (G.Adj 3 5), decide (G.Adj 4 5)]

noncomputable def r5FixedNeighborsEquivNeighborSet
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors) :
    Fin 5 ≃ (G.neighborFinset 0 : Set (Fin 26)) where
  toFun index :=
    ⟨⟨(index : ℕ) + 1, by omega⟩, by
      rw [hneighbor]
      fin_cases index <;> decide⟩
  invFun vertex :=
    ⟨(vertex.1 : ℕ) - 1, by
      have hmem : vertex.1 ∈ r5FixedNeighbors := by
        rw [← hneighbor]
        exact vertex.property
      simp only [r5FixedNeighbors, mem_insert, mem_singleton] at hmem
      rcases hmem with h | h | h | h | h
      all_goals omega⟩
  left_inv index := by
    ext
    simp
  right_inv vertex := by
    ext
    have hmem : vertex.1 ∈ r5FixedNeighbors := by
      rw [← hneighbor]
      exact vertex.property
    simp only [r5FixedNeighbors, mem_insert, mem_singleton] at hmem
    rcases hmem with h | h | h | h | h
    all_goals
      have hv := congrArg Fin.val h
      change ((vertex.1 : ℕ) - 1) + 1 = vertex.1
      omega

theorem r5NeighborhoodEdgeBits_sum_eq_internal
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors) :
    (∑ index, edgeBit (r5NeighborhoodEdgeBits G index)) =
      neighborhoodInternalEdgeCount G 0 := by
  let R := G.induce (G.neighborFinset 0 : Set (Fin 26))
  let e := r5FixedNeighborsEquivNeighborSet G hneighbor
  let H : SimpleGraph (Fin 5) := R.comap e
  have h01 : H.Adj 0 1 ↔ G.Adj 1 2 := by rfl
  have h02 : H.Adj 0 2 ↔ G.Adj 1 3 := by rfl
  have h03 : H.Adj 0 3 ↔ G.Adj 1 4 := by rfl
  have h04 : H.Adj 0 4 ↔ G.Adj 1 5 := by rfl
  have h12 : H.Adj 1 2 ↔ G.Adj 2 3 := by rfl
  have h13 : H.Adj 1 3 ↔ G.Adj 2 4 := by rfl
  have h14 : H.Adj 1 4 ↔ G.Adj 2 5 := by rfl
  have h23 : H.Adj 2 3 ↔ G.Adj 3 4 := by rfl
  have h24 : H.Adj 2 4 ↔ G.Adj 3 5 := by rfl
  have h34 : H.Adj 3 4 ↔ G.Adj 4 5 := by rfl
  have hd0 := fin_five_degree_zero_formula H
  have hd1 := fin_five_degree_one_formula H
  have hd2 := fin_five_degree_two_formula H
  have hd3 := fin_five_degree_three_formula H
  have hd4 := fin_five_degree_four_formula H
  have hhandshake := H.sum_degrees_eq_twice_card_edges
  have hbits :
      (∑ index, edgeBit (r5NeighborhoodEdgeBits G index)) =
        (if G.Adj 1 2 then 1 else 0) +
        (if G.Adj 1 3 then 1 else 0) +
        (if G.Adj 1 4 then 1 else 0) +
        (if G.Adj 1 5 then 1 else 0) +
        (if G.Adj 2 3 then 1 else 0) +
        (if G.Adj 2 4 then 1 else 0) +
        (if G.Adj 2 5 then 1 else 0) +
        (if G.Adj 3 4 then 1 else 0) +
        (if G.Adj 3 5 then 1 else 0) +
        (if G.Adj 4 5 then 1 else 0) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp [r5NeighborhoodEdgeBits, edgeBit, Nat.add_assoc]
  have hdegrees :
      (∑ vertex, H.degree vertex) =
        H.degree 0 + H.degree 1 + H.degree 2 +
          H.degree 3 + H.degree 4 := by
    simp [Fin.sum_univ_succ, Nat.add_assoc]
    rfl
  rw [hdegrees, hd0, hd1, hd2, hd3, hd4] at hhandshake
  simp only [h01, h02, h03, h04, h12, h13, h14, h23, h24, h34]
    at hhandshake
  have hcardH : #H.edgeFinset =
      #(G.induce (G.neighborFinset 0 : Set (Fin 26))).edgeFinset := by
    simpa [H, R] using (SimpleGraph.Iso.comap e R).card_edgeFinset_eq
  rw [neighborhoodInternalEdgeCount_eq_induce, ← hcardH]
  rw [hbits]
  omega

theorem r5NeighborhoodEdgeBits_sum_le_six_of_admissible
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hG : Admissible G)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors) :
    (∑ index, edgeBit (r5NeighborhoodEdgeBits G index)) ≤ 6 := by
  rw [r5NeighborhoodEdgeBits_sum_eq_internal G hneighbor]
  exact neighborhoodInternalEdgeCount_le_six_of_admissible_degree_five
    G hG 0 (hregular 0)

/-- The labels `1, ..., 5`, viewed as the fixed neighborhood of vertex zero. -/
def r5FixedNeighborLabelEquiv :
    Fin 5 ≃ {vertex : Fin 26 // vertex ∈ r5FixedNeighbors} where
  toFun index :=
    ⟨⟨(index : ℕ) + 1, by omega⟩, by
      fin_cases index <;> decide⟩
  invFun vertex :=
    ⟨(vertex.1 : ℕ) - 1, by
      have hmem := vertex.property
      simp only [r5FixedNeighbors, mem_insert, mem_singleton] at hmem
      rcases hmem with h | h | h | h | h
      all_goals omega⟩
  left_inv index := by
    ext
    simp
  right_inv vertex := by
    ext
    have hmem := vertex.property
    simp only [r5FixedNeighbors, mem_insert, mem_singleton] at hmem
    rcases hmem with h | h | h | h | h
    all_goals
      have hv := congrArg Fin.val h
      change ((vertex.1 : ℕ) - 1) + 1 = vertex.1
      omega

/-- Extend a permutation of the five neighbor labels to all 26 labels,
acting identically off `{1, ..., 5}`. -/
noncomputable def r5NeighborRelabelPerm
    (permutation : Equiv.Perm (Fin 5)) : Equiv.Perm (Fin 26) :=
  let neighborPermutation :
      Equiv.Perm {vertex : Fin 26 // vertex ∈ r5FixedNeighbors} :=
    r5FixedNeighborLabelEquiv.symm.trans
      (permutation.trans r5FixedNeighborLabelEquiv)
  neighborPermutation.subtypeCongr (Equiv.refl _)

@[simp]
theorem r5NeighborRelabelPerm_apply_neighbor
    (permutation : Equiv.Perm (Fin 5)) (index : Fin 5) :
    r5NeighborRelabelPerm permutation
        ⟨(index : ℕ) + 1, by omega⟩ =
      ⟨(permutation index : ℕ) + 1, by omega⟩ := by
  have hmem :
      (⟨(index : ℕ) + 1, by omega⟩ : Fin 26) ∈
        r5FixedNeighbors := by
    fin_cases index <;> decide
  rw [r5NeighborRelabelPerm, Equiv.Perm.subtypeCongr.left_apply
    (h := hmem)]
  rfl

@[simp]
theorem r5NeighborRelabelPerm_apply_of_notMem
    (permutation : Equiv.Perm (Fin 5)) (vertex : Fin 26)
    (hvertex : vertex ∉ r5FixedNeighbors) :
    r5NeighborRelabelPerm permutation vertex = vertex := by
  rw [r5NeighborRelabelPerm, Equiv.Perm.subtypeCongr.right_apply
    (h := hvertex)]
  rfl

@[simp]
theorem r5NeighborRelabelPerm_zero
    (permutation : Equiv.Perm (Fin 5)) :
    r5NeighborRelabelPerm permutation 0 = 0 :=
  r5NeighborRelabelPerm_apply_of_notMem permutation 0
    zero_notMem_r5FixedNeighbors

@[simp]
theorem r5NeighborRelabelPerm_apply_exterior
    (permutation : Equiv.Perm (Fin 5)) (vertex : Fin 26)
    (hvertex : 6 ≤ vertex) :
    r5NeighborRelabelPerm permutation vertex = vertex := by
  apply r5NeighborRelabelPerm_apply_of_notMem
  simp only [r5FixedNeighbors, mem_insert, mem_singleton]
  omega

/-- The ten stored bits are the exact adjacency relation on labels
`1, ..., 5`, including symmetry and the loopless diagonal. -/
theorem r5FiveVertexAdjacency_edgeBits
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (left right : Fin 5) :
    r5FiveVertexAdjacency (r5NeighborhoodEdgeBits G) left right =
      decide (G.Adj
        ⟨(left : ℕ) + 1, by omega⟩
        ⟨(right : ℕ) + 1, by omega⟩) := by
  fin_cases left <;> fin_cases right <;>
    simp [r5FiveVertexAdjacency, r5NeighborhoodEdgeBits,
      SimpleGraph.adj_comm]

/-- Admissibility places every normalized neighborhood in one of the 26
certified isomorphism classes.  The witnessing vertex permutation is extended
to all labels while fixing vertex zero and every exterior vertex. -/
theorem exists_r5NeighborRelabel_representative
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hG : Admissible G)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors) :
    ∃ branch : Fin 26, ∃ permutation : Equiv.Perm (Fin 5),
      let relabeling := r5NeighborRelabelPerm permutation
      (relabelGraph G relabeling).neighborFinset 0 = r5FixedNeighbors ∧
      (∀ vertex : Fin 26, 6 ≤ vertex → relabeling vertex = vertex) ∧
      ∀ left right : Fin 5,
        decide ((relabelGraph G relabeling).Adj
          ⟨(left : ℕ) + 1, by omega⟩
          ⟨(right : ℕ) + 1, by omega⟩) =
        r5FiveVertexAdjacency
          (edgeVectorOfCode (r5NeighborhoodRepresentativeCode branch))
          left right := by
  have hedgeCount :=
    r5NeighborhoodEdgeBits_sum_le_six_of_admissible
      G hregular hG hneighbor
  obtain ⟨branch, permutation, horbit⟩ :=
    r5_neighborhood_orbit_check (r5NeighborhoodEdgeBits G) hedgeCount
  refine ⟨branch, permutation, ?_, ?_, ?_⟩
  · ext vertex
    simp only [SimpleGraph.mem_neighborFinset, relabelGraph_adj_iff,
      r5NeighborRelabelPerm_zero]
    constructor
    · intro hadj
      have hmem : r5NeighborRelabelPerm permutation vertex ∈
          r5FixedNeighbors := by
        rw [← hneighbor, SimpleGraph.mem_neighborFinset]
        exact hadj
      by_contra hvertex
      rw [r5NeighborRelabelPerm_apply_of_notMem permutation vertex hvertex]
        at hmem
      exact hvertex hmem
    · intro hmem
      rw [← SimpleGraph.mem_neighborFinset, hneighbor]
      exact (show r5NeighborRelabelPerm permutation vertex ∈
        r5FixedNeighbors by
          let index := r5FixedNeighborLabelEquiv.symm ⟨vertex, hmem⟩
          have hvertex :
              vertex =
                ⟨(index : ℕ) + 1, by omega⟩ := by
            exact (congrArg Subtype.val
              (r5FixedNeighborLabelEquiv.apply_symm_apply
                ⟨vertex, hmem⟩)).symm
          rw [hvertex, r5NeighborRelabelPerm_apply_neighbor]
          exact (r5FixedNeighborLabelEquiv (permutation index)).property)
  · exact r5NeighborRelabelPerm_apply_exterior permutation
  · intro left right
    rw [show decide ((relabelGraph G
          (r5NeighborRelabelPerm permutation)).Adj
          ⟨(left : ℕ) + 1, by omega⟩
          ⟨(right : ℕ) + 1, by omega⟩) =
        decide (G.Adj
          ⟨(permutation left : ℕ) + 1, by omega⟩
          ⟨(permutation right : ℕ) + 1, by omega⟩) by
      simp only [relabelGraph_adj_iff,
        r5NeighborRelabelPerm_apply_neighbor]]
    rw [← r5FiveVertexAdjacency_edgeBits G
      (permutation left) (permutation right)]
    exact horbit left right

/-- After the neighborhood orbit has been chosen, the remaining exterior
labels can be sorted without changing that orbit.  This packages the two
symmetry reductions in exactly the form needed by the E038 branch theorems. -/
theorem exists_r5CanonicalSpecialBrooksBranch_of_normalized
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hG : Admissible G)
    (hclique : G.CliqueFree 6)
    (hindep : G.IndepSetFree 6)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors) :
    ∃ branch : Fin 26, ∃ relabeling : Equiv.Perm (Fin 26),
      let H := relabelGraph G relabeling
      (∀ vertex, H.degree vertex = 5) ∧
      Admissible H ∧
      H.CliqueFree 6 ∧
      H.IndepSetFree 6 ∧
      H.neighborFinset 0 = r5FixedNeighbors ∧
      R5ComparisonsSorted H r5FullExteriorComparisons ∧
      ∀ left right : Fin 5,
        decide (H.Adj
          ⟨(left : ℕ) + 1, by omega⟩
          ⟨(right : ℕ) + 1, by omega⟩) =
        r5FiveVertexAdjacency
          (edgeVectorOfCode (r5NeighborhoodRepresentativeCode branch))
          left right := by
  obtain ⟨branch, permutation, hfirstNeighbor, -, hfirstOrbit⟩ :=
    exists_r5NeighborRelabel_representative
      G hregular hG hneighbor
  let firstRelabeling := r5NeighborRelabelPerm permutation
  let firstGraph := relabelGraph G firstRelabeling
  let secondRelabeling := r5SortExteriorPerm firstGraph
  let finalGraph := relabelGraph firstGraph secondRelabeling
  have hfinalNeighbor :
      finalGraph.neighborFinset 0 = r5FixedNeighbors := by
    have hsubset :
        r5FixedNeighbors ⊆ finalGraph.neighborFinset 0 := by
      intro vertex hvertex
      have hvertexLT : vertex < 6 := by
        simp only [r5FixedNeighbors, mem_insert, mem_singleton] at hvertex
        rcases hvertex with h | h | h | h | h
        all_goals omega
      rw [SimpleGraph.mem_neighborFinset]
      change firstGraph.Adj
        (secondRelabeling 0) (secondRelabeling vertex)
      rw [show secondRelabeling 0 = 0 by
          exact r5SortExteriorPerm_apply_of_lt_six firstGraph 0 (by omega),
        show secondRelabeling vertex = vertex by
          exact r5SortExteriorPerm_apply_of_lt_six
            firstGraph vertex hvertexLT,
        ← SimpleGraph.mem_neighborFinset, hfirstNeighbor]
      exact hvertex
    have hdegree : finalGraph.degree 0 = 5 := by
      change (relabelGraph firstGraph secondRelabeling).degree 0 = 5
      rw [relabelGraph_degree,
        show secondRelabeling 0 = 0 by
          exact r5SortExteriorPerm_apply_of_lt_six
            firstGraph 0 (by omega)]
      change (relabelGraph G firstRelabeling).degree 0 = 5
      rw [relabelGraph_degree]
      exact hregular _
    have hcard :
        #(finalGraph.neighborFinset 0) ≤ #r5FixedNeighbors := by
      simp [hdegree]
    exact (Finset.eq_of_subset_of_card_le hsubset hcard).symm
  have hfinalOrbit (left right : Fin 5) :
      decide (finalGraph.Adj
        ⟨(left : ℕ) + 1, by omega⟩
        ⟨(right : ℕ) + 1, by omega⟩) =
      r5FiveVertexAdjacency
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode branch))
        left right := by
    change decide (firstGraph.Adj
      (secondRelabeling ⟨(left : ℕ) + 1, by omega⟩)
      (secondRelabeling ⟨(right : ℕ) + 1, by omega⟩)) = _
    rw [show secondRelabeling
          ⟨(left : ℕ) + 1, by omega⟩ =
          ⟨(left : ℕ) + 1, by omega⟩ by
        exact r5SortExteriorPerm_apply_of_lt_six
          firstGraph _ (by
            change (left : ℕ) + 1 < 6
            omega),
      show secondRelabeling
          ⟨(right : ℕ) + 1, by omega⟩ =
          ⟨(right : ℕ) + 1, by omega⟩ by
        exact r5SortExteriorPerm_apply_of_lt_six
          firstGraph _ (by
            change (right : ℕ) + 1 < 6
            omega)]
    exact hfirstOrbit left right
  let finalRelabeling := secondRelabeling.trans firstRelabeling
  refine ⟨branch, finalRelabeling, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro vertex
    rw [relabelGraph_degree]
    exact hregular _
  · change Admissible finalGraph
    exact (admissible_relabelGraph_iff firstGraph secondRelabeling).2
      ((admissible_relabelGraph_iff G firstRelabeling).2 hG)
  · change finalGraph.CliqueFree 6
    exact (cliqueFree_relabelGraph_iff firstGraph secondRelabeling 6).2
      ((cliqueFree_relabelGraph_iff G firstRelabeling 6).2 hclique)
  · change finalGraph.IndepSetFree 6
    exact (indepSetFree_relabelGraph_iff firstGraph secondRelabeling 6).2
      ((indepSetFree_relabelGraph_iff G firstRelabeling 6).2 hindep)
  · change finalGraph.neighborFinset 0 = r5FixedNeighbors
    exact hfinalNeighbor
  · change R5ComparisonsSorted finalGraph r5FullExteriorComparisons
    exact r5ComparisonsSorted_relabel_sort firstGraph
  · change ∀ left right : Fin 5,
      decide (finalGraph.Adj
        ⟨(left : ℕ) + 1, by omega⟩
        ⟨(right : ℕ) + 1, by omega⟩) =
      r5FiveVertexAdjacency
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode branch))
        left right
    exact hfinalOrbit

end Erdos617
