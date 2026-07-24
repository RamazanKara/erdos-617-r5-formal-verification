/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.Sat.SpecialBrooksZeroAnchor

/-!
# Within-class sorting for the E045 zero-anchor quotient

After vertex 6 has neighbors `7, ..., 11`, the remaining symmetry is the
product of the permutations of `7, ..., 11` and `12, ..., 25`.  This file
sorts the five-bit neighborhood rows independently in those two classes and
proves exactly the 17 comparisons used by E045.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

def r5AnchorNeighborFinEquiv :
    Fin 5 ≃ {vertex : Fin 26 // 7 ≤ vertex ∧ vertex < 12} where
  toFun index :=
    ⟨⟨(index : ℕ) + 7, by omega⟩, by
      constructor
      · change 7 ≤ (index : ℕ) + 7
        omega
      · change (index : ℕ) + 7 < 12
        omega⟩
  invFun vertex :=
    ⟨vertex.1 - 7, by omega⟩
  left_inv index := by
    ext
    change ((index : ℕ) + 7) - 7 = index
    omega
  right_inv vertex := by
    ext
    change ((vertex.1 : ℕ) - 7) + 7 = vertex.1
    have hvertex := vertex.property
    omega

def r5AnchorNonneighborFinEquiv :
    Fin 14 ≃ {vertex : Fin 26 // 12 ≤ vertex} where
  toFun index :=
    ⟨⟨(index : ℕ) + 12, by omega⟩, by
      change 12 ≤ (index : ℕ) + 12
      omega⟩
  invFun vertex :=
    ⟨vertex.1 - 12, by omega⟩
  left_inv index := by
    ext
    change ((index : ℕ) + 12) - 12 = index
    omega
  right_inv vertex := by
    ext
    change ((vertex.1 : ℕ) - 12) + 12 = vertex.1
    have hvertex := vertex.property
    omega

noncomputable def r5SortAnchorNeighborPerm
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] :
    Equiv.Perm (Fin 26) :=
  let pattern : Fin 5 → ℕ :=
    fun index => r5ExteriorPatternCode G ((index : ℕ) + 7)
  let classPermutation :
      Equiv.Perm {vertex : Fin 26 // 7 ≤ vertex ∧ vertex < 12} :=
    r5AnchorNeighborFinEquiv.symm.trans
      ((Tuple.sort pattern).trans r5AnchorNeighborFinEquiv)
  classPermutation.subtypeCongr (Equiv.refl _)

@[simp]
theorem r5SortAnchorNeighborPerm_apply_of_outside
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (vertex : Fin 26) (hvertex : ¬(7 ≤ vertex ∧ vertex < 12)) :
    r5SortAnchorNeighborPerm G vertex = vertex := by
  classical
  simp [r5SortAnchorNeighborPerm, hvertex]

theorem r5SortAnchorNeighborPerm_apply_class
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (index : Fin 5) :
    r5SortAnchorNeighborPerm G
        ⟨(index : ℕ) + 7, by omega⟩ =
      ⟨Tuple.sort
        (fun offset : Fin 5 =>
          r5ExteriorPatternCode G ((offset : ℕ) + 7)) index + 7,
        by omega⟩ := by
  change r5SortAnchorNeighborPerm G (r5AnchorNeighborFinEquiv index) =
    r5AnchorNeighborFinEquiv
      (Tuple.sort
        (fun offset : Fin 5 =>
          r5ExteriorPatternCode G ((offset : ℕ) + 7)) index)
  have hclass := (r5AnchorNeighborFinEquiv index).property
  simp [r5SortAnchorNeighborPerm, hclass]

theorem r5AnchorNeighborPatternCode_relabel_sort
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (index : Fin 5) :
    r5ExteriorPatternCode
        (relabelGraph G (r5SortAnchorNeighborPerm G))
        ((index : ℕ) + 7) =
      r5ExteriorPatternCode G
        (Tuple.sort
          (fun offset : Fin 5 =>
            r5ExteriorPatternCode G ((offset : ℕ) + 7)) index + 7) := by
  let sortedIndex :=
    Tuple.sort
      (fun offset : Fin 5 =>
        r5ExteriorPatternCode G ((offset : ℕ) + 7)) index
  have hbit (position : ℕ) (hposition : position < 5) :
      r5ExteriorPatternBit
          (relabelGraph G (r5SortAnchorNeighborPerm G))
          ((index : ℕ) + 7) position ↔
        r5ExteriorPatternBit G (sortedIndex + 7) position := by
    simp only [r5ExteriorPatternBit]
    rw [dif_pos (by omega), dif_pos hposition,
      dif_pos (by omega), dif_pos hposition]
    simp only [relabelGraph_adj_iff]
    rw [r5SortAnchorNeighborPerm_apply_of_outside G
        (hvertex := by
          have hlabelLT :
              (⟨position + 1, by omega⟩ : Fin 26) < 7 := by
            change position + 1 < 7
            omega
          exact fun hclass => (not_le_of_gt hlabelLT) hclass.1),
      r5SortAnchorNeighborPerm_apply_class G index]
  change r5ExteriorPatternCode
      (relabelGraph G (r5SortAnchorNeighborPerm G))
      ((index : ℕ) + 7) =
    r5ExteriorPatternCode G ((sortedIndex : ℕ) + 7)
  unfold r5ExteriorPatternCode
  simp only [hbit 0 (by omega), hbit 1 (by omega),
    hbit 2 (by omega), hbit 3 (by omega), hbit 4 (by omega)]

noncomputable def r5SortAnchorNonneighborPerm
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] :
    Equiv.Perm (Fin 26) :=
  let pattern : Fin 14 → ℕ :=
    fun index => r5ExteriorPatternCode G ((index : ℕ) + 12)
  let classPermutation :
      Equiv.Perm {vertex : Fin 26 // 12 ≤ vertex} :=
    r5AnchorNonneighborFinEquiv.symm.trans
      ((Tuple.sort pattern).trans r5AnchorNonneighborFinEquiv)
  classPermutation.subtypeCongr (Equiv.refl _)

@[simp]
theorem r5SortAnchorNonneighborPerm_apply_of_lt_twelve
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (vertex : Fin 26) (hvertex : vertex < 12) :
    r5SortAnchorNonneighborPerm G vertex = vertex := by
  rw [r5SortAnchorNonneighborPerm,
    Equiv.Perm.subtypeCongr.right_apply (h := by omega)]
  rfl

theorem r5SortAnchorNonneighborPerm_apply_class
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (index : Fin 14) :
    r5SortAnchorNonneighborPerm G
        ⟨(index : ℕ) + 12, by omega⟩ =
      ⟨Tuple.sort
        (fun offset : Fin 14 =>
          r5ExteriorPatternCode G ((offset : ℕ) + 12)) index + 12,
        by omega⟩ := by
  change r5SortAnchorNonneighborPerm G
      (r5AnchorNonneighborFinEquiv index) =
    r5AnchorNonneighborFinEquiv
      (Tuple.sort
        (fun offset : Fin 14 =>
          r5ExteriorPatternCode G ((offset : ℕ) + 12)) index)
  have hclass := (r5AnchorNonneighborFinEquiv index).property
  simp [r5SortAnchorNonneighborPerm, hclass]

theorem r5AnchorNonneighborPatternCode_relabel_sort
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (index : Fin 14) :
    r5ExteriorPatternCode
        (relabelGraph G (r5SortAnchorNonneighborPerm G))
        ((index : ℕ) + 12) =
      r5ExteriorPatternCode G
        (Tuple.sort
          (fun offset : Fin 14 =>
            r5ExteriorPatternCode G ((offset : ℕ) + 12)) index + 12) := by
  let sortedIndex :=
    Tuple.sort
      (fun offset : Fin 14 =>
        r5ExteriorPatternCode G ((offset : ℕ) + 12)) index
  have hbit (position : ℕ) (hposition : position < 5) :
      r5ExteriorPatternBit
          (relabelGraph G (r5SortAnchorNonneighborPerm G))
          ((index : ℕ) + 12) position ↔
        r5ExteriorPatternBit G (sortedIndex + 12) position := by
    simp only [r5ExteriorPatternBit]
    rw [dif_pos (by omega), dif_pos hposition,
      dif_pos (by omega), dif_pos hposition]
    simp only [relabelGraph_adj_iff]
    rw [r5SortAnchorNonneighborPerm_apply_of_lt_twelve G
        (hvertex := by
          change position + 1 < 12
          omega),
      r5SortAnchorNonneighborPerm_apply_class G index]
  change r5ExteriorPatternCode
      (relabelGraph G (r5SortAnchorNonneighborPerm G))
      ((index : ℕ) + 12) =
    r5ExteriorPatternCode G ((sortedIndex : ℕ) + 12)
  unfold r5ExteriorPatternCode
  simp only [hbit 0 (by omega), hbit 1 (by omega),
    hbit 2 (by omega), hbit 3 (by omega), hbit 4 (by omega)]

theorem r5ExteriorPatternCode_relabel_of_fixed
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (relabeling : Equiv.Perm (Fin 26))
    (hfixed : ∀ vertex : Fin 26, vertex < 6 →
      relabeling vertex = vertex)
    (vertex : Fin 26) (hvertex : relabeling vertex = vertex) :
    r5ExteriorPatternCode (relabelGraph G relabeling) vertex =
      r5ExteriorPatternCode G vertex := by
  have hbit (position : ℕ) (hposition : position < 5) :
      r5ExteriorPatternBit (relabelGraph G relabeling)
          vertex position ↔
        r5ExteriorPatternBit G vertex position := by
    simp only [r5ExteriorPatternBit]
    rw [dif_pos vertex.isLt, dif_pos hposition,
      dif_pos vertex.isLt, dif_pos hposition]
    simp only [relabelGraph_adj_iff]
    rw [hfixed _ (by
      change position + 1 < 6
      omega), hvertex]
  unfold r5ExteriorPatternCode
  simp only [hbit 0 (by omega), hbit 1 (by omega),
    hbit 2 (by omega), hbit 3 (by omega), hbit 4 (by omega)]

theorem mem_r5FixedAnchorNeighbors_iff (vertex : Fin 26) :
    vertex ∈ r5FixedAnchorNeighbors ↔ 7 ≤ vertex ∧ vertex < 12 := by
  fin_cases vertex <;> decide

/-- Sort both E045 exterior classes and prove the exact 17 comparisons. -/
theorem exists_r5ZeroAnchorSortedRelabel
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hzeroNeighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (hanchorNeighbor :
      G.neighborFinset 6 = r5FixedAnchorNeighbors) :
    ∃ relabeling : Equiv.Perm (Fin 26),
      let H := relabelGraph G relabeling
      (∀ vertex : Fin 26, vertex < 7 →
        relabeling vertex = vertex) ∧
      H.neighborFinset 0 = r5FixedNeighbors ∧
      H.neighborFinset 6 = r5FixedAnchorNeighbors ∧
      R5ComparisonsSorted H r5ZeroAnchorComparisons := by
  let firstRelabeling := r5SortAnchorNeighborPerm G
  let firstGraph := relabelGraph G firstRelabeling
  let secondRelabeling := r5SortAnchorNonneighborPerm firstGraph
  let finalGraph := relabelGraph firstGraph secondRelabeling
  let finalRelabeling := secondRelabeling.trans firstRelabeling
  have hfirstFixed (vertex : Fin 26) (hvertex : vertex < 7) :
      firstRelabeling vertex = vertex := by
    exact r5SortAnchorNeighborPerm_apply_of_outside G vertex (by omega)
  have hsecondFixed (vertex : Fin 26) (hvertex : vertex < 12) :
      secondRelabeling vertex = vertex :=
    r5SortAnchorNonneighborPerm_apply_of_lt_twelve
      firstGraph vertex hvertex
  have hfinalZeroNeighbor :
      finalGraph.neighborFinset 0 = r5FixedNeighbors := by
    have hsubset :
        r5FixedNeighbors ⊆ finalGraph.neighborFinset 0 := by
      intro vertex hvertex
      have hvertexLT : vertex < 6 := by
        simp only [r5FixedNeighbors, mem_insert, mem_singleton] at hvertex
        rcases hvertex with h | h | h | h | h
        all_goals omega
      rw [SimpleGraph.mem_neighborFinset]
      change G.Adj
        (firstRelabeling (secondRelabeling 0))
        (firstRelabeling (secondRelabeling vertex))
      rw [hsecondFixed 0 (by omega),
        hsecondFixed vertex (by omega),
        hfirstFixed 0 (by omega),
        hfirstFixed vertex (by omega),
        ← SimpleGraph.mem_neighborFinset, hzeroNeighbor]
      exact hvertex
    have hdegree : finalGraph.degree 0 = 5 := by
      change (relabelGraph firstGraph secondRelabeling).degree 0 = 5
      rw [relabelGraph_degree]
      change (relabelGraph G firstRelabeling).degree
        (secondRelabeling 0) = 5
      rw [relabelGraph_degree]
      exact hregular _
    have hcard :
        #(finalGraph.neighborFinset 0) ≤ #r5FixedNeighbors := by
      simp [hdegree]
    exact (Finset.eq_of_subset_of_card_le hsubset hcard).symm
  have hfinalAnchorNeighbor :
      finalGraph.neighborFinset 6 = r5FixedAnchorNeighbors := by
    have hsubset :
        r5FixedAnchorNeighbors ⊆ finalGraph.neighborFinset 6 := by
      intro vertex hvertex
      have hvertexBounds : 7 ≤ vertex ∧ vertex < 12 := by
        simp only [r5FixedAnchorNeighbors, mem_insert, mem_singleton]
          at hvertex
        rcases hvertex with h | h | h | h | h
        all_goals omega
      have hfirstImage :
          firstRelabeling vertex ∈ r5FixedAnchorNeighbors := by
        let index := r5AnchorNeighborFinEquiv.symm
          ⟨vertex, hvertexBounds⟩
        have hvertexEq :
            vertex = ⟨(index : ℕ) + 7, by omega⟩ := by
          exact (congrArg Subtype.val
            (r5AnchorNeighborFinEquiv.apply_symm_apply
              ⟨vertex, hvertexBounds⟩)).symm
        rw [hvertexEq, r5SortAnchorNeighborPerm_apply_class]
        have houtput :=
          (r5AnchorNeighborFinEquiv
            (Tuple.sort
              (fun offset : Fin 5 =>
                r5ExteriorPatternCode G ((offset : ℕ) + 7))
              index)).property
        exact (mem_r5FixedAnchorNeighbors_iff _).2 houtput
      rw [SimpleGraph.mem_neighborFinset]
      change G.Adj
        (firstRelabeling (secondRelabeling 6))
        (firstRelabeling (secondRelabeling vertex))
      rw [hsecondFixed 6 (by omega),
        hsecondFixed vertex hvertexBounds.2,
        hfirstFixed 6 (by omega),
        ← SimpleGraph.mem_neighborFinset, hanchorNeighbor]
      exact hfirstImage
    have hdegree : finalGraph.degree 6 = 5 := by
      change (relabelGraph firstGraph secondRelabeling).degree 6 = 5
      rw [relabelGraph_degree]
      change (relabelGraph G firstRelabeling).degree
        (secondRelabeling 6) = 5
      rw [relabelGraph_degree]
      exact hregular _
    have hcard :
        #(finalGraph.neighborFinset 6) ≤
          #r5FixedAnchorNeighbors := by
      simp [hdegree]
    exact (Finset.eq_of_subset_of_card_le hsubset hcard).symm
  have hfinalSorted :
      R5ComparisonsSorted finalGraph r5ZeroAnchorComparisons := by
    intro comparison hcomparison
    rw [r5ZeroAnchorComparisons, List.mem_append] at hcomparison
    rcases hcomparison with hfirst | hsecond
    · rw [List.mem_map] at hfirst
      obtain ⟨offset, hoffset, rfl⟩ := hfirst
      have hoffsetLT : offset < 4 := List.mem_range.mp hoffset
      apply propLexicographicLE_of_r5ExteriorPatternCode_le
      change r5ExteriorPatternCode finalGraph (offset + 7) ≤
        r5ExteriorPatternCode finalGraph (offset + 8)
      rw [show r5ExteriorPatternCode finalGraph (offset + 7) =
            r5ExteriorPatternCode firstGraph (offset + 7) by
          simpa [finalGraph] using
            (r5ExteriorPatternCode_relabel_of_fixed
              firstGraph secondRelabeling
              (fun vertex hvertex =>
                hsecondFixed vertex (by omega))
              ⟨offset + 7, by omega⟩
              (hsecondFixed _ (by
                change offset + 7 < 12
                omega))),
        show r5ExteriorPatternCode finalGraph (offset + 8) =
            r5ExteriorPatternCode firstGraph (offset + 8) by
          simpa [finalGraph] using
            (r5ExteriorPatternCode_relabel_of_fixed
              firstGraph secondRelabeling
              (fun vertex hvertex =>
                hsecondFixed vertex (by omega))
              ⟨offset + 8, by omega⟩
              (hsecondFixed _ (by
                change offset + 8 < 12
                omega))),
        r5AnchorNeighborPatternCode_relabel_sort
          (G := G) (index := ⟨offset, by omega⟩),
        r5AnchorNeighborPatternCode_relabel_sort
          (G := G) (index := ⟨offset + 1, by omega⟩)]
      exact Tuple.monotone_sort
        (fun index : Fin 5 =>
          r5ExteriorPatternCode G ((index : ℕ) + 7))
        (show (⟨offset, by omega⟩ : Fin 5) ≤
          ⟨offset + 1, by omega⟩ by
            simp only [Fin.mk_le_mk]
            omega)
    · rw [List.mem_map] at hsecond
      obtain ⟨offset, hoffset, rfl⟩ := hsecond
      have hoffsetLT : offset < 13 := List.mem_range.mp hoffset
      apply propLexicographicLE_of_r5ExteriorPatternCode_le
      change r5ExteriorPatternCode finalGraph (offset + 12) ≤
        r5ExteriorPatternCode finalGraph (offset + 13)
      rw [r5AnchorNonneighborPatternCode_relabel_sort
          (G := firstGraph) (index := ⟨offset, by omega⟩),
        r5AnchorNonneighborPatternCode_relabel_sort
          (G := firstGraph) (index := ⟨offset + 1, by omega⟩)]
      exact Tuple.monotone_sort
        (fun index : Fin 14 =>
          r5ExteriorPatternCode firstGraph ((index : ℕ) + 12))
        (show (⟨offset, by omega⟩ : Fin 14) ≤
          ⟨offset + 1, by omega⟩ by
            simp only [Fin.mk_le_mk]
            omega)
  refine ⟨finalRelabeling, ?_, ?_, ?_, ?_⟩
  · intro vertex hvertex
    change firstRelabeling (secondRelabeling vertex) = vertex
    rw [hsecondFixed vertex (by omega),
      hfirstFixed vertex hvertex]
  · change finalGraph.neighborFinset 0 = r5FixedNeighbors
    exact hfinalZeroNeighbor
  · change finalGraph.neighborFinset 6 = r5FixedAnchorNeighbors
    exact hfinalAnchorNeighbor
  · change R5ComparisonsSorted finalGraph r5ZeroAnchorComparisons
    exact hfinalSorted

end Erdos617
