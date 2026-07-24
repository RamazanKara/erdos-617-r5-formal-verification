/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.Sat.ClauseSemantics
public import Mathlib.Data.Fin.Tuple.Sort

/-!
# Symmetry coverage for the finite special-Brooks certificates

This file supplies kernel-checked normalization steps connecting an arbitrary
five-regular graph to the exact E038--E045 branch quotients.  The first step
sorts the twenty exterior adjacency rows while fixing labels `0, ..., 5`.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

def r5ExteriorPatternCode
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (exterior : ℕ) : ℕ :=
  (if r5ExteriorPatternBit G exterior 0 then 16 else 0) +
  (if r5ExteriorPatternBit G exterior 1 then 8 else 0) +
  (if r5ExteriorPatternBit G exterior 2 then 4 else 0) +
  (if r5ExteriorPatternBit G exterior 3 then 2 else 0) +
  (if r5ExteriorPatternBit G exterior 4 then 1 else 0)

theorem r5BitTerm_le (p : Prop) [Decidable p] (weight : ℕ) :
    (if p then weight else 0) ≤ weight := by
  by_cases hp : p <;> simp [hp]

theorem propLexicographicLE_of_r5ExteriorPatternCode_le
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (left right : ℕ)
    (hcode : r5ExteriorPatternCode G left ≤
      r5ExteriorPatternCode G right) :
    propLexicographicLE
      (r5ExteriorPatternBit G left)
      (r5ExteriorPatternBit G right) 5 := by
  intro position hposition hprefix hleft
  interval_cases position
  · by_contra hright
    have hright1 := r5BitTerm_le
      (r5ExteriorPatternBit G right 1) 8
    have hright2 := r5BitTerm_le
      (r5ExteriorPatternBit G right 2) 4
    have hright3 := r5BitTerm_le
      (r5ExteriorPatternBit G right 3) 2
    have hright4 := r5BitTerm_le
      (r5ExteriorPatternBit G right 4) 1
    simp only [r5ExteriorPatternCode, if_pos hleft,
      if_neg hright] at hcode
    omega
  · have hprefix0 := hprefix 0 (by omega)
    have hterm0 :
        (if r5ExteriorPatternBit G left 0 then 16 else 0) =
        (if r5ExteriorPatternBit G right 0 then 16 else 0) := by
      by_cases hleft0 : r5ExteriorPatternBit G left 0
      · have hright0 := hprefix0.mp hleft0
        simp [hleft0, hright0]
      · have hright0 : ¬r5ExteriorPatternBit G right 0 :=
          fun h => hleft0 (hprefix0.mpr h)
        simp [hleft0, hright0]
    by_contra hright
    have hright2 := r5BitTerm_le
      (r5ExteriorPatternBit G right 2) 4
    have hright3 := r5BitTerm_le
      (r5ExteriorPatternBit G right 3) 2
    have hright4 := r5BitTerm_le
      (r5ExteriorPatternBit G right 4) 1
    simp only [r5ExteriorPatternCode, if_pos hleft,
      if_neg hright] at hcode
    omega
  · have hprefix0 := hprefix 0 (by omega)
    have hprefix1 := hprefix 1 (by omega)
    have hterm0 :
        (if r5ExteriorPatternBit G left 0 then 16 else 0) =
        (if r5ExteriorPatternBit G right 0 then 16 else 0) := by
      by_cases hleft0 : r5ExteriorPatternBit G left 0
      · have hright0 := hprefix0.mp hleft0
        simp [hleft0, hright0]
      · have hright0 : ¬r5ExteriorPatternBit G right 0 :=
          fun h => hleft0 (hprefix0.mpr h)
        simp [hleft0, hright0]
    have hterm1 :
        (if r5ExteriorPatternBit G left 1 then 8 else 0) =
        (if r5ExteriorPatternBit G right 1 then 8 else 0) := by
      by_cases hleft1 : r5ExteriorPatternBit G left 1
      · have hright1 := hprefix1.mp hleft1
        simp [hleft1, hright1]
      · have hright1 : ¬r5ExteriorPatternBit G right 1 :=
          fun h => hleft1 (hprefix1.mpr h)
        simp [hleft1, hright1]
    by_contra hright
    have hright3 := r5BitTerm_le
      (r5ExteriorPatternBit G right 3) 2
    have hright4 := r5BitTerm_le
      (r5ExteriorPatternBit G right 4) 1
    simp only [r5ExteriorPatternCode, if_pos hleft,
      if_neg hright] at hcode
    omega
  · have hprefix0 := hprefix 0 (by omega)
    have hprefix1 := hprefix 1 (by omega)
    have hprefix2 := hprefix 2 (by omega)
    have hterm0 :
        (if r5ExteriorPatternBit G left 0 then 16 else 0) =
        (if r5ExteriorPatternBit G right 0 then 16 else 0) := by
      by_cases hleft0 : r5ExteriorPatternBit G left 0
      · have hright0 := hprefix0.mp hleft0
        simp [hleft0, hright0]
      · have hright0 : ¬r5ExteriorPatternBit G right 0 :=
          fun h => hleft0 (hprefix0.mpr h)
        simp [hleft0, hright0]
    have hterm1 :
        (if r5ExteriorPatternBit G left 1 then 8 else 0) =
        (if r5ExteriorPatternBit G right 1 then 8 else 0) := by
      by_cases hleft1 : r5ExteriorPatternBit G left 1
      · have hright1 := hprefix1.mp hleft1
        simp [hleft1, hright1]
      · have hright1 : ¬r5ExteriorPatternBit G right 1 :=
          fun h => hleft1 (hprefix1.mpr h)
        simp [hleft1, hright1]
    have hterm2 :
        (if r5ExteriorPatternBit G left 2 then 4 else 0) =
        (if r5ExteriorPatternBit G right 2 then 4 else 0) := by
      by_cases hleft2 : r5ExteriorPatternBit G left 2
      · have hright2 := hprefix2.mp hleft2
        simp [hleft2, hright2]
      · have hright2 : ¬r5ExteriorPatternBit G right 2 :=
          fun h => hleft2 (hprefix2.mpr h)
        simp [hleft2, hright2]
    by_contra hright
    have hright4 := r5BitTerm_le
      (r5ExteriorPatternBit G right 4) 1
    simp only [r5ExteriorPatternCode, if_pos hleft,
      if_neg hright] at hcode
    omega
  · have hprefix0 := hprefix 0 (by omega)
    have hprefix1 := hprefix 1 (by omega)
    have hprefix2 := hprefix 2 (by omega)
    have hprefix3 := hprefix 3 (by omega)
    have hterm0 :
        (if r5ExteriorPatternBit G left 0 then 16 else 0) =
        (if r5ExteriorPatternBit G right 0 then 16 else 0) := by
      by_cases hleft0 : r5ExteriorPatternBit G left 0
      · have hright0 := hprefix0.mp hleft0
        simp [hleft0, hright0]
      · have hright0 : ¬r5ExteriorPatternBit G right 0 :=
          fun h => hleft0 (hprefix0.mpr h)
        simp [hleft0, hright0]
    have hterm1 :
        (if r5ExteriorPatternBit G left 1 then 8 else 0) =
        (if r5ExteriorPatternBit G right 1 then 8 else 0) := by
      by_cases hleft1 : r5ExteriorPatternBit G left 1
      · have hright1 := hprefix1.mp hleft1
        simp [hleft1, hright1]
      · have hright1 : ¬r5ExteriorPatternBit G right 1 :=
          fun h => hleft1 (hprefix1.mpr h)
        simp [hleft1, hright1]
    have hterm2 :
        (if r5ExteriorPatternBit G left 2 then 4 else 0) =
        (if r5ExteriorPatternBit G right 2 then 4 else 0) := by
      by_cases hleft2 : r5ExteriorPatternBit G left 2
      · have hright2 := hprefix2.mp hleft2
        simp [hleft2, hright2]
      · have hright2 : ¬r5ExteriorPatternBit G right 2 :=
          fun h => hleft2 (hprefix2.mpr h)
        simp [hleft2, hright2]
    have hterm3 :
        (if r5ExteriorPatternBit G left 3 then 2 else 0) =
        (if r5ExteriorPatternBit G right 3 then 2 else 0) := by
      by_cases hleft3 : r5ExteriorPatternBit G left 3
      · have hright3 := hprefix3.mp hleft3
        simp [hleft3, hright3]
      · have hright3 : ¬r5ExteriorPatternBit G right 3 :=
          fun h => hleft3 (hprefix3.mpr h)
        simp [hleft3, hright3]
    by_contra hright
    simp only [r5ExteriorPatternCode, if_pos hleft,
      if_neg hright] at hcode
    omega

def r5ExteriorFinEquiv :
    Fin 20 ≃ {vertex : Fin 26 // 6 ≤ vertex} where
  toFun index :=
    ⟨⟨(index : ℕ) + 6, by omega⟩, by
      change 6 ≤ (index : ℕ) + 6
      omega⟩
  invFun vertex :=
    ⟨vertex.1 - 6, by omega⟩
  left_inv index := by
    ext
    change ((index : ℕ) + 6) - 6 = index
    omega
  right_inv vertex := by
    ext
    change ((vertex.1 : ℕ) - 6) + 6 = vertex.1
    omega

noncomputable def r5SortExteriorPerm
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] :
    Equiv.Perm (Fin 26) :=
  let pattern : Fin 20 → ℕ :=
    fun index => r5ExteriorPatternCode G ((index : ℕ) + 6)
  let exteriorPerm : Equiv.Perm {vertex : Fin 26 // 6 ≤ vertex} :=
    r5ExteriorFinEquiv.symm.trans
      ((Tuple.sort pattern).trans r5ExteriorFinEquiv)
  exteriorPerm.subtypeCongr (Equiv.refl _)

@[simp]
theorem r5SortExteriorPerm_apply_of_lt_six
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (vertex : Fin 26) (hvertex : vertex < 6) :
    r5SortExteriorPerm G vertex = vertex := by
  simp [r5SortExteriorPerm, not_le.mpr hvertex]

theorem r5SortExteriorPerm_apply_exterior
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (index : Fin 20) :
    r5SortExteriorPerm G ⟨(index : ℕ) + 6, by omega⟩ =
      ⟨Tuple.sort
        (fun offset : Fin 20 =>
          r5ExteriorPatternCode G ((offset : ℕ) + 6)) index + 6, by omega⟩ := by
  change r5SortExteriorPerm G (r5ExteriorFinEquiv index) =
    r5ExteriorFinEquiv
      (Tuple.sort
        (fun offset : Fin 20 =>
          r5ExteriorPatternCode G ((offset : ℕ) + 6)) index)
  have hexterior :
      6 ≤ (r5ExteriorFinEquiv index : Fin 26) :=
    (r5ExteriorFinEquiv index).property
  simp [r5SortExteriorPerm, hexterior]

theorem r5ExteriorPatternCode_relabel_sort
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (index : Fin 20) :
    r5ExteriorPatternCode (relabelGraph G (r5SortExteriorPerm G))
        ((index : ℕ) + 6) =
      r5ExteriorPatternCode G
        (Tuple.sort
          (fun offset : Fin 20 =>
            r5ExteriorPatternCode G ((offset : ℕ) + 6)) index + 6) := by
  let sortedIndex :=
    Tuple.sort
      (fun offset : Fin 20 =>
        r5ExteriorPatternCode G ((offset : ℕ) + 6)) index
  have hbit (position : ℕ) (hposition : position < 5) :
      r5ExteriorPatternBit
          (relabelGraph G (r5SortExteriorPerm G))
          ((index : ℕ) + 6) position ↔
        r5ExteriorPatternBit G (sortedIndex + 6) position := by
    simp only [r5ExteriorPatternBit]
    rw [dif_pos (by omega), dif_pos hposition,
      dif_pos (by omega), dif_pos hposition]
    simp only [relabelGraph_adj_iff]
    rw [r5SortExteriorPerm_apply_of_lt_six G
        (hvertex := by
          change position + 1 < 6
          omega),
      r5SortExteriorPerm_apply_exterior G index]
  change r5ExteriorPatternCode
      (relabelGraph G (r5SortExteriorPerm G))
      ((index : ℕ) + 6) =
    r5ExteriorPatternCode G ((sortedIndex : ℕ) + 6)
  unfold r5ExteriorPatternCode
  simp only [hbit 0 (by omega), hbit 1 (by omega),
    hbit 2 (by omega), hbit 3 (by omega), hbit 4 (by omega)]

theorem r5ComparisonsSorted_relabel_sort
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] :
    R5ComparisonsSorted
      (relabelGraph G (r5SortExteriorPerm G))
      r5FullExteriorComparisons := by
  intro comparison hcomparison
  rw [r5FullExteriorComparisons, List.mem_map] at hcomparison
  obtain ⟨offset, hoffset, rfl⟩ := hcomparison
  have hoffsetLT : offset < 19 := List.mem_range.mp hoffset
  apply propLexicographicLE_of_r5ExteriorPatternCode_le
  change
    r5ExteriorPatternCode (relabelGraph G (r5SortExteriorPerm G))
        (offset + 6) ≤
      r5ExteriorPatternCode (relabelGraph G (r5SortExteriorPerm G))
        (offset + 7)
  rw [r5ExteriorPatternCode_relabel_sort (G := G)
      (index := ⟨offset, by omega⟩),
    r5ExteriorPatternCode_relabel_sort (G := G)
      (index := ⟨offset + 1, by omega⟩)]
  exact Tuple.monotone_sort
    (fun index : Fin 20 =>
      r5ExteriorPatternCode G ((index : ℕ) + 6))
    (show (⟨offset, by omega⟩ : Fin 20) ≤
      ⟨offset + 1, by omega⟩ by
        simp only [Fin.mk_le_mk]
        omega)

end Erdos617
