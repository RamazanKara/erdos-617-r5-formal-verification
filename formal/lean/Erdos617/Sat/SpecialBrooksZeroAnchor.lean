/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.Sat.SpecialBrooksBranchUnits

/-!
# Zero-anchor symmetry for E058 branches 20--25

The final six neighborhood representatives all contain the internal edge
`1--5`.  Regularity then leaves at most eighteen exterior vertices covered by
the exterior neighborhoods of labels `1, ..., 5`.  This forces a zero-pattern
exterior vertex, which is the anchor used by the E045 quotient.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

/-- The twenty labels outside vertex zero and its normalized neighborhood. -/
def r5ExteriorVertices : Finset (Fin 26) :=
  Finset.univ.filter fun vertex => 6 ≤ vertex

@[simp]
theorem card_r5ExteriorVertices : #r5ExteriorVertices = 20 := by
  decide

theorem mem_r5ExteriorVertices_iff (vertex : Fin 26) :
    vertex ∈ r5ExteriorVertices ↔ 6 ≤ vertex := by
  simp [r5ExteriorVertices]

/-- Exterior neighbors of one vertex. -/
def r5ExteriorNeighbors
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (vertex : Fin 26) : Finset (Fin 26) :=
  G.neighborFinset vertex ∩ r5ExteriorVertices

/-- Exterior vertices incident with at least one fixed-neighborhood vertex. -/
def r5CrossCoveredVertices
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] :
    Finset (Fin 26) :=
  Finset.univ.biUnion fun index : Fin 5 =>
    r5ExteriorNeighbors G (r5NeighborVertex index)

theorem r5NeighborVertex_mem_fixed (index : Fin 5) :
    r5NeighborVertex index ∈ r5FixedNeighbors := by
  fin_cases index <;> decide

theorem zero_mem_neighborFinset_r5NeighborVertex
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (index : Fin 5) :
    0 ∈ G.neighborFinset (r5NeighborVertex index) := by
  rw [SimpleGraph.mem_neighborFinset, G.adj_comm,
    ← SimpleGraph.mem_neighborFinset, hneighbor]
  exact r5NeighborVertex_mem_fixed index

theorem card_r5ExteriorNeighbors_le_four
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (index : Fin 5) :
    #(r5ExteriorNeighbors G (r5NeighborVertex index)) ≤ 4 := by
  have hzero :=
    zero_mem_neighborFinset_r5NeighborVertex G hneighbor index
  have hsubset :
      r5ExteriorNeighbors G (r5NeighborVertex index) ⊆
        (G.neighborFinset (r5NeighborVertex index)).erase 0 := by
    intro vertex hvertex
    rw [r5ExteriorNeighbors, mem_inter] at hvertex
    rw [mem_erase]
    refine ⟨?_, hvertex.1⟩
    have hexterior :=
      (mem_r5ExteriorVertices_iff vertex).mp hvertex.2
    omega
  apply (card_le_card hsubset).trans_eq
  rw [card_erase_of_mem hzero, G.card_neighborFinset_eq_degree,
    hregular]

theorem card_r5ExteriorNeighbors_le_three_of_adj
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (left right : Fin 5)
    (hadj : G.Adj (r5NeighborVertex left) (r5NeighborVertex right)) :
    #(r5ExteriorNeighbors G (r5NeighborVertex left)) ≤ 3 := by
  have hzero :=
    zero_mem_neighborFinset_r5NeighborVertex G hneighbor left
  have hright :
      r5NeighborVertex right ∈
        G.neighborFinset (r5NeighborVertex left) := by
    rwa [SimpleGraph.mem_neighborFinset]
  have hrightNeZero : r5NeighborVertex right ≠ 0 := by
    simp [r5NeighborVertex]
  have hrightErase :
      r5NeighborVertex right ∈
        (G.neighborFinset (r5NeighborVertex left)).erase 0 :=
    mem_erase.mpr ⟨hrightNeZero, hright⟩
  have hsubset :
      r5ExteriorNeighbors G (r5NeighborVertex left) ⊆
        ((G.neighborFinset (r5NeighborVertex left)).erase 0).erase
          (r5NeighborVertex right) := by
    intro vertex hvertex
    rw [r5ExteriorNeighbors, mem_inter] at hvertex
    rw [mem_erase, mem_erase]
    have hexterior :=
      (mem_r5ExteriorVertices_iff vertex).mp hvertex.2
    have hvertexNeZero : vertex ≠ 0 := by omega
    have hvertexNeRight : vertex ≠ r5NeighborVertex right := by
      intro heq
      subst vertex
      change 6 ≤ (right : ℕ) + 1 at hexterior
      omega
    exact ⟨hvertexNeRight, hvertexNeZero, hvertex.1⟩
  apply (card_le_card hsubset).trans_eq
  rw [card_erase_of_mem hrightErase, card_erase_of_mem hzero,
    G.card_neighborFinset_eq_degree, hregular]

theorem card_r5CrossCoveredVertices_le_eighteen_of_adj_one_five
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (hadj : G.Adj 1 5) :
    #(r5CrossCoveredVertices G) ≤ 18 := by
  have h0 :
      #(r5ExteriorNeighbors G (r5NeighborVertex 0)) ≤ 3 := by
    apply card_r5ExteriorNeighbors_le_three_of_adj
      G hregular hneighbor 0 4
    simpa [r5NeighborVertex] using hadj
  have h4 :
      #(r5ExteriorNeighbors G (r5NeighborVertex 4)) ≤ 3 := by
    apply card_r5ExteriorNeighbors_le_three_of_adj
      G hregular hneighbor 4 0
    simpa [r5NeighborVertex, G.adj_comm] using hadj
  have h1 := card_r5ExteriorNeighbors_le_four
    G hregular hneighbor 1
  have h2 := card_r5ExteriorNeighbors_le_four
    G hregular hneighbor 2
  have h3 := card_r5ExteriorNeighbors_le_four
    G hregular hneighbor 3
  have hsum :
      (∑ index : Fin 5,
        #(r5ExteriorNeighbors G (r5NeighborVertex index))) ≤ 18 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp
    omega
  calc
    #(r5CrossCoveredVertices G) ≤
        ∑ index ∈ Finset.univ,
          #(r5ExteriorNeighbors G (r5NeighborVertex index)) :=
      Finset.card_biUnion_le
    _ = ∑ index : Fin 5,
          #(r5ExteriorNeighbors G (r5NeighborVertex index)) := by
      simp
    _ ≤ 18 := hsum

theorem exists_r5ZeroPatternExterior_of_adj_one_five
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (hadj : G.Adj 1 5) :
    ∃ anchor : Fin 26,
      anchor ∈ r5ExteriorVertices ∧
      ∀ index : Fin 5,
        ¬G.Adj (r5NeighborVertex index) anchor := by
  classical
  by_contra hexists
  have hcover :
      r5ExteriorVertices ⊆ r5CrossCoveredVertices G := by
    intro vertex hvertex
    by_contra hnotCovered
    have hzero (index : Fin 5) :
        ¬G.Adj (r5NeighborVertex index) vertex := by
      intro hadj
      apply hnotCovered
      rw [r5CrossCoveredVertices, mem_biUnion]
      refine ⟨index, mem_univ index, ?_⟩
      rw [r5ExteriorNeighbors, mem_inter,
        SimpleGraph.mem_neighborFinset]
      exact ⟨hadj, hvertex⟩
    exact hexists ⟨vertex, hvertex, hzero⟩
  have htwenty :
      20 ≤ #(r5CrossCoveredVertices G) := by
    simpa using card_le_card hcover
  have heighteen :=
    card_r5CrossCoveredVertices_le_eighteen_of_adj_one_five
      G hregular hneighbor hadj
  omega

theorem r5FinalRepresentative_edge_three
    (branch : Fin 26) (hbranch : 20 ≤ branch) :
    edgeVectorOfCode
      (r5NeighborhoodRepresentativeCode branch) 3 = true := by
  fin_cases branch <;>
    revert hbranch <;>
    decide

theorem r5AdjOneFive_of_final_branch
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (branch : Fin 26) (hbranch : 20 ≤ branch)
    (horbit : ∀ left right : Fin 5,
      decide (G.Adj (r5NeighborVertex left) (r5NeighborVertex right)) =
        r5FiveVertexAdjacency
          (edgeVectorOfCode (r5NeighborhoodRepresentativeCode branch))
          left right) :
    G.Adj 1 5 := by
  have hedge := horbit 0 4
  change decide (G.Adj 1 5) =
    edgeVectorOfCode
      (r5NeighborhoodRepresentativeCode branch) 3 at hedge
  rw [r5FinalRepresentative_edge_three branch hbranch] at hedge
  simpa using hedge

theorem exists_r5ZeroPatternExterior_of_final_branch
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (branch : Fin 26) (hbranch : 20 ≤ branch)
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (horbit : ∀ left right : Fin 5,
      decide (G.Adj (r5NeighborVertex left) (r5NeighborVertex right)) =
        r5FiveVertexAdjacency
          (edgeVectorOfCode (r5NeighborhoodRepresentativeCode branch))
          left right) :
    ∃ anchor : Fin 26,
      anchor ∈ r5ExteriorVertices ∧
      ∀ index : Fin 5,
        ¬G.Adj (r5NeighborVertex index) anchor :=
  exists_r5ZeroPatternExterior_of_adj_one_five
    G hregular hneighbor
      (r5AdjOneFive_of_final_branch G branch hbranch horbit)

/-- The normalized five exterior neighbors of the E045 anchor. -/
def r5FixedAnchorNeighbors : Finset (Fin 26) :=
  {7, 8, 9, 10, 11}

@[simp]
theorem card_r5FixedAnchorNeighbors :
    #r5FixedAnchorNeighbors = 5 := by
  decide

@[simp]
theorem six_notMem_r5FixedAnchorNeighbors :
    (6 : Fin 26) ∉ r5FixedAnchorNeighbors := by
  decide

/-- Embed the six labels below the exterior range. -/
def r5InitialLabelEmbedding : Fin 6 ↪ Fin 26 where
  toFun index := ⟨index, by omega⟩
  inj' := by
    intro left right heq
    have hval :=
      congrArg (fun value : Fin 26 => value.val) heq
    exact Fin.ext hval

/-- Combine an embedding into the exterior range with the fixed initial
labels. -/
def r5InitialExteriorSumEmbedding
    (tail : Option (Fin 5) ↪ Fin 26)
    (htail : ∀ index, 6 ≤ tail index) :
    Fin 6 ⊕ Option (Fin 5) ↪ Fin 26 where
  toFun
    | .inl index => r5InitialLabelEmbedding index
    | .inr index => tail index
  inj' := by
    intro left right heq
    cases left with
    | inl left =>
        cases right with
        | inl right =>
            congr 1
            exact r5InitialLabelEmbedding.injective heq
        | inr right =>
            exfalso
            change r5InitialLabelEmbedding left = tail right at heq
            have hleft : (r5InitialLabelEmbedding left : ℕ) < 6 := by
              simp [r5InitialLabelEmbedding]
            have hright := htail right
            have hval := congrArg Fin.val heq
            omega
    | inr left =>
        cases right with
        | inl right =>
            exfalso
            change tail left = r5InitialLabelEmbedding right at heq
            have hleft := htail left
            have hright : (r5InitialLabelEmbedding right : ℕ) < 6 := by
              simp [r5InitialLabelEmbedding]
            have hval := congrArg Fin.val heq
            omega
        | inr right =>
            congr 1
            exact tail.injective heq

/-- Source embedding for the fixed labels `0, ..., 11`. -/
noncomputable def r5FixedAnchorSourceTail :
    Option (Fin 5) ↪ Fin 26 :=
  pointAndFinsetEmbedding
    (6 : Fin 26) r5FixedAnchorNeighbors
    six_notMem_r5FixedAnchorNeighbors card_r5FixedAnchorNeighbors

theorem r5FixedAnchorSourceTail_ge_six
    (index : Option (Fin 5)) :
    6 ≤ r5FixedAnchorSourceTail index := by
  cases index with
  | none => simp [r5FixedAnchorSourceTail, pointAndFinsetEmbedding]
  | some index =>
      let vertex : Fin 26 :=
        (r5FixedAnchorNeighbors.equivFinOfCardEq
          card_r5FixedAnchorNeighbors).symm index
      have hmem : vertex ∈ r5FixedAnchorNeighbors :=
        ((r5FixedAnchorNeighbors.equivFinOfCardEq
          card_r5FixedAnchorNeighbors).symm index).property
      change 6 ≤ vertex
      simp only [r5FixedAnchorNeighbors, mem_insert, mem_singleton] at hmem
      rcases hmem with h | h | h | h | h
      all_goals simp [h]

noncomputable def r5FixedAnchorSourceEmbedding :
    Fin 6 ⊕ Option (Fin 5) ↪ Fin 26 :=
  r5InitialExteriorSumEmbedding
    r5FixedAnchorSourceTail r5FixedAnchorSourceTail_ge_six

theorem r5AnchorNeighbor_ge_six
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (anchor : Fin 26) (hanchor : anchor ∈ r5ExteriorVertices)
    (hzero : ∀ index : Fin 5,
      ¬G.Adj (r5NeighborVertex index) anchor)
    (vertex : Fin 26) (hvertex : vertex ∈ G.neighborFinset anchor) :
    6 ≤ vertex := by
  by_contra hnotExterior
  have hvertexLT : vertex < 6 := by omega
  have hcases : vertex = 0 ∨ vertex ∈ r5FixedNeighbors := by
    fin_cases vertex <;>
      simp_all [r5FixedNeighbors]
  rcases hcases with rfl | hfixed
  · have hadj : G.Adj 0 anchor := by
      rw [SimpleGraph.mem_neighborFinset] at hvertex
      exact (G.adj_comm anchor 0).mp hvertex
    have hanchorFixed : anchor ∈ r5FixedNeighbors := by
      rw [← hneighbor, SimpleGraph.mem_neighborFinset]
      exact hadj
    have hanchorExterior :=
      (mem_r5ExteriorVertices_iff anchor).mp hanchor
    simp only [r5FixedNeighbors, mem_insert, mem_singleton]
      at hanchorFixed
    rcases hanchorFixed with h | h | h | h | h
    all_goals omega
  · let index := r5FixedNeighborLabelEquiv.symm ⟨vertex, hfixed⟩
    have hlabel :
        r5NeighborVertex index = vertex := by
      exact congrArg Subtype.val
        (r5FixedNeighborLabelEquiv.apply_symm_apply ⟨vertex, hfixed⟩)
    apply hzero index
    rw [hlabel, G.adj_comm, ← SimpleGraph.mem_neighborFinset]
    exact hvertex

/-- Target tail containing the chosen anchor and its five actual neighbors. -/
noncomputable def r5ActualAnchorTargetTail
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ vertex, G.degree vertex = 5)
    (anchor : Fin 26) :
    Option (Fin 5) ↪ Fin 26 :=
  pointAndFinsetEmbedding anchor (G.neighborFinset anchor)
    (G.notMem_neighborFinset_self anchor) (by
      simpa using hregular anchor)

theorem r5ActualAnchorTargetTail_ge_six
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (anchor : Fin 26) (hanchor : anchor ∈ r5ExteriorVertices)
    (hzero : ∀ index : Fin 5,
      ¬G.Adj (r5NeighborVertex index) anchor)
    (index : Option (Fin 5)) :
    6 ≤ r5ActualAnchorTargetTail G hregular anchor index := by
  cases index with
  | none =>
      exact (mem_r5ExteriorVertices_iff anchor).mp hanchor
  | some index =>
      apply r5AnchorNeighbor_ge_six
        G hneighbor anchor hanchor hzero
      exact ((G.neighborFinset anchor).equivFinOfCardEq
        (by simpa using hregular anchor)).symm index |>.property

noncomputable def r5ActualAnchorTargetEmbedding
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (anchor : Fin 26) (hanchor : anchor ∈ r5ExteriorVertices)
    (hzero : ∀ index : Fin 5,
      ¬G.Adj (r5NeighborVertex index) anchor) :
    Fin 6 ⊕ Option (Fin 5) ↪ Fin 26 :=
  r5InitialExteriorSumEmbedding
    (r5ActualAnchorTargetTail G hregular anchor)
    (r5ActualAnchorTargetTail_ge_six
      G hregular hneighbor anchor hanchor hzero)

/-- Relabel a chosen zero-pattern exterior vertex as `6`, its five neighbors
as `7, ..., 11`, and fix `0, ..., 5`. -/
theorem exists_r5RelabelGraph_anchor_six
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (anchor : Fin 26) (hanchor : anchor ∈ r5ExteriorVertices)
    (hzero : ∀ index : Fin 5,
      ¬G.Adj (r5NeighborVertex index) anchor) :
    ∃ relabeling : Equiv.Perm (Fin 26),
      (∀ vertex : Fin 26, vertex < 6 → relabeling vertex = vertex) ∧
      relabeling 6 = anchor ∧
      (relabelGraph G relabeling).neighborFinset 0 =
        r5FixedNeighbors ∧
      (relabelGraph G relabeling).neighborFinset 6 =
        r5FixedAnchorNeighbors := by
  classical
  let source := r5FixedAnchorSourceEmbedding
  let target :=
    r5ActualAnchorTargetEmbedding
      G hregular hneighbor anchor hanchor hzero
  obtain ⟨relabeling, hrelabeling⟩ :=
    Equiv.Perm.exists_extending_pair
      source target source.injective target.injective
  have hfixed (vertex : Fin 26) (hvertex : vertex < 6) :
      relabeling vertex = vertex := by
    let index : Fin 6 := ⟨vertex, hvertex⟩
    have hmap := hrelabeling (Sum.inl index)
    simpa [source, target, r5FixedAnchorSourceEmbedding,
      r5ActualAnchorTargetEmbedding, r5InitialExteriorSumEmbedding,
      r5InitialLabelEmbedding, index] using hmap
  have hanchorMap : relabeling 6 = anchor := by
    have hmap := hrelabeling (Sum.inr none)
    simpa [source, target, r5FixedAnchorSourceEmbedding,
      r5ActualAnchorTargetEmbedding, r5InitialExteriorSumEmbedding,
      r5FixedAnchorSourceTail, r5ActualAnchorTargetTail,
      pointAndFinsetEmbedding] using hmap
  have hzeroNeighbor :
      (relabelGraph G relabeling).neighborFinset 0 =
        r5FixedNeighbors := by
    have hsubset :
        r5FixedNeighbors ⊆
          (relabelGraph G relabeling).neighborFinset 0 := by
      intro vertex hvertex
      have hvertexLT : vertex < 6 := by
        simp only [r5FixedNeighbors, mem_insert, mem_singleton] at hvertex
        rcases hvertex with h | h | h | h | h
        all_goals omega
      rw [SimpleGraph.mem_neighborFinset, relabelGraph_adj_iff,
        hfixed 0 (by omega), hfixed vertex hvertexLT,
        ← SimpleGraph.mem_neighborFinset, hneighbor]
      exact hvertex
    have hdegree :
        (relabelGraph G relabeling).degree 0 = 5 := by
      rw [relabelGraph_degree, hfixed 0 (by omega), hregular]
    have hcard :
        #((relabelGraph G relabeling).neighborFinset 0) ≤
          #r5FixedNeighbors := by
      simp [hdegree]
    exact (Finset.eq_of_subset_of_card_le hsubset hcard).symm
  have hanchorNeighbor :
      (relabelGraph G relabeling).neighborFinset 6 =
        r5FixedAnchorNeighbors := by
    have hsubset :
        r5FixedAnchorNeighbors ⊆
          (relabelGraph G relabeling).neighborFinset 6 := by
      intro vertex hvertex
      let index : Fin 5 :=
        (r5FixedAnchorNeighbors.equivFinOfCardEq
          card_r5FixedAnchorNeighbors) ⟨vertex, hvertex⟩
      have hsource :
          source (Sum.inr (some index)) = vertex := by
        simp [source, r5FixedAnchorSourceEmbedding,
          r5InitialExteriorSumEmbedding, r5FixedAnchorSourceTail,
          pointAndFinsetEmbedding, index]
      have htarget :
          target (Sum.inr (some index)) ∈
            G.neighborFinset anchor := by
        exact ((G.neighborFinset anchor).equivFinOfCardEq
          (by simpa using hregular anchor)).symm index |>.property
      have himage :
          relabeling vertex =
            target (Sum.inr (some index)) := by
        rw [← hsource]
        exact hrelabeling _
      rw [SimpleGraph.mem_neighborFinset, relabelGraph_adj_iff,
        hanchorMap, ← SimpleGraph.mem_neighborFinset, himage]
      exact htarget
    have hdegree :
        (relabelGraph G relabeling).degree 6 = 5 := by
      rw [relabelGraph_degree, hanchorMap, hregular]
    have hcard :
        #((relabelGraph G relabeling).neighborFinset 6) ≤
          #r5FixedAnchorNeighbors := by
      simp [hdegree]
    exact (Finset.eq_of_subset_of_card_le hsubset hcard).symm
  exact ⟨relabeling, hfixed, hanchorMap,
    hzeroNeighbor, hanchorNeighbor⟩

end Erdos617
