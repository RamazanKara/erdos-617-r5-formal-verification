/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.Sat.SpecialBrooksBranch19Bridge
public import Erdos617.Sat.SpecialBrooksFiniteTransport

/-!
# Graph bridge for the E043 parent-19 zero-anchor quotient

The nineteenth E042 cross pattern has sixteen zero rows followed by the four
rows `3, 5, 9, 17`.  Vertex `6` is therefore a zero-pattern anchor.  This file
uses the checked stabilizer action from `ZeroAnchorOrbitCertificate` and a
finite predicate transport inside labels `7, ..., 21` to normalize its five
exterior neighbors to one of the five E043 parent-19 children.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

/-- Zero-pattern rows other than the anchor itself in E042 child 19. -/
def r5P19ZeroBlock (vertex : Fin 26) : Prop :=
  7 ≤ vertex ∧ vertex < 22

instance : DecidablePred r5P19ZeroBlock := by
  intro vertex
  unfold r5P19ZeroBlock
  infer_instance

/-- The initial segment of zero rows selected by an E043 parent-19 child. -/
def r5P19TargetZeroNeighbor
    (child : Fin 5) (value : {vertex : Fin 26 // r5P19ZeroBlock vertex}) :
    Prop :=
  (value.1 : Nat) <
    7 + (5 - r5ZeroAnchorP19RepresentativeWeight child)

instance (child : Fin 5) :
    DecidablePred (r5P19TargetZeroNeighbor child) := by
  intro value
  unfold r5P19TargetZeroNeighbor
  infer_instance

theorem r5P19TargetZeroNeighbor_card (child : Fin 5) :
    Fintype.card
        {value : {vertex : Fin 26 // r5P19ZeroBlock vertex} //
          r5P19TargetZeroNeighbor child value} =
      5 - r5ZeroAnchorP19RepresentativeWeight child := by
  fin_cases child <;> decide

/-- The exact Boolean assigned to edge `6 -- (offset + 7)` by an E043 child. -/
def r5P19AnchorTargetBit (child : Fin 5) (offset : Fin 19) : Bool :=
  if _hoffset : (offset : Nat) < 15 then
    decide ((offset : Nat) <
      5 - r5ZeroAnchorP19RepresentativeWeight child)
  else
    Nat.testBit (r5ZeroAnchorP19Representative child)
      ((offset : Nat) - 15)

/-- The nineteen anchor-to-exterior primary units added by E043. -/
def r5CanonicalE043P19AnchorUnits (child : Fin 5) :
    List R5NamedLiteral :=
  List.ofFn fun offset : Fin 19 =>
    r5EdgeLiteralFromBool 6
      ⟨(offset : Nat) + 7, by omega⟩
      (r5P19AnchorTargetBit child offset)

def r5CanonicalE043P19Units (child : Fin 5) :
    List R5NamedLiteral :=
  r5CanonicalE042Units 19 ++
    r5CanonicalE043P19AnchorUnits child

def r5P19NonzeroAnchorBits
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] :
    Fin 4 → Bool :=
  fun index =>
    decide (G.Adj 6
      ⟨(index : Nat) + 22, by omega⟩)

theorem r5Fin4EdgeBit_sum_le_five :
    ∀ bits : Fin 4 → Bool,
      (∑ index, edgeBit (bits index)) ≤ 5 := by
  decide

theorem r5ZeroAnchorP19Witness_weight
    (bits : Fin 4 → Bool)
    (hle : (∑ index, edgeBit (bits index)) ≤ 5) :
    (∑ index, edgeBit (bits index)) =
      r5ZeroAnchorP19RepresentativeWeight
        (r5ZeroAnchorP19WitnessChild bits) := by
  let witness := r5ZeroAnchorP19WitnessAction bits
  have hperm :=
    Equiv.sum_comp
      (r5ZeroAnchorP19RowPermutation witness).symm
      (fun index : Fin 4 => edgeBit (bits index))
  calc
    (∑ index, edgeBit (bits index)) =
        ∑ index,
          edgeBit
            (r5ZeroAnchorP19TransformedBits bits witness index) := by
      change (∑ index, edgeBit (bits index)) =
        ∑ index,
          edgeBit
            (bits
              ((r5ZeroAnchorP19RowPermutation witness).symm index))
      exact hperm.symm
    _ = r5ZeroAnchorP19RepresentativeWeight
          (r5ZeroAnchorP19WitnessChild bits) := by
      apply Fintype.sum_congr
      intro index
      rw [r5_zero_anchor_19_orbit_bits_check bits hle index]

theorem r5P19Anchor_not_adj_zero
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors) :
    ¬G.Adj 6 0 := by
  rw [G.adj_comm, ← SimpleGraph.mem_neighborFinset, hneighbor]
  decide

theorem r5P19Anchor_not_adj_fixed
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hcodes : ∀ row : Fin 20,
      r5ExteriorPatternCode G ((row : Nat) + 6) =
        r5CrossPatternSortedCode 19 row)
    (position : Fin 5) :
    ¬G.Adj 6 (r5NeighborVertex position) := by
  rw [G.adj_comm]
  apply of_decide_eq_false
  rw [← r5ExteriorPatternCode_testBit]
  have hcode0 :
      r5ExteriorPatternCode G (6 : Fin 26) = 0 := by
    simpa [r5CrossPatternSortedCode] using hcodes 0
  rw [hcode0]
  fin_cases position <;> decide

set_option maxHeartbeats 400000 in
-- The proof expands one 26-term degree sum and the matching 15+4 split.
theorem r5P19Anchor_degree_split
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (hcodes : ∀ row : Fin 20,
      r5ExteriorPatternCode G ((row : Nat) + 6) =
        r5CrossPatternSortedCode 19 row) :
    (∑ index : Fin 15,
      if G.Adj 6 ⟨(index : Nat) + 7, by omega⟩ then 1 else 0) +
    (∑ index : Fin 4,
      if G.Adj 6 ⟨(index : Nat) + 22, by omega⟩ then 1 else 0) =
      5 := by
  have hdegree :=
    SimpleGraph.degree_eq_sum_if_adj (R := Nat) G 6
  rw [hregular 6] at hdegree
  have h0 := r5P19Anchor_not_adj_zero G hneighbor
  have h1 := r5P19Anchor_not_adj_fixed G hcodes 0
  have h2 := r5P19Anchor_not_adj_fixed G hcodes 1
  have h3 := r5P19Anchor_not_adj_fixed G hcodes 2
  have h4 := r5P19Anchor_not_adj_fixed G hcodes 3
  have h5 := r5P19Anchor_not_adj_fixed G hcodes 4
  have h1' : ¬G.Adj 6 (1 : Fin 26) := by
    simpa [r5NeighborVertex] using h1
  have h2' : ¬G.Adj 6 (2 : Fin 26) := by
    simpa [r5NeighborVertex] using h2
  have h3' : ¬G.Adj 6 (3 : Fin 26) := by
    simpa [r5NeighborVertex] using h3
  have h4' : ¬G.Adj 6 (4 : Fin 26) := by
    simpa [r5NeighborVertex] using h4
  have h5' : ¬G.Adj 6 (5 : Fin 26) := by
    simpa [r5NeighborVertex] using h5
  let term : Fin 26 → Nat :=
    fun vertex => if G.Adj 6 vertex then 1 else 0
  let tail : Fin 19 → Nat :=
    fun offset => term (Fin.natAdd 7 offset)
  have hhead :
      (∑ index : Fin 7, term (Fin.castAdd 19 index)) = 0 := by
    simp [term, h0, h1', h2', h3', h4', h5']
  have hlow :
      (∑ index : Fin 15,
        if G.Adj 6 ⟨(index : Nat) + 7, by omega⟩ then 1 else 0) =
        ∑ index : Fin 15, tail (Fin.castAdd 4 index) := by
    apply Fintype.sum_congr
    intro index
    have hvertex :
        (⟨(index : Nat) + 7, by omega⟩ : Fin 26) =
          Fin.natAdd 7 (Fin.castAdd 4 index) := by
      apply Fin.ext
      simp [Nat.add_comm]
    rw [hvertex]
  have hhigh :
      (∑ index : Fin 4,
        if G.Adj 6 ⟨(index : Nat) + 22, by omega⟩ then 1 else 0) =
        ∑ index : Fin 4, tail (Fin.natAdd 15 index) := by
    apply Fintype.sum_congr
    intro index
    have hvertex :
        (⟨(index : Nat) + 22, by omega⟩ : Fin 26) =
          Fin.natAdd 7 (Fin.natAdd 15 index) := by
      apply Fin.ext
      simp [Nat.add_comm, Nat.add_left_comm]
    rw [hvertex]
  have hfull :
      (∑ vertex : Fin 26, term vertex) =
        ∑ offset : Fin 19, tail offset := by
    calc
      (∑ vertex : Fin 26, term vertex) =
          (∑ index : Fin 7, term (Fin.castAdd 19 index)) +
            ∑ offset : Fin 19, term (Fin.natAdd 7 offset) :=
        Fin.sum_univ_add (a := 7) (b := 19) term
      _ = ∑ offset : Fin 19, tail offset := by
        rw [hhead, zero_add]
  calc
    (∑ index : Fin 15,
        if G.Adj 6 ⟨(index : Nat) + 7, by omega⟩ then 1 else 0) +
      (∑ index : Fin 4,
        if G.Adj 6 ⟨(index : Nat) + 22, by omega⟩ then 1 else 0) =
        ∑ offset : Fin 19, tail offset := by
      rw [hlow, hhigh]
      exact (Fin.sum_univ_add (a := 15) (b := 4) tail).symm
    _ = ∑ vertex : Fin 26, term vertex := hfull.symm
    _ = 5 := by
      change
        (∑ vertex : Fin 26,
          if G.Adj 6 vertex then (1 : Nat) else 0) = 5
      exact hdegree.symm

theorem r5P19ZeroSource_card_eq_sum
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] :
    Fintype.card
        {value : {vertex : Fin 26 // r5P19ZeroBlock vertex} //
          G.Adj 6 value} =
      ∑ index : Fin 15,
        if G.Adj 6 ⟨(index : Nat) + 7, by omega⟩ then 1 else 0 := by
  rw [r5CardNestedSubtype_eq_filter_univ]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp [r5P19ZeroBlock, Fin.sum_univ_succ, Nat.add_assoc]
  by_cases hadj : G.Adj 6 21 <;> simp [hadj]

theorem r5P19ZeroSource_card
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (hcodes : ∀ row : Fin 20,
      r5ExteriorPatternCode G ((row : Nat) + 6) =
        r5CrossPatternSortedCode 19 row) :
    Fintype.card
        {value : {vertex : Fin 26 // r5P19ZeroBlock vertex} //
          G.Adj 6 value} =
      5 - ∑ index,
        edgeBit (r5P19NonzeroAnchorBits G index) := by
  rw [r5P19ZeroSource_card_eq_sum]
  have hsplit :=
    r5P19Anchor_degree_split G hregular hneighbor hcodes
  have hnonzero :
      (∑ index : Fin 4,
        if G.Adj 6 ⟨(index : Nat) + 22, by omega⟩ then 1 else 0) =
        ∑ index,
          edgeBit (r5P19NonzeroAnchorBits G index) := by
    apply Fintype.sum_congr
    intro index
    by_cases hadj :
        G.Adj 6 ⟨(index : Nat) + 22, by omega⟩
    · simp [r5P19NonzeroAnchorBits, edgeBit, hadj]
    · simp [r5P19NonzeroAnchorBits, edgeBit, hadj]
  rw [hnonzero] at hsplit
  omega

@[simp]
theorem r5ZeroAnchorP19ActionRelabeling_apply_anchor
    (witness : Fin 24) :
    r5ZeroAnchorP19ActionRelabeling witness 6 = 6 := by
  simp [r5ZeroAnchorP19ActionRelabeling,
    r5ZeroAnchorP19ActionMap]

theorem r5ZeroAnchorP19ActionRelabeling_apply_zeroBlock
    (witness : Fin 24) (vertex : Fin 26)
    (hvertex : r5P19ZeroBlock vertex) :
    r5ZeroAnchorP19ActionRelabeling witness vertex = vertex := by
  rcases hvertex with ⟨hge, hlt⟩
  change r5ZeroAnchorP19ActionMap witness vertex = vertex
  simp [r5ZeroAnchorP19ActionMap,
    show ¬(1 ≤ (vertex : Nat) ∧ (vertex : Nat) < 5) by omega,
    show ¬22 ≤ (vertex : Nat) by omega]

theorem r5ZeroAnchorP19ActionRelabeling_preserves_fixed :
    ∀ witness vertex,
      r5ZeroAnchorP19ActionRelabeling witness vertex ∈
          r5FixedNeighbors ↔
        vertex ∈ r5FixedNeighbors := by
  decide

/-- The source neighborhood position read after applying the P19 action. -/
def r5ZeroAnchorP19SourcePosition
    (witness : Fin 24) (position : Fin 5) : Fin 5 :=
  if hposition : (position : Nat) < 4 then
    (r5ZeroAnchorP19ColumnInverseMap witness
      ⟨position, hposition⟩).castSucc
  else
    4

/-- The source exterior row read after applying the P19 action. -/
def r5ZeroAnchorP19SourceRow
    (witness : Fin 24) (row : Fin 20) : Fin 20 :=
  if hrow : (row : Nat) < 16 then
    row
  else
    ⟨(r5ZeroAnchorP19RowInverseMap witness
        ⟨(row : Nat) - 16, by omega⟩ : Nat) + 16,
      by omega⟩

set_option maxRecDepth 10000 in
theorem r5ZeroAnchorP19ActionRelabeling_apply_neighbor :
    ∀ witness position,
      r5ZeroAnchorP19ActionRelabeling witness
          (r5NeighborVertex position) =
        r5NeighborVertex
          (r5ZeroAnchorP19SourcePosition witness position) := by
  decide

set_option maxRecDepth 10000 in
theorem r5ZeroAnchorP19ActionRelabeling_apply_exterior :
    ∀ (witness : Fin 24) (row : Fin 20),
      r5ZeroAnchorP19ActionRelabeling witness
          ⟨(row : Nat) + 6, by omega⟩ =
        ⟨(r5ZeroAnchorP19SourceRow witness row : Nat) + 6,
          by omega⟩ := by
  decide

set_option maxRecDepth 10000 in
theorem r5ZeroAnchorP19SourceBit :
    ∀ witness row position,
      Nat.testBit
          (r5CrossPatternSortedCode 19
            (r5ZeroAnchorP19SourceRow witness row))
          (4 -
            (r5ZeroAnchorP19SourcePosition witness position : Nat)) =
        Nat.testBit (r5CrossPatternSortedCode 19 row)
          (4 - (position : Nat)) := by
  decide

set_option maxRecDepth 10000 in
theorem r5ZeroAnchorP19SourceNeighborhoodInvariant :
    ∀ witness left right,
      r5FiveVertexAdjacency
          (edgeVectorOfCode (r5NeighborhoodRepresentativeCode 19))
          (r5ZeroAnchorP19SourcePosition witness left)
          (r5ZeroAnchorP19SourcePosition witness right) =
        r5FiveVertexAdjacency
          (edgeVectorOfCode (r5NeighborhoodRepresentativeCode 19))
          left right := by
  decide

/-- Reading one graph adjacency from its five-bit exterior-row code. -/
theorem r5Adj_iff_exteriorPatternCode_testBit
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (exterior : Fin 26) (position : Fin 5) :
    G.Adj (r5NeighborVertex position) exterior ↔
      Nat.testBit (r5ExteriorPatternCode G exterior)
        (4 - (position : Nat)) = true := by
  have hbit :=
    r5ExteriorPatternCode_testBit G exterior position
  constructor
  · intro hadj
    have hdecide :
        decide (G.Adj (r5NeighborVertex position) exterior) = true := by
      simp [hadj]
    rw [← hbit] at hdecide
    exact hdecide
  · intro hbitTrue
    apply of_decide_eq_true
    rw [← hbit]
    exact hbitTrue

theorem r5ZeroAnchorP19ActionRelabeling_codes
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hcodes : ∀ row : Fin 20,
      r5ExteriorPatternCode G ((row : Nat) + 6) =
        r5CrossPatternSortedCode 19 row)
    (witness : Fin 24) (row : Fin 20) :
    r5ExteriorPatternCode
        (relabelGraph G
          (r5ZeroAnchorP19ActionRelabeling witness))
        ((row : Nat) + 6) =
      r5CrossPatternSortedCode 19 row := by
  have hadj (position : Fin 5) :
      (relabelGraph G
        (r5ZeroAnchorP19ActionRelabeling witness)).Adj
          (r5NeighborVertex position)
          ⟨(row : Nat) + 6, by omega⟩ ↔
        Nat.testBit (r5CrossPatternSortedCode 19 row)
          (4 - (position : Nat)) = true := by
    change G.Adj
      (r5ZeroAnchorP19ActionRelabeling witness
        (r5NeighborVertex position))
      (r5ZeroAnchorP19ActionRelabeling witness
        ⟨(row : Nat) + 6, by omega⟩) ↔ _
    rw [r5ZeroAnchorP19ActionRelabeling_apply_neighbor,
      r5ZeroAnchorP19ActionRelabeling_apply_exterior,
      r5Adj_iff_exteriorPatternCode_testBit,
      hcodes (r5ZeroAnchorP19SourceRow witness row),
      r5ZeroAnchorP19SourceBit]
  change r5ExteriorPatternCode
      (relabelGraph G
        (r5ZeroAnchorP19ActionRelabeling witness))
      (⟨(row : Nat) + 6, by omega⟩ : Fin 26) =
    r5CrossPatternSortedCode 19 row
  rw [r5ExteriorPatternCode_eq_sum]
  simp_rw [hadj]
  fin_cases row <;> decide

theorem r5ZeroAnchorP19ActionRelabeling_orbit
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (horbit : ∀ left right : Fin 5,
      decide (G.Adj (r5NeighborVertex left)
        (r5NeighborVertex right)) =
      r5FiveVertexAdjacency
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode 19))
        left right)
    (witness : Fin 24) :
    ∀ left right : Fin 5,
      decide ((relabelGraph G
        (r5ZeroAnchorP19ActionRelabeling witness)).Adj
          (r5NeighborVertex left)
          (r5NeighborVertex right)) =
      r5FiveVertexAdjacency
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode 19))
        left right := by
  intro left right
  change decide (G.Adj
    (r5ZeroAnchorP19ActionRelabeling witness
      (r5NeighborVertex left))
    (r5ZeroAnchorP19ActionRelabeling witness
      (r5NeighborVertex right))) = _
  rw [r5ZeroAnchorP19ActionRelabeling_apply_neighbor,
    r5ZeroAnchorP19ActionRelabeling_apply_neighbor,
    horbit, r5ZeroAnchorP19SourceNeighborhoodInvariant]

@[simp]
theorem r5ZeroAnchorP19ActionRelabeling_apply_zero
    (witness : Fin 24) :
    r5ZeroAnchorP19ActionRelabeling witness 0 = 0 := by
  simp [r5ZeroAnchorP19ActionRelabeling,
    r5ZeroAnchorP19ActionMap]

set_option maxRecDepth 10000 in
theorem r5ZeroAnchorP19ActionRelabeling_apply_nonzeroRow :
    ∀ (witness : Fin 24) (index : Fin 4),
      r5ZeroAnchorP19ActionRelabeling witness
          ⟨(index : Nat) + 22, by omega⟩ =
        ⟨(r5ZeroAnchorP19RowInverseMap witness index : Nat) + 22,
          by omega⟩ := by
  decide

theorem r5ZeroAnchorP19ActionRelabeling_anchorBits
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (witness : Fin 24) (index : Fin 4) :
    decide ((relabelGraph G
      (r5ZeroAnchorP19ActionRelabeling witness)).Adj
        6 ⟨(index : Nat) + 22, by omega⟩) =
      r5ZeroAnchorP19TransformedBits
        (r5P19NonzeroAnchorBits G) witness index := by
  change decide (G.Adj
    (r5ZeroAnchorP19ActionRelabeling witness 6)
    (r5ZeroAnchorP19ActionRelabeling witness
      ⟨(index : Nat) + 22, by omega⟩)) = _
  rw [r5ZeroAnchorP19ActionRelabeling_apply_anchor,
    r5ZeroAnchorP19ActionRelabeling_apply_nonzeroRow]
  rfl

/-- Relabeling only the exterior endpoint preserves its row code when all
five distinguished neighborhood labels are fixed. -/
theorem r5ExteriorPatternCode_relabel_of_fixedNeighbors
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (relabeling : Equiv.Perm (Fin 26))
    (hfixed : ∀ position : Fin 5,
      relabeling (r5NeighborVertex position) =
        r5NeighborVertex position)
    (vertex : Fin 26) :
    r5ExteriorPatternCode (relabelGraph G relabeling) vertex =
      r5ExteriorPatternCode G (relabeling vertex) := by
  rw [r5ExteriorPatternCode_eq_sum,
    r5ExteriorPatternCode_eq_sum]
  apply Fintype.sum_congr
  intro position
  simp only [relabelGraph_adj_iff, hfixed position]

theorem r5P19ZeroBlock_sortedCode :
    ∀ row : Fin 20,
      r5P19ZeroBlock
          (⟨(row : Nat) + 6, by omega⟩ : Fin 26) →
        r5CrossPatternSortedCode 19 row = 0 := by
  decide

/-- Every graph in the nineteenth E042 cross-pattern branch can be relabeled
to one exact E043 parent-19 child.  The first relabeling applies the checked
stabilizer action on the four nonzero rows.  The second acts only inside the
fifteen interchangeable zero rows. -/
theorem exists_r5CanonicalE043P19Child
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hG : Admissible G)
    (hclique : G.CliqueFree 6)
    (hindep : G.IndepSetFree 6)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (horbit : ∀ left right : Fin 5,
      decide (G.Adj (r5NeighborVertex left)
        (r5NeighborVertex right)) =
      r5FiveVertexAdjacency
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode 19))
        left right)
    (hcodes : ∀ row : Fin 20,
      r5ExteriorPatternCode G ((row : Nat) + 6) =
        r5CrossPatternSortedCode 19 row) :
    ∃ child : Fin 5, ∃ relabeling : Equiv.Perm (Fin 26),
      let H := relabelGraph G relabeling
      (∀ vertex, H.degree vertex = 5) ∧
      Admissible H ∧
      H.CliqueFree 6 ∧
      H.IndepSetFree 6 ∧
      H.neighborFinset 0 = r5FixedNeighbors ∧
      R5ComparisonsSorted H r5FullExteriorComparisons ∧
      (∀ left right : Fin 5,
        decide (H.Adj (r5NeighborVertex left)
          (r5NeighborVertex right)) =
        r5FiveVertexAdjacency
          (edgeVectorOfCode
            (r5NeighborhoodRepresentativeCode 19))
          left right) ∧
      (∀ row : Fin 20,
        r5ExteriorPatternCode H ((row : Nat) + 6) =
          r5CrossPatternSortedCode 19 row) ∧
      ∀ offset : Fin 19,
        decide (H.Adj 6
          ⟨(offset : Nat) + 7, by omega⟩) =
        r5P19AnchorTargetBit child offset := by
  classical
  let bits := r5P19NonzeroAnchorBits G
  let child := r5ZeroAnchorP19WitnessChild bits
  let witness := r5ZeroAnchorP19WitnessAction bits
  let firstRelabeling :=
    r5ZeroAnchorP19ActionRelabeling witness
  let firstGraph := relabelGraph G firstRelabeling
  have hbitsLe :
      (∑ index, edgeBit (bits index)) ≤ 5 :=
    r5Fin4EdgeBit_sum_le_five bits
  have hweight :
      (∑ index, edgeBit (bits index)) =
        r5ZeroAnchorP19RepresentativeWeight child := by
    exact r5ZeroAnchorP19Witness_weight bits hbitsLe
  have hsourceCard :
      Fintype.card
          {value : {vertex : Fin 26 // r5P19ZeroBlock vertex} //
            G.Adj 6 value} =
        5 - ∑ index, edgeBit (bits index) := by
    simpa [bits] using
      r5P19ZeroSource_card G hregular hneighbor hcodes
  have hcard :
      Fintype.card
          {value :
              {vertex : Fin 26 // r5P19ZeroBlock vertex} //
            r5P19TargetZeroNeighbor child value} =
        Fintype.card
          {value :
              {vertex : Fin 26 // r5P19ZeroBlock vertex} //
            G.Adj 6 value} := by
    calc
      Fintype.card
          {value :
              {vertex : Fin 26 // r5P19ZeroBlock vertex} //
            r5P19TargetZeroNeighbor child value} =
          5 - r5ZeroAnchorP19RepresentativeWeight child :=
        r5P19TargetZeroNeighbor_card child
      _ = 5 - ∑ index, edgeBit (bits index) := by
        rw [hweight]
      _ = Fintype.card
          {value :
              {vertex : Fin 26 // r5P19ZeroBlock vertex} //
            G.Adj 6 value} :=
        hsourceCard.symm
  let secondRelabeling :=
    r5BlockPredicateTransportPerm
      r5P19ZeroBlock
      (r5P19TargetZeroNeighbor child)
      (fun value => G.Adj 6 value)
      hcard
  let finalGraph := relabelGraph firstGraph secondRelabeling
  let finalRelabeling := secondRelabeling.trans firstRelabeling
  have hsecondOutside
      (vertex : Fin 26) (hvertex : ¬r5P19ZeroBlock vertex) :
      secondRelabeling vertex = vertex := by
    exact r5BlockPredicateTransportPerm_apply_outside
      r5P19ZeroBlock
      (r5P19TargetZeroNeighbor child)
      (fun value => G.Adj 6 value)
      hcard vertex hvertex
  have hsecondInside
      (vertex : Fin 26) (hvertex : r5P19ZeroBlock vertex) :
      secondRelabeling vertex =
        r5PredicateTransportPerm
          (r5P19TargetZeroNeighbor child)
          (fun value => G.Adj 6 value)
          hcard ⟨vertex, hvertex⟩ := by
    exact r5BlockPredicateTransportPerm_apply_inside
      r5P19ZeroBlock
      (r5P19TargetZeroNeighbor child)
      (fun value => G.Adj 6 value)
      hcard vertex hvertex
  have hsecondBlock
      (vertex : Fin 26) (hvertex : r5P19ZeroBlock vertex) :
      r5P19ZeroBlock (secondRelabeling vertex) := by
    rw [hsecondInside vertex hvertex]
    exact (r5PredicateTransportPerm
      (r5P19TargetZeroNeighbor child)
      (fun value => G.Adj 6 value)
      hcard ⟨vertex, hvertex⟩).property
  have htransport
      (vertex : Fin 26) (hvertex : r5P19ZeroBlock vertex) :
      G.Adj 6 (secondRelabeling vertex) ↔
        r5P19TargetZeroNeighbor child ⟨vertex, hvertex⟩ := by
    rw [hsecondInside vertex hvertex]
    exact r5PredicateTransportPerm_mem_iff
      (r5P19TargetZeroNeighbor child)
      (fun value => G.Adj 6 value)
      hcard ⟨vertex, hvertex⟩
  have hfirstNeighbor :
      firstGraph.neighborFinset 0 = r5FixedNeighbors := by
    ext vertex
    rw [SimpleGraph.mem_neighborFinset, relabelGraph_adj_iff,
      r5ZeroAnchorP19ActionRelabeling_apply_zero,
      ← SimpleGraph.mem_neighborFinset, hneighbor,
      r5ZeroAnchorP19ActionRelabeling_preserves_fixed]
  have hsecondFixedNeighbor (position : Fin 5) :
      secondRelabeling (r5NeighborVertex position) =
        r5NeighborVertex position := by
    apply hsecondOutside
    intro hblock
    have hge := hblock.1
    change 7 ≤ (position : Nat) + 1 at hge
    omega
  have hfinalNeighbor :
      finalGraph.neighborFinset 0 = r5FixedNeighbors := by
    have hsubset :
        r5FixedNeighbors ⊆ finalGraph.neighborFinset 0 := by
      intro vertex hvertex
      have hvertexLT : vertex < 6 := by
        simp only [r5FixedNeighbors, mem_insert, mem_singleton]
          at hvertex
        rcases hvertex with h | h | h | h | h
        all_goals omega
      rw [SimpleGraph.mem_neighborFinset]
      change firstGraph.Adj
        (secondRelabeling 0) (secondRelabeling vertex)
      rw [hsecondOutside 0 (by
          unfold r5P19ZeroBlock
          omega),
        hsecondOutside vertex (by
          unfold r5P19ZeroBlock
          omega),
        ← SimpleGraph.mem_neighborFinset, hfirstNeighbor]
      exact hvertex
    have hdegree : finalGraph.degree 0 = 5 := by
      change
        (relabelGraph firstGraph secondRelabeling).degree 0 = 5
      rw [relabelGraph_degree]
      change
        (relabelGraph G firstRelabeling).degree
          (secondRelabeling 0) = 5
      rw [relabelGraph_degree]
      exact hregular _
    have hcardNeighbor :
        #(finalGraph.neighborFinset 0) ≤ #r5FixedNeighbors := by
      simp [hdegree]
    exact
      (Finset.eq_of_subset_of_card_le hsubset hcardNeighbor).symm
  have hfirstOrbit :
      ∀ left right : Fin 5,
        decide (firstGraph.Adj
          (r5NeighborVertex left)
          (r5NeighborVertex right)) =
        r5FiveVertexAdjacency
          (edgeVectorOfCode
            (r5NeighborhoodRepresentativeCode 19))
          left right :=
    r5ZeroAnchorP19ActionRelabeling_orbit
      G horbit witness
  have hfinalOrbit :
      ∀ left right : Fin 5,
        decide (finalGraph.Adj
          (r5NeighborVertex left)
          (r5NeighborVertex right)) =
        r5FiveVertexAdjacency
          (edgeVectorOfCode
            (r5NeighborhoodRepresentativeCode 19))
          left right := by
    intro left right
    change decide (firstGraph.Adj
      (secondRelabeling (r5NeighborVertex left))
      (secondRelabeling (r5NeighborVertex right))) = _
    rw [hsecondFixedNeighbor left,
      hsecondFixedNeighbor right]
    exact hfirstOrbit left right
  have hfirstCodes :
      ∀ row : Fin 20,
        r5ExteriorPatternCode firstGraph
            ((row : Nat) + 6) =
          r5CrossPatternSortedCode 19 row :=
    r5ZeroAnchorP19ActionRelabeling_codes
      G hcodes witness
  have hfirstBlockCode
      (vertex : Fin 26) (hvertex : r5P19ZeroBlock vertex) :
      r5ExteriorPatternCode firstGraph vertex = 0 := by
    let row : Fin 20 :=
      ⟨(vertex : Nat) - 6, by
        rcases hvertex with ⟨-, hlt⟩
        omega⟩
    have hrowValue :
        (row : Nat) + 6 = (vertex : Nat) := by
      dsimp [row]
      rcases hvertex with ⟨hge, -⟩
      omega
    rw [← hrowValue, hfirstCodes row]
    apply r5P19ZeroBlock_sortedCode row
    have hrowVertex :
        (⟨(row : Nat) + 6, by omega⟩ : Fin 26) =
          vertex := by
      apply Fin.ext
      exact hrowValue
    rw [hrowVertex]
    exact hvertex
  have hfinalCodes :
      ∀ row : Fin 20,
        r5ExteriorPatternCode finalGraph
            ((row : Nat) + 6) =
          r5CrossPatternSortedCode 19 row := by
    intro row
    let vertex : Fin 26 :=
      ⟨(row : Nat) + 6, by omega⟩
    change r5ExteriorPatternCode finalGraph vertex =
      r5CrossPatternSortedCode 19 row
    rw [show r5ExteriorPatternCode finalGraph vertex =
        r5ExteriorPatternCode firstGraph
          (secondRelabeling vertex) by
      exact r5ExteriorPatternCode_relabel_of_fixedNeighbors
        firstGraph secondRelabeling
        hsecondFixedNeighbor vertex]
    by_cases hvertex : r5P19ZeroBlock vertex
    · rw [hfirstBlockCode
          (secondRelabeling vertex)
          (hsecondBlock vertex hvertex),
        r5P19ZeroBlock_sortedCode row hvertex]
    · rw [hsecondOutside vertex hvertex]
      exact hfirstCodes row
  have hfinalSorted :
      R5ComparisonsSorted
        finalGraph r5FullExteriorComparisons := by
    intro comparison hcomparison
    rw [r5FullExteriorComparisons, List.mem_map] at hcomparison
    obtain ⟨offset, hoffset, rfl⟩ := hcomparison
    have hoffsetLT : offset < 19 := List.mem_range.mp hoffset
    apply propLexicographicLE_of_r5ExteriorPatternCode_le
    change
      r5ExteriorPatternCode finalGraph (offset + 6) ≤
        r5ExteriorPatternCode finalGraph (offset + 7)
    rw [hfinalCodes ⟨offset, by omega⟩,
      hfinalCodes ⟨offset + 1, by omega⟩]
    exact r5CrossPatternSortedCode_monotone 19
      (show (⟨offset, by omega⟩ : Fin 20) ≤
        ⟨offset + 1, by omega⟩ by
          simp only [Fin.mk_le_mk]
          omega)
  have hfinalAnchorBlock
      (vertex : Fin 26) (hvertex : r5P19ZeroBlock vertex) :
      finalGraph.Adj 6 vertex ↔
        r5P19TargetZeroNeighbor child ⟨vertex, hvertex⟩ := by
    change firstGraph.Adj
      (secondRelabeling 6) (secondRelabeling vertex) ↔ _
    rw [hsecondOutside 6 (by
        unfold r5P19ZeroBlock
        omega)]
    change G.Adj
      (firstRelabeling 6)
      (firstRelabeling (secondRelabeling vertex)) ↔ _
    rw [r5ZeroAnchorP19ActionRelabeling_apply_anchor,
      r5ZeroAnchorP19ActionRelabeling_apply_zeroBlock
        witness (secondRelabeling vertex)
        (hsecondBlock vertex hvertex)]
    exact htransport vertex hvertex
  have hfinalAnchorNonzero (index : Fin 4) :
      decide (finalGraph.Adj 6
        ⟨(index : Nat) + 22, by omega⟩) =
      r5ZeroAnchorP19TransformedBits bits witness index := by
    have hanchorOutside : ¬r5P19ZeroBlock (6 : Fin 26) := by
      unfold r5P19ZeroBlock
      omega
    have hrowOutside :
        ¬r5P19ZeroBlock
          (⟨(index : Nat) + 22, by omega⟩ : Fin 26) := by
      intro hblock
      have hlt := hblock.2
      change (index : Nat) + 22 < 22 at hlt
      omega
    change decide (firstGraph.Adj
      (secondRelabeling 6)
      (secondRelabeling
        ⟨(index : Nat) + 22, by omega⟩)) = _
    rw [hsecondOutside 6 hanchorOutside,
      hsecondOutside _ hrowOutside]
    exact r5ZeroAnchorP19ActionRelabeling_anchorBits
      G witness index
  have hfinalAnchor :
      ∀ offset : Fin 19,
        decide (finalGraph.Adj 6
          ⟨(offset : Nat) + 7, by omega⟩) =
        r5P19AnchorTargetBit child offset := by
    intro offset
    by_cases hoffset : (offset : Nat) < 15
    · have hvertex :
          r5P19ZeroBlock
            (⟨(offset : Nat) + 7, by omega⟩ : Fin 26) := by
        constructor
        · change 7 ≤ (offset : Nat) + 7
          omega
        · change (offset : Nat) + 7 < 22
          omega
      have hadj :
          finalGraph.Adj 6
              ⟨(offset : Nat) + 7, by omega⟩ ↔
            (offset : Nat) <
              5 - r5ZeroAnchorP19RepresentativeWeight child := by
        calc
          finalGraph.Adj 6
              ⟨(offset : Nat) + 7, by omega⟩ ↔
              r5P19TargetZeroNeighbor child
                ⟨⟨(offset : Nat) + 7, by omega⟩, hvertex⟩ :=
            hfinalAnchorBlock _ hvertex
          _ ↔ (offset : Nat) <
              5 - r5ZeroAnchorP19RepresentativeWeight child := by
            have hrepLe :=
              r5ZeroAnchorP19RepresentativeWeight_le_five child
            change
              (offset : Nat) + 7 <
                  7 +
                    (5 -
                      r5ZeroAnchorP19RepresentativeWeight child) ↔
                (offset : Nat) <
                  5 -
                    r5ZeroAnchorP19RepresentativeWeight child
            omega
      simp only [r5P19AnchorTargetBit, dif_pos hoffset]
      simp only [hadj]
    · let index : Fin 4 :=
        ⟨(offset : Nat) - 15, by omega⟩
      have hvertex :
          (⟨(offset : Nat) + 7, by omega⟩ : Fin 26) =
            ⟨(index : Nat) + 22, by omega⟩ := by
        apply Fin.ext
        dsimp [index]
        omega
      rw [r5P19AnchorTargetBit, dif_neg hoffset,
        hvertex, hfinalAnchorNonzero index,
        r5_zero_anchor_19_orbit_bits_check
          bits hbitsLe index]
  refine ⟨child, finalRelabeling,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro vertex
    rw [relabelGraph_degree]
    exact hregular _
  · change Admissible finalGraph
    exact (admissible_relabelGraph_iff
      firstGraph secondRelabeling).2
      ((admissible_relabelGraph_iff
        G firstRelabeling).2 hG)
  · change finalGraph.CliqueFree 6
    exact (cliqueFree_relabelGraph_iff
      firstGraph secondRelabeling 6).2
      ((cliqueFree_relabelGraph_iff
        G firstRelabeling 6).2 hclique)
  · change finalGraph.IndepSetFree 6
    exact (indepSetFree_relabelGraph_iff
      firstGraph secondRelabeling 6).2
      ((indepSetFree_relabelGraph_iff
        G firstRelabeling 6).2 hindep)
  · change finalGraph.neighborFinset 0 = r5FixedNeighbors
    exact hfinalNeighbor
  · change R5ComparisonsSorted
      finalGraph r5FullExteriorComparisons
    exact hfinalSorted
  · exact hfinalOrbit
  · exact hfinalCodes
  · exact hfinalAnchor

theorem r5CanonicalE043P19AnchorUnits_allTrue
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (child : Fin 5)
    (hanchor : ∀ offset : Fin 19,
      decide (G.Adj 6
        ⟨(offset : Nat) + 7, by omega⟩) =
      r5P19AnchorTargetBit child offset) :
    R5NamedClause.AllTrue G
      (r5CanonicalE043P19AnchorUnits child) := by
  intro literal hliteral
  rw [r5CanonicalE043P19AnchorUnits,
    List.mem_ofFn'] at hliteral
  obtain ⟨offset, rfl⟩ := hliteral
  apply r5EdgeLiteralFromBool_true
  exact hanchor offset

theorem r5CanonicalE043P19Units_allTrue
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (child : Fin 5)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (horbit : ∀ left right : Fin 5,
      decide (G.Adj (r5NeighborVertex left)
        (r5NeighborVertex right)) =
      r5FiveVertexAdjacency
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode 19))
        left right)
    (hcodes : ∀ row : Fin 20,
      r5ExteriorPatternCode G ((row : Nat) + 6) =
        r5CrossPatternSortedCode 19 row)
    (hanchor : ∀ offset : Fin 19,
      decide (G.Adj 6
        ⟨(offset : Nat) + 7, by omega⟩) =
      r5P19AnchorTargetBit child offset) :
    R5NamedClause.AllTrue G
      (r5CanonicalE043P19Units child) := by
  intro literal hliteral
  rw [r5CanonicalE043P19Units,
    List.mem_append] at hliteral
  rcases hliteral with he042 | hanchorLiteral
  · exact r5CanonicalE042Units_allTrue
      G 19 hneighbor horbit hcodes literal he042
  · exact r5CanonicalE043P19AnchorUnits_allTrue
      G child hanchor literal hanchorLiteral

end Erdos617
