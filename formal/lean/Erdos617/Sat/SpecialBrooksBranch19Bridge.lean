/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.Sat.NeighborhoodCrossPatternCertificate
public import Erdos617.Sat.SpecialBrooksZeroAnchor

/-!
# Graph bridge for the E058 branch-19 cross-pattern quotient

Neighborhood branch 19 is a `K₄` plus an isolated fifth vertex.  Regularity
therefore leaves one exterior stub at each `K₄` vertex and four distinct
exterior stubs at the isolated vertex.  This file connects those eight stubs
to the generated twenty-orbit cross-pattern certificate.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

/-- The ten stored edge bits of branch 19: a `K₄` on positions zero through
three and an isolated position four. -/
theorem r5Branch19_edgeVector :
    edgeVectorOfCode (r5NeighborhoodRepresentativeCode 19) =
      ![true, true, true, false, true,
        true, false, true, false, false] := by
  decide

set_option linter.flexible false in
/-- The exact internal adjacency relation of neighborhood branch 19. -/
theorem r5Branch19_neighborAdjacency
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (horbit : ∀ left right : Fin 5,
      decide (G.Adj (r5NeighborVertex left)
        (r5NeighborVertex right)) =
      r5FiveVertexAdjacency
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode 19))
        left right)
    (left right : Fin 5) :
    G.Adj (r5NeighborVertex left) (r5NeighborVertex right) ↔
      left ≠ 4 ∧ right ≠ 4 ∧ left ≠ right := by
  have h := horbit left right
  clear horbit
  rw [r5Branch19_edgeVector] at h
  fin_cases left <;> fin_cases right <;>
    simp [r5NeighborVertex, r5FiveVertexAdjacency] at h ⊢ <;>
    assumption

/-- Pure finite description of the neighbors below label six of a branch-19
neighborhood vertex. -/
def r5Branch19InitialNeighbors (index : Fin 5) :
    Finset (Fin 26) :=
  Finset.univ.filter fun vertex =>
    vertex = 0 ∨
      ∃ right : Fin 5,
        vertex = r5NeighborVertex right ∧
        index ≠ 4 ∧ right ≠ 4 ∧ index ≠ right

theorem card_r5Branch19InitialNeighbors (index : Fin 5) :
    #(r5Branch19InitialNeighbors index) =
      if index = 4 then 1 else 4 := by
  fin_cases index <;> decide

theorem r5Branch19_adj_initial_iff
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (horbit : ∀ left right : Fin 5,
      decide (G.Adj (r5NeighborVertex left)
        (r5NeighborVertex right)) =
      r5FiveVertexAdjacency
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode 19))
        left right)
    (index : Fin 5) (vertex : Fin 26) (hvertex : vertex < 6) :
    G.Adj (r5NeighborVertex index) vertex ↔
      vertex = 0 ∨
        ∃ right : Fin 5,
          vertex = r5NeighborVertex right ∧
          index ≠ 4 ∧ right ≠ 4 ∧ index ≠ right := by
  have hclass :
      vertex = 0 ∨
        ∃ right : Fin 5, vertex = r5NeighborVertex right := by
    by_cases hzero : vertex = 0
    · exact Or.inl hzero
    · have hpositive : 1 ≤ (vertex : Nat) := by omega
      let right : Fin 5 :=
        ⟨(vertex : Nat) - 1, by omega⟩
      refine Or.inr ⟨right, ?_⟩
      apply Fin.ext
      simp [right, r5NeighborVertex]
      omega
  constructor
  · intro hadj
    rcases hclass with rfl | ⟨right, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨right, rfl,
        (r5Branch19_neighborAdjacency G horbit index right).mp hadj⟩
  · rintro (rfl | ⟨right, rfl, hrelation⟩)
    · rw [G.adj_comm, ← SimpleGraph.mem_neighborFinset, hneighbor]
      fin_cases index <;> decide
    · exact (r5Branch19_neighborAdjacency
        G horbit index right).mpr hrelation

theorem r5Branch19_initialNeighborFinset
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (horbit : ∀ left right : Fin 5,
      decide (G.Adj (r5NeighborVertex left)
        (r5NeighborVertex right)) =
      r5FiveVertexAdjacency
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode 19))
        left right)
    (index : Fin 5) :
    (G.neighborFinset (r5NeighborVertex index)).filter
        (fun vertex => vertex < 6) =
      r5Branch19InitialNeighbors index := by
  ext vertex
  by_cases hvertex : vertex < 6
  · simp only [mem_filter, hvertex, and_true,
      r5Branch19InitialNeighbors, mem_univ, true_and]
    rw [SimpleGraph.mem_neighborFinset,
      r5Branch19_adj_initial_iff
        G hneighbor horbit index vertex hvertex]
  · simp only [mem_filter, hvertex, and_false,
      r5Branch19InitialNeighbors, mem_univ, true_and, false_iff]
    rintro (rfl | ⟨right, rfl, -⟩)
    · exact hvertex (by omega)
    · apply hvertex
      change (right : Nat) + 1 < 6
      omega

theorem r5ExteriorNeighbors_eq_filter_not_lt_six
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (vertex : Fin 26) :
    r5ExteriorNeighbors G vertex =
      (G.neighborFinset vertex).filter
        (fun exterior => ¬exterior < 6) := by
  ext exterior
  simp only [r5ExteriorNeighbors, mem_inter,
    SimpleGraph.mem_neighborFinset, mem_r5ExteriorVertices_iff,
    mem_filter]
  constructor
  · rintro ⟨hadj, hge⟩
    exact ⟨hadj, by omega⟩
  · rintro ⟨hadj, hnotLT⟩
    exact ⟨hadj, by omega⟩

/-- Branch 19 has one exterior stub at each of the first four neighbors and
four exterior stubs at the isolated fifth neighbor. -/
theorem card_r5Branch19ExteriorNeighbors
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (horbit : ∀ left right : Fin 5,
      decide (G.Adj (r5NeighborVertex left)
        (r5NeighborVertex right)) =
      r5FiveVertexAdjacency
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode 19))
        left right)
    (index : Fin 5) :
    #(r5ExteriorNeighbors G (r5NeighborVertex index)) =
      if index = 4 then 4 else 1 := by
  have hpartition :=
    Finset.card_filter_add_card_filter_not
      (s := G.neighborFinset (r5NeighborVertex index))
      (fun vertex : Fin 26 => vertex < 6)
  rw [r5Branch19_initialNeighborFinset
      G hneighbor horbit index,
    card_r5Branch19InitialNeighbors,
    ← r5ExteriorNeighbors_eq_filter_not_lt_six,
    G.card_neighborFinset_eq_degree, hregular] at hpartition
  by_cases hindex : index = 4
  · subst index
    simp at hpartition ⊢
    omega
  · simp [hindex] at hpartition ⊢
    omega

/-- An enumeration of the eight exterior stubs forced by branch 19. -/
structure R5Branch19StubEnumeration
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] where
  first : Fin 4 → Fin 26
  fifth : Fin 4 → Fin 26
  fifth_injective : Function.Injective fifth
  first_mem : ∀ index,
    first index ∈
      r5ExteriorNeighbors G (r5NeighborVertex index.castSucc)
  first_unique : ∀ index vertex,
    vertex ∈
        r5ExteriorNeighbors G (r5NeighborVertex index.castSucc) →
      vertex = first index
  fifth_mem : ∀ index,
    fifth index ∈ r5ExteriorNeighbors G (r5NeighborVertex 4)
  fifth_surjective : ∀ vertex,
    vertex ∈ r5ExteriorNeighbors G (r5NeighborVertex 4) →
      ∃ index, fifth index = vertex

/-- Choose the unique four `K₄` stubs and enumerate the four isolated-vertex
stubs.  The choices are made through finite equivalences, so their advertised
membership, uniqueness, and injectivity are kernel checked. -/
theorem exists_r5Branch19StubEnumeration
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (horbit : ∀ left right : Fin 5,
      decide (G.Adj (r5NeighborVertex left)
        (r5NeighborVertex right)) =
      r5FiveVertexAdjacency
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode 19))
        left right) :
    Nonempty (R5Branch19StubEnumeration G) := by
  classical
  have hfirstCard (index : Fin 4) :
      #(r5ExteriorNeighbors G
          (r5NeighborVertex index.castSucc)) = 1 := by
    have hindex : index.castSucc ≠ (4 : Fin 5) := by
      simpa using index.castSucc_lt_last.ne
    rw [card_r5Branch19ExteriorNeighbors
      G hregular hneighbor horbit index.castSucc]
    simp [hindex]
  have hfifthCard :
      #(r5ExteriorNeighbors G (r5NeighborVertex 4)) = 4 := by
    simpa using card_r5Branch19ExteriorNeighbors
      G hregular hneighbor horbit 4
  let first (index : Fin 4) : Fin 26 :=
    ((r5ExteriorNeighbors G
        (r5NeighborVertex index.castSucc)).equivFinOfCardEq
          (hfirstCard index)).symm 0
  let fifth (index : Fin 4) : Fin 26 :=
    ((r5ExteriorNeighbors G
        (r5NeighborVertex 4)).equivFinOfCardEq
          hfifthCard).symm index
  have hfirstMem (index : Fin 4) :
      first index ∈
        r5ExteriorNeighbors G
          (r5NeighborVertex index.castSucc) := by
    exact ((r5ExteriorNeighbors G
      (r5NeighborVertex index.castSucc)).equivFinOfCardEq
        (hfirstCard index)).symm 0 |>.property
  have hfirstUnique (index : Fin 4) (vertex : Fin 26)
      (hvertex : vertex ∈
        r5ExteriorNeighbors G
          (r5NeighborVertex index.castSucc)) :
      vertex = first index := by
    let equivalence :=
      (r5ExteriorNeighbors G
        (r5NeighborVertex index.castSucc)).equivFinOfCardEq
          (hfirstCard index)
    have himage :
        equivalence ⟨vertex, hvertex⟩ = (0 : Fin 1) :=
      Subsingleton.elim _ _
    have hsubtype :
        (⟨vertex, hvertex⟩ :
          {value // value ∈
            r5ExteriorNeighbors G
              (r5NeighborVertex index.castSucc)}) =
          equivalence.symm 0 := by
      apply equivalence.injective
      simpa using himage
    exact congrArg Subtype.val hsubtype
  have hfifthMem (index : Fin 4) :
      fifth index ∈
        r5ExteriorNeighbors G (r5NeighborVertex 4) := by
    exact ((r5ExteriorNeighbors G
      (r5NeighborVertex 4)).equivFinOfCardEq
        hfifthCard).symm index |>.property
  have hfifthInjective : Function.Injective fifth := by
    intro left right heq
    let equivalence :=
      (r5ExteriorNeighbors G
        (r5NeighborVertex 4)).equivFinOfCardEq hfifthCard
    apply equivalence.symm.injective
    apply Subtype.ext
    exact heq
  have hfifthSurjective (vertex : Fin 26)
      (hvertex : vertex ∈
        r5ExteriorNeighbors G (r5NeighborVertex 4)) :
      ∃ index, fifth index = vertex := by
    let equivalence :=
      (r5ExteriorNeighbors G
        (r5NeighborVertex 4)).equivFinOfCardEq hfifthCard
    refine ⟨equivalence ⟨vertex, hvertex⟩, ?_⟩
    exact congrArg Subtype.val
      (equivalence.symm_apply_apply ⟨vertex, hvertex⟩)
  exact ⟨{
    first := first
    fifth := fifth
    fifth_injective := hfifthInjective
    first_mem := hfirstMem
    first_unique := hfirstUnique
    fifth_mem := hfifthMem
    fifth_surjective := hfifthSurjective
  }⟩

/-- The classifier's eight-endpoint function attached to a stub
enumeration. -/
def R5Branch19StubEnumeration.endpoints
    {G : SimpleGraph (Fin 26)} [DecidableRel G.Adj]
    (enumeration : R5Branch19StubEnumeration G) :
    Fin 8 → Fin 26 :=
  ![enumeration.first 0, enumeration.first 1,
    enumeration.first 2, enumeration.first 3,
    enumeration.fifth 0, enumeration.fifth 1,
    enumeration.fifth 2, enumeration.fifth 3]

theorem R5Branch19StubEnumeration.endpoints_fifth_distinct
    {G : SimpleGraph (Fin 26)} [DecidableRel G.Adj]
    (enumeration : R5Branch19StubEnumeration G) :
    R5FifthStubDistinct enumeration.endpoints := by
  have hinjective := enumeration.fifth_injective
  constructor
  · change enumeration.fifth 0 ≠ enumeration.fifth 1
    intro h
    have hindices := hinjective h
    have := congrArg Fin.val hindices
    omega
  constructor
  · change enumeration.fifth 0 ≠ enumeration.fifth 2
    intro h
    have hindices := hinjective h
    have := congrArg Fin.val hindices
    omega
  constructor
  · change enumeration.fifth 0 ≠ enumeration.fifth 3
    intro h
    have hindices := hinjective h
    have := congrArg Fin.val hindices
    omega
  constructor
  · change enumeration.fifth 1 ≠ enumeration.fifth 2
    intro h
    have hindices := hinjective h
    have := congrArg Fin.val hindices
    omega
  constructor
  · change enumeration.fifth 1 ≠ enumeration.fifth 3
    intro h
    have hindices := hinjective h
    have := congrArg Fin.val hindices
    omega
  · change enumeration.fifth 2 ≠ enumeration.fifth 3
    intro h
    have hindices := hinjective h
    have := congrArg Fin.val hindices
    omega

theorem R5Branch19StubEnumeration.first_adj_iff
    {G : SimpleGraph (Fin 26)} [DecidableRel G.Adj]
    (enumeration : R5Branch19StubEnumeration G)
    (index : Fin 4) (exterior : Fin 26)
    (hexterior : 6 ≤ exterior) :
    G.Adj (r5NeighborVertex index.castSucc) exterior ↔
      enumeration.first index = exterior := by
  constructor
  · intro hadj
    exact (enumeration.first_unique index exterior
      (by
        rw [r5ExteriorNeighbors, mem_inter,
          SimpleGraph.mem_neighborFinset,
          mem_r5ExteriorVertices_iff]
        exact ⟨hadj, hexterior⟩)).symm
  · intro heq
    rw [← heq, ← SimpleGraph.mem_neighborFinset]
    exact (mem_inter.mp (enumeration.first_mem index)).1

theorem R5Branch19StubEnumeration.fifth_adj_iff
    {G : SimpleGraph (Fin 26)} [DecidableRel G.Adj]
    (enumeration : R5Branch19StubEnumeration G)
    (exterior : Fin 26) (hexterior : 6 ≤ exterior) :
    G.Adj (r5NeighborVertex 4) exterior ↔
      ∃ index : Fin 4, enumeration.fifth index = exterior := by
  constructor
  · intro hadj
    apply enumeration.fifth_surjective exterior
    rw [r5ExteriorNeighbors, mem_inter,
      SimpleGraph.mem_neighborFinset,
      mem_r5ExteriorVertices_iff]
    exact ⟨hadj, hexterior⟩
  · rintro ⟨index, rfl⟩
    rw [← SimpleGraph.mem_neighborFinset]
    exact (mem_inter.mp (enumeration.fifth_mem index)).1

theorem R5Branch19StubEnumeration.fifth_indicator_sum
    {G : SimpleGraph (Fin 26)} [DecidableRel G.Adj]
    (enumeration : R5Branch19StubEnumeration G)
    (vertex : Fin 26) :
    (if ∃ index : Fin 4, enumeration.fifth index = vertex
      then 1 else 0) =
      ∑ index : Fin 4,
        if enumeration.fifth index = vertex then 1 else 0 := by
  by_cases hexists :
      ∃ index : Fin 4, enumeration.fifth index = vertex
  · obtain ⟨selected, hselected⟩ := hexists
    have hiff (index : Fin 4) :
        enumeration.fifth index = vertex ↔ index = selected := by
      constructor
      · intro hindex
        apply enumeration.fifth_injective
        exact hindex.trans hselected.symm
      · rintro rfl
        exact hselected
    rw [if_pos ⟨selected, hselected⟩]
    simp_rw [hiff]
    simp
  · have hnone (index : Fin 4) :
        enumeration.fifth index ≠ vertex := by
      exact fun hindex => hexists ⟨index, hindex⟩
    rw [if_neg hexists]
    simp [hnone]

/-- Relabel the four `K₄` columns by the inverse of the classifier's column
map, while fixing the isolated fifth neighbor. -/
def r5Branch19NeighborPermutation
    (permutation : Fin 24) : Equiv.Perm (Fin 5) where
  toFun column :=
    if hcolumn : (column : Nat) < 4 then
      (r5CrossColumnInverseMap permutation
        ⟨column, hcolumn⟩).castSucc
    else
      4
  invFun column :=
    if hcolumn : (column : Nat) < 4 then
      (r5CrossColumnMap permutation
        ⟨column, hcolumn⟩).castSucc
    else
      4
  left_inv column := by
    fin_cases permutation <;> fin_cases column <;> decide
  right_inv column := by
    fin_cases permutation <;> fin_cases column <;> decide

@[simp]
theorem r5Branch19NeighborPermutation_apply_column
    (permutation : Fin 24) (column : Fin 4) :
    r5Branch19NeighborPermutation permutation column.castSucc =
      (r5CrossColumnInverseMap permutation column).castSucc := by
  simp [r5Branch19NeighborPermutation]

@[simp]
theorem r5Branch19NeighborPermutation_apply_fifth
    (permutation : Fin 24) :
    r5Branch19NeighborPermutation permutation 4 = 4 := by
  simp [r5Branch19NeighborPermutation]

noncomputable def r5Branch19ColumnRelabeling
    (permutation : Fin 24) : Equiv.Perm (Fin 26) :=
  r5NeighborRelabelPerm
    (r5Branch19NeighborPermutation permutation)

@[simp]
theorem r5Branch19ColumnRelabeling_apply_neighbor
    (permutation : Fin 24) (index : Fin 5) :
    r5Branch19ColumnRelabeling permutation
        (r5NeighborVertex index) =
      r5NeighborVertex
        (r5Branch19NeighborPermutation permutation index) := by
  change r5NeighborRelabelPerm
      (r5Branch19NeighborPermutation permutation)
        ⟨(index : Nat) + 1, by omega⟩ =
    ⟨(r5Branch19NeighborPermutation permutation index : Nat) + 1,
      by omega⟩
  exact r5NeighborRelabelPerm_apply_neighbor
    (r5Branch19NeighborPermutation permutation) index

@[simp]
theorem r5Branch19ColumnRelabeling_apply_exterior
    (permutation : Fin 24) (vertex : Fin 26)
    (hvertex : 6 ≤ vertex) :
    r5Branch19ColumnRelabeling permutation vertex = vertex :=
  r5NeighborRelabelPerm_apply_exterior _ vertex hvertex

theorem R5Branch19StubEnumeration.columnRelabel_first_adj_iff
    {G : SimpleGraph (Fin 26)} [DecidableRel G.Adj]
    (enumeration : R5Branch19StubEnumeration G)
    (permutation : Fin 24) (column : Fin 4)
    (exterior : Fin 26) (hexterior : 6 ≤ exterior) :
    (relabelGraph G
        (r5Branch19ColumnRelabeling permutation)).Adj
        (r5NeighborVertex column.castSucc) exterior ↔
      enumeration.first
        (r5CrossColumnInverseMap permutation column) = exterior := by
  rw [relabelGraph_adj_iff,
    r5Branch19ColumnRelabeling_apply_exterior
      permutation exterior hexterior]
  change G.Adj
    (r5Branch19ColumnRelabeling permutation
      ⟨(column : Nat) + 1, by omega⟩) exterior ↔ _
  rw [show r5Branch19ColumnRelabeling permutation
        ⟨(column : Nat) + 1, by omega⟩ =
      r5NeighborVertex
        (r5CrossColumnInverseMap permutation column).castSucc by
    change r5Branch19ColumnRelabeling permutation
      (r5NeighborVertex column.castSucc) =
        r5NeighborVertex
          (r5CrossColumnInverseMap permutation column).castSucc
    rw [r5Branch19ColumnRelabeling_apply_neighbor,
      r5Branch19NeighborPermutation_apply_column]]
  exact enumeration.first_adj_iff _ exterior hexterior

theorem R5Branch19StubEnumeration.columnRelabel_fifth_adj_iff
    {G : SimpleGraph (Fin 26)} [DecidableRel G.Adj]
    (enumeration : R5Branch19StubEnumeration G)
    (permutation : Fin 24)
    (exterior : Fin 26) (hexterior : 6 ≤ exterior) :
    (relabelGraph G
        (r5Branch19ColumnRelabeling permutation)).Adj
        (r5NeighborVertex 4) exterior ↔
      ∃ index : Fin 4, enumeration.fifth index = exterior := by
  rw [relabelGraph_adj_iff,
    r5Branch19ColumnRelabeling_apply_exterior
      permutation exterior hexterior]
  change G.Adj
    (r5Branch19ColumnRelabeling permutation 5) exterior ↔ _
  rw [show r5Branch19ColumnRelabeling permutation 5 = 5 by
    change r5Branch19ColumnRelabeling permutation
      (r5NeighborVertex 4) = r5NeighborVertex 4
    rw [r5Branch19ColumnRelabeling_apply_neighbor,
      r5Branch19NeighborPermutation_apply_fifth]]
  exact enumeration.fifth_adj_iff exterior hexterior

theorem r5Branch19ColumnRelabel_neighborFinset
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (permutation : Fin 24) :
    (relabelGraph G
      (r5Branch19ColumnRelabeling permutation)).neighborFinset 0 =
        r5FixedNeighbors := by
  let relabeling := r5Branch19ColumnRelabeling permutation
  have himageFixed (vertex : Fin 26)
      (hvertex : vertex ∈ r5FixedNeighbors) :
      relabeling vertex ∈ r5FixedNeighbors := by
    let index :=
      r5FixedNeighborLabelEquiv.symm ⟨vertex, hvertex⟩
    have hvertexEq :
        vertex = r5NeighborVertex index := by
      exact (congrArg Subtype.val
        (r5FixedNeighborLabelEquiv.apply_symm_apply
          ⟨vertex, hvertex⟩)).symm
    rw [hvertexEq]
    change r5NeighborRelabelPerm
      (r5Branch19NeighborPermutation permutation)
        (r5NeighborVertex index) ∈ r5FixedNeighbors
    rw [show r5NeighborRelabelPerm
        (r5Branch19NeighborPermutation permutation)
          (r5NeighborVertex index) =
        r5NeighborVertex
          (r5Branch19NeighborPermutation permutation index) by
      simp [r5NeighborVertex]]
    exact
      (r5FixedNeighborLabelEquiv
        (r5Branch19NeighborPermutation permutation index)).property
  have hsubset :
      r5FixedNeighbors ⊆
        (relabelGraph G relabeling).neighborFinset 0 := by
    intro vertex hvertex
    rw [SimpleGraph.mem_neighborFinset, relabelGraph_adj_iff]
    change G.Adj
      (r5NeighborRelabelPerm
        (r5Branch19NeighborPermutation permutation) 0)
      (relabeling vertex)
    rw [r5NeighborRelabelPerm_zero,
      ← SimpleGraph.mem_neighborFinset, hneighbor]
    exact himageFixed vertex hvertex
  have hdegree :
      (relabelGraph G relabeling).degree 0 = 5 := by
    rw [relabelGraph_degree]
    change G.degree
      (r5NeighborRelabelPerm
        (r5Branch19NeighborPermutation permutation) 0) = 5
    rw [r5NeighborRelabelPerm_zero, hregular]
  have hcard :
      #((relabelGraph G relabeling).neighborFinset 0) ≤
        #r5FixedNeighbors := by
    simp [hdegree]
  exact (Finset.eq_of_subset_of_card_le hsubset hcard).symm

theorem r5Branch19ColumnRelabel_orbit
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (horbit : ∀ left right : Fin 5,
      decide (G.Adj (r5NeighborVertex left)
        (r5NeighborVertex right)) =
      r5FiveVertexAdjacency
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode 19))
        left right)
    (permutation : Fin 24) :
    ∀ left right : Fin 5,
      decide ((relabelGraph G
        (r5Branch19ColumnRelabeling permutation)).Adj
          (r5NeighborVertex left) (r5NeighborVertex right)) =
      r5FiveVertexAdjacency
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode 19))
        left right := by
  have hrelation (left right : Fin 5) :
      (relabelGraph G
        (r5Branch19ColumnRelabeling permutation)).Adj
          (r5NeighborVertex left) (r5NeighborVertex right) ↔
        left ≠ 4 ∧ right ≠ 4 ∧ left ≠ right := by
    change G.Adj
      (r5Branch19ColumnRelabeling permutation
        (r5NeighborVertex left))
      (r5Branch19ColumnRelabeling permutation
        (r5NeighborVertex right)) ↔ _
    rw [show r5Branch19ColumnRelabeling permutation
          (r5NeighborVertex left) =
        r5NeighborVertex
          (r5Branch19NeighborPermutation permutation left) by
      simp [r5Branch19ColumnRelabeling, r5NeighborVertex],
      show r5Branch19ColumnRelabeling permutation
          (r5NeighborVertex right) =
        r5NeighborVertex
          (r5Branch19NeighborPermutation permutation right) by
      simp [r5Branch19ColumnRelabeling, r5NeighborVertex],
      r5Branch19_neighborAdjacency G horbit]
    constructor
    · rintro ⟨hleft, hright, hne⟩
      refine ⟨?_, ?_, ?_⟩
      · intro heq
        apply hleft
        rw [heq]
        exact r5Branch19NeighborPermutation_apply_fifth permutation
      · intro heq
        apply hright
        rw [heq]
        exact r5Branch19NeighborPermutation_apply_fifth permutation
      · exact fun heq =>
          hne (congrArg
            (r5Branch19NeighborPermutation permutation) heq)
    · rintro ⟨hleft, hright, hne⟩
      refine ⟨?_, ?_, ?_⟩
      · intro heq
        apply hleft
        apply (r5Branch19NeighborPermutation permutation).injective
        simpa using heq
      · intro heq
        apply hright
        apply (r5Branch19NeighborPermutation permutation).injective
        simpa using heq
      · exact fun heq =>
          hne ((r5Branch19NeighborPermutation permutation).injective heq)
  intro left right
  have h := hrelation left right
  clear hrelation horbit
  fin_cases left <;> fin_cases right <;>
    simp [r5FiveVertexAdjacency, r5Branch19_edgeVector] at h ⊢
  all_goals simp_all

theorem r5ExteriorPatternCode_eq_sum
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (exterior : Fin 26) :
    r5ExteriorPatternCode G exterior =
      ∑ position : Fin 5,
        if G.Adj (r5NeighborVertex position) exterior
          then 2 ^ (4 - (position : Nat)) else 0 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ]
  simp [r5ExteriorPatternCode, r5ExteriorPatternBit,
    r5NeighborVertex, Nat.add_assoc]

theorem R5Branch19StubEnumeration.endpointPattern_eq
    {G : SimpleGraph (Fin 26)} [DecidableRel G.Adj]
    (enumeration : R5Branch19StubEnumeration G)
    (permutation : Fin 24) (vertex : Fin 26) :
    r5EndpointPattern enumeration.endpoints permutation vertex =
      (∑ index : Fin 4,
        if enumeration.first index = vertex then
          2 ^ (4 -
            (r5CrossColumnMap permutation index : Nat))
        else 0) +
      ∑ index : Fin 4,
        if enumeration.fifth index = vertex then 1 else 0 := by
  simp [r5EndpointPattern, r5StubMask,
    R5Branch19StubEnumeration.endpoints,
    Fin.sum_univ_succ, Finset.filter_singleton,
    Nat.add_assoc]
  all_goals rfl

/-- After applying the classifier's inverse column permutation, its endpoint
pattern is exactly the graph's five-bit exterior-row code. -/
theorem R5Branch19StubEnumeration.exteriorPatternCode_columnRelabel
    {G : SimpleGraph (Fin 26)} [DecidableRel G.Adj]
    (enumeration : R5Branch19StubEnumeration G)
    (permutation : Fin 24) (exterior : Fin 26)
    (hexterior : 6 ≤ exterior) :
    r5ExteriorPatternCode
        (relabelGraph G
          (r5Branch19ColumnRelabeling permutation))
        exterior =
      r5EndpointPattern enumeration.endpoints
        permutation exterior := by
  have hfirst (column : Fin 4) :
      (relabelGraph G
        (r5Branch19ColumnRelabeling permutation)).Adj
          (r5NeighborVertex column.castSucc) exterior ↔
        enumeration.first
          (r5CrossColumnInverseMap permutation column) = exterior := by
    exact enumeration.columnRelabel_first_adj_iff
      permutation column exterior hexterior
  have hlast :
      (relabelGraph G
        (r5Branch19ColumnRelabeling permutation)).Adj
          (r5NeighborVertex (Fin.last 4)) exterior ↔
        ∃ index : Fin 4,
          enumeration.fifth index = exterior := by
    simpa using enumeration.columnRelabel_fifth_adj_iff
      permutation exterior hexterior
  rw [r5ExteriorPatternCode_eq_sum,
    enumeration.endpointPattern_eq]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, Nat.reduceSub, pow_zero]
  simp_rw [hfirst]
  simp only [hlast]
  rw [enumeration.fifth_indicator_sum, add_right_cancel_iff]
  symm
  have hleft (index : Fin 4) :
      r5CrossColumnInverseMap permutation
          (r5CrossColumnMap permutation index) =
        index := by
    exact (r5CrossColumnPermutation permutation).left_inv index
  calc
    (∑ index : Fin 4,
        if enumeration.first index = exterior then
          2 ^ (4 -
            (r5CrossColumnMap permutation index : Nat))
        else 0) =
        ∑ index : Fin 4,
          if enumeration.first
              (r5CrossColumnInverseMap permutation
                (r5CrossColumnMap permutation index)) = exterior
          then 2 ^ (4 -
            (r5CrossColumnMap permutation index : Nat))
          else 0 := by
      apply Fintype.sum_congr
      intro index
      rw [hleft]
    _ = ∑ column : Fin 4,
          if enumeration.first
              (r5CrossColumnInverseMap permutation column) = exterior
          then 2 ^ (4 - (column : Nat))
          else 0 := by
      exact Equiv.sum_comp (r5CrossColumnPermutation permutation)
        (fun column : Fin 4 =>
          if enumeration.first
              (r5CrossColumnInverseMap permutation column) = exterior
          then 2 ^ (4 - (column : Nat))
          else 0)

theorem R5Branch19StubEnumeration.endpoint_mem_exterior
    {G : SimpleGraph (Fin 26)} [DecidableRel G.Adj]
    (enumeration : R5Branch19StubEnumeration G)
    (stub : Fin 8) :
    enumeration.endpoints stub ∈ r5ExteriorVertices := by
  fin_cases stub
  · simpa [R5Branch19StubEnumeration.endpoints] using
      (mem_inter.mp (enumeration.first_mem 0)).2
  · simpa [R5Branch19StubEnumeration.endpoints] using
      (mem_inter.mp (enumeration.first_mem 1)).2
  · simpa [R5Branch19StubEnumeration.endpoints] using
      (mem_inter.mp (enumeration.first_mem 2)).2
  · simpa [R5Branch19StubEnumeration.endpoints] using
      (mem_inter.mp (enumeration.first_mem 3)).2
  · simpa [R5Branch19StubEnumeration.endpoints] using
      (mem_inter.mp (enumeration.fifth_mem 0)).2
  · simpa [R5Branch19StubEnumeration.endpoints] using
      (mem_inter.mp (enumeration.fifth_mem 1)).2
  · simpa [R5Branch19StubEnumeration.endpoints] using
      (mem_inter.mp (enumeration.fifth_mem 2)).2
  · simpa [R5Branch19StubEnumeration.endpoints] using
      (mem_inter.mp (enumeration.fifth_mem 3)).2

def r5ExteriorPatternCodeMultiset
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] :
    Multiset Nat :=
  r5ExteriorVertices.val.map fun vertex : Fin 26 =>
    r5ExteriorPatternCode G vertex

theorem r5ExteriorVertices_tuple_multiset :
    (List.ofFn (fun index : Fin 20 =>
      (⟨(index : Nat) + 6, by omega⟩ : Fin 26)) :
        Multiset (Fin 26)) =
      r5ExteriorVertices.val := by
  decide

theorem r5ExteriorPatternCodeMultiset_eq_tuple
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] :
    r5ExteriorPatternCodeMultiset G =
      (List.ofFn (fun index : Fin 20 =>
        r5ExteriorPatternCode G ((index : Nat) + 6)) :
          Multiset Nat) := by
  have hmap := congrArg
    (Multiset.map fun vertex : Fin 26 =>
      r5ExteriorPatternCode G vertex)
    r5ExteriorVertices_tuple_multiset
  simpa [r5ExteriorPatternCodeMultiset, List.map_ofFn] using hmap.symm

theorem multiset_map_eq_map_of_eq_on
    {α β : Type} (values : Multiset α) (left right : α → β)
    (hpoint : ∀ value ∈ values, left value = right value) :
    values.map left = values.map right :=
  Multiset.map_congr rfl hpoint

set_option maxHeartbeats 400000 in
-- The finite endpoint-multiset normalization expands all twenty rows.
set_option maxRecDepth 10000 in
/-- The classifier's endpoint multiset determines all twenty exterior rows:
rows outside the endpoint image have code zero. -/
theorem R5Branch19StubEnumeration.exteriorPatternCodeMultiset_columnRelabel
    {G : SimpleGraph (Fin 26)} [DecidableRel G.Adj]
    (enumeration : R5Branch19StubEnumeration G)
    (child : Fin 20) (permutation : Fin 24)
    (hpattern :
      r5EndpointPatternMultiset enumeration.endpoints permutation =
        (r5CrossPatternRepresentative child : Multiset Nat)) :
    r5ExteriorPatternCodeMultiset
        (relabelGraph G
          (r5Branch19ColumnRelabeling permutation)) =
      Multiset.replicate
        (20 - (r5CrossPatternRepresentative child).length) 0 +
      (r5CrossPatternRepresentative child : Multiset Nat) := by
  classical
  let H :=
    relabelGraph G (r5Branch19ColumnRelabeling permutation)
  let endpointSet : Finset (Fin 26) :=
    Finset.univ.image enumeration.endpoints
  let zeroSet : Finset (Fin 26) :=
    r5ExteriorVertices \ endpointSet
  have hendpointSubset :
      endpointSet ⊆ r5ExteriorVertices := by
    intro vertex hvertex
    change vertex ∈
      Finset.univ.image enumeration.endpoints at hvertex
    rw [mem_image] at hvertex
    obtain ⟨stub, -, rfl⟩ := hvertex
    exact enumeration.endpoint_mem_exterior stub
  have hendpointPattern :
      endpointSet.val.map
          (r5EndpointPattern enumeration.endpoints permutation) =
        (r5CrossPatternRepresentative child : Multiset Nat) := by
    change r5EndpointPatternMultiset
        enumeration.endpoints permutation =
      (r5CrossPatternRepresentative child : Multiset Nat)
    exact hpattern
  have hendpointMap :
      endpointSet.val.map
          (fun vertex : Fin 26 => r5ExteriorPatternCode H vertex) =
        (r5CrossPatternRepresentative child : Multiset Nat) := by
    have hendpointPoint
        (vertex : Fin 26) (hvertex : vertex ∈ endpointSet.val) :
        r5ExteriorPatternCode H vertex =
          r5EndpointPattern enumeration.endpoints
            permutation vertex := by
      have hmem : vertex ∈ endpointSet := hvertex
      have hexterior :
          6 ≤ vertex :=
        (mem_r5ExteriorVertices_iff vertex).mp
          (hendpointSubset hmem)
      change r5ExteriorPatternCode
          (relabelGraph G
            (r5Branch19ColumnRelabeling permutation)) vertex =
        r5EndpointPattern enumeration.endpoints permutation vertex
      exact enumeration.exteriorPatternCode_columnRelabel
        permutation vertex hexterior
    have hcodeMap :
      endpointSet.val.map
          (fun vertex : Fin 26 => r5ExteriorPatternCode H vertex) =
        endpointSet.val.map
          (r5EndpointPattern enumeration.endpoints permutation) :=
      multiset_map_eq_map_of_eq_on endpointSet.val
        (fun vertex : Fin 26 => r5ExteriorPatternCode H vertex)
        (r5EndpointPattern enumeration.endpoints permutation)
        hendpointPoint
    rw [hcodeMap]
    exact hendpointPattern
  have hendpointCard :
      #endpointSet =
        (r5CrossPatternRepresentative child).length := by
    have hcard := congrArg Multiset.card hendpointPattern
    simpa only [Multiset.card_map, Finset.card_def,
      Multiset.coe_card] using hcard
  have hzeroCode (vertex : Fin 26) (hvertex : vertex ∈ zeroSet) :
      r5ExteriorPatternCode H vertex = 0 := by
    have hexteriorMem : vertex ∈ r5ExteriorVertices :=
      (mem_sdiff.mp hvertex).1
    have hnotEndpoint : vertex ∉ endpointSet :=
      (mem_sdiff.mp hvertex).2
    rw [enumeration.exteriorPatternCode_columnRelabel
      permutation vertex
        ((mem_r5ExteriorVertices_iff vertex).mp hexteriorMem)]
    apply Finset.sum_eq_zero
    intro stub _
    rw [if_neg]
    intro heq
    apply hnotEndpoint
    change vertex ∈
      Finset.univ.image enumeration.endpoints
    rw [mem_image]
    exact ⟨stub, mem_univ stub, heq⟩
  have hzeroMap :
      zeroSet.val.map
          (fun vertex : Fin 26 => r5ExteriorPatternCode H vertex) =
        Multiset.replicate #zeroSet 0 := by
    calc
      zeroSet.val.map
          (fun vertex : Fin 26 => r5ExteriorPatternCode H vertex) =
          zeroSet.val.map (fun _ : Fin 26 => 0) := by
        exact multiset_map_eq_map_of_eq_on zeroSet.val
          (fun vertex : Fin 26 => r5ExteriorPatternCode H vertex)
          (fun _ : Fin 26 => 0)
          hzeroCode
      _ = Multiset.replicate #zeroSet 0 := by
        simp
  have hzeroCard :
      #zeroSet =
        20 - (r5CrossPatternRepresentative child).length := by
    change #(r5ExteriorVertices \ endpointSet) =
      20 - (r5CrossPatternRepresentative child).length
    rw [card_sdiff_of_subset hendpointSubset,
      card_r5ExteriorVertices, hendpointCard]
  have hunion :
      endpointSet ∪ zeroSet = r5ExteriorVertices := by
    exact union_sdiff_of_subset hendpointSubset
  have hdisjoint : Disjoint endpointSet zeroSet := by
    change Disjoint endpointSet
      (r5ExteriorVertices \ endpointSet)
    exact disjoint_sdiff_self_right
  have hval :
      r5ExteriorVertices.val =
        endpointSet.val + zeroSet.val := by
    rw [← hunion, Finset.union_val]
    symm
    apply (Multiset.add_eq_union_iff_disjoint).2
    simpa using hdisjoint
  rw [r5ExteriorPatternCodeMultiset, hval,
    Multiset.map_add, hendpointMap, hzeroMap, hzeroCard,
    add_comm]

/-- Sorting the twenty exterior labels turns the orbit multiset into the exact
pointwise row assignment used by the E042 child. -/
theorem R5Branch19StubEnumeration.exists_sortedCrossPattern
    {G : SimpleGraph (Fin 26)} [DecidableRel G.Adj]
    (enumeration : R5Branch19StubEnumeration G)
    (child : Fin 20) (permutation : Fin 24)
    (hpattern :
      r5EndpointPatternMultiset enumeration.endpoints permutation =
        (r5CrossPatternRepresentative child : Multiset Nat)) :
    let columnGraph :=
      relabelGraph G (r5Branch19ColumnRelabeling permutation)
    let sortedGraph :=
      relabelGraph columnGraph (r5SortExteriorPerm columnGraph)
    ∀ index : Fin 20,
      r5ExteriorPatternCode sortedGraph ((index : Nat) + 6) =
        r5CrossPatternSortedCode child index := by
  let columnGraph :=
    relabelGraph G (r5Branch19ColumnRelabeling permutation)
  let sortedGraph :=
    relabelGraph columnGraph (r5SortExteriorPerm columnGraph)
  let before : Fin 20 → Nat :=
    fun index =>
      r5ExteriorPatternCode columnGraph ((index : Nat) + 6)
  let after : Fin 20 → Nat :=
    fun index =>
      r5ExteriorPatternCode sortedGraph ((index : Nat) + 6)
  let expected : Fin 20 → Nat :=
    r5CrossPatternSortedCode child
  have hafter :
      after = before ∘ Tuple.sort before := by
    funext index
    exact r5ExteriorPatternCode_relabel_sort
      (G := columnGraph) (index := index)
  have hbeforeMultiset :
      (List.ofFn before : Multiset Nat) =
        (List.ofFn expected : Multiset Nat) := by
    calc
      (List.ofFn before : Multiset Nat) =
          r5ExteriorPatternCodeMultiset columnGraph := by
        symm
        exact r5ExteriorPatternCodeMultiset_eq_tuple columnGraph
      _ = Multiset.replicate
            (20 -
              (r5CrossPatternRepresentative child).length) 0 +
          (r5CrossPatternRepresentative child : Multiset Nat) :=
        enumeration.exteriorPatternCodeMultiset_columnRelabel
          child permutation hpattern
      _ = (List.ofFn expected : Multiset Nat) := by
        symm
        exact r5CrossPatternSortedCode_multiset child
  have hpermBeforeExpected :
      (List.ofFn before).Perm (List.ofFn expected) :=
    Multiset.coe_eq_coe.mp hbeforeMultiset
  have hpermAfterBefore :
      (List.ofFn after).Perm (List.ofFn before) := by
    rw [hafter]
    exact (Tuple.sort before).ofFn_comp_perm before
  have hafterMonotone : Monotone after := by
    rw [hafter]
    exact Tuple.monotone_sort before
  have hexpectedMonotone : Monotone expected :=
    r5CrossPatternSortedCode_monotone child
  have hlist :
      List.ofFn after = List.ofFn expected :=
    (hpermAfterBefore.trans hpermBeforeExpected).eq_of_pairwise'
      hafterMonotone.sortedLE_ofFn.pairwise
      hexpectedMonotone.sortedLE_ofFn.pairwise
  have hfunctions : after = expected :=
    List.ofFn_injective hlist
  exact fun index => congrFun hfunctions index

/-- Complete symmetry bridge from a normalized branch-19 graph to one exact
E042 cross-pattern child. -/
theorem exists_r5CanonicalE042Child
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
        left right) :
    ∃ child : Fin 20, ∃ relabeling : Equiv.Perm (Fin 26),
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
      ∀ row : Fin 20,
        r5ExteriorPatternCode H ((row : Nat) + 6) =
          r5CrossPatternSortedCode child row := by
  classical
  obtain ⟨enumeration⟩ :=
    exists_r5Branch19StubEnumeration
      G hregular hneighbor horbit
  obtain ⟨child, permutation, hpattern⟩ :=
    r5_cross_pattern_orbit_check enumeration.endpoints
      enumeration.endpoints_fifth_distinct
  let firstRelabeling :=
    r5Branch19ColumnRelabeling permutation
  let firstGraph := relabelGraph G firstRelabeling
  let secondRelabeling := r5SortExteriorPerm firstGraph
  let finalGraph := relabelGraph firstGraph secondRelabeling
  let finalRelabeling := secondRelabeling.trans firstRelabeling
  have hfirstNeighbor :
      firstGraph.neighborFinset 0 = r5FixedNeighbors := by
    exact r5Branch19ColumnRelabel_neighborFinset
      G hregular hneighbor permutation
  have hfirstOrbit :
      ∀ left right : Fin 5,
        decide (firstGraph.Adj (r5NeighborVertex left)
          (r5NeighborVertex right)) =
        r5FiveVertexAdjacency
          (edgeVectorOfCode
            (r5NeighborhoodRepresentativeCode 19))
          left right :=
    r5Branch19ColumnRelabel_orbit G horbit permutation
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
      rw [show secondRelabeling 0 = 0 by
          exact r5SortExteriorPerm_apply_of_lt_six
            firstGraph 0 (by omega),
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
  have hfinalOrbit :
      ∀ left right : Fin 5,
        decide (finalGraph.Adj (r5NeighborVertex left)
          (r5NeighborVertex right)) =
        r5FiveVertexAdjacency
          (edgeVectorOfCode
            (r5NeighborhoodRepresentativeCode 19))
          left right := by
    intro left right
    change decide (firstGraph.Adj
      (secondRelabeling (r5NeighborVertex left))
      (secondRelabeling (r5NeighborVertex right))) = _
    rw [show secondRelabeling (r5NeighborVertex left) =
          r5NeighborVertex left by
        exact r5SortExteriorPerm_apply_of_lt_six
          firstGraph _ (by
            change (left : Nat) + 1 < 6
            omega),
      show secondRelabeling (r5NeighborVertex right) =
          r5NeighborVertex right by
        exact r5SortExteriorPerm_apply_of_lt_six
          firstGraph _ (by
            change (right : Nat) + 1 < 6
            omega)]
    exact hfirstOrbit left right
  have hfinalCodes :
      ∀ row : Fin 20,
        r5ExteriorPatternCode finalGraph ((row : Nat) + 6) =
          r5CrossPatternSortedCode child row := by
    exact enumeration.exists_sortedCrossPattern
      child permutation hpattern
  refine ⟨child, finalRelabeling,
    ?_, ?_, ?_, ?_, ?_, ?_, hfinalOrbit, hfinalCodes⟩
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
    exact r5ComparisonsSorted_relabel_sort firstGraph

def r5CrossPatternBit
    (child : Fin 20) (row : Fin 20) (position : Fin 5) : Bool :=
  Nat.testBit (r5CrossPatternSortedCode child row)
    (4 - (position : Nat))

def r5CanonicalCrossPatternUnits
    (child : Fin 20) : List R5NamedLiteral :=
  (List.ofFn fun row : Fin 20 =>
    List.ofFn fun position : Fin 5 =>
      r5EdgeLiteralFromBool
        (r5NeighborVertex position)
        ⟨(row : Nat) + 6, by omega⟩
        (r5CrossPatternBit child row position)).flatten

def r5CanonicalE042Units
    (child : Fin 20) : List R5NamedLiteral :=
  r5CanonicalBranchUnits 19 ++
    r5CanonicalCrossPatternUnits child

theorem r5ExteriorPatternCode_testBit
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (exterior : Fin 26) (position : Fin 5) :
    Nat.testBit (r5ExteriorPatternCode G exterior)
        (4 - (position : Nat)) =
      decide (G.Adj (r5NeighborVertex position) exterior) := by
  fin_cases position <;>
    by_cases h0 : G.Adj 1 exterior <;>
    by_cases h1 : G.Adj 2 exterior <;>
    by_cases h2 : G.Adj 3 exterior <;>
    by_cases h3 : G.Adj 4 exterior <;>
    by_cases h4 : G.Adj 5 exterior <;>
    simp_all [r5ExteriorPatternCode, r5ExteriorPatternBit,
      r5NeighborVertex, Nat.testBit]

theorem r5CanonicalCrossPatternUnits_allTrue
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (child : Fin 20)
    (hcodes : ∀ row : Fin 20,
      r5ExteriorPatternCode G ((row : Nat) + 6) =
        r5CrossPatternSortedCode child row) :
    R5NamedClause.AllTrue G
      (r5CanonicalCrossPatternUnits child) := by
  intro literal hliteral
  rw [r5CanonicalCrossPatternUnits,
    List.mem_flatten] at hliteral
  obtain ⟨rowLiterals, hrowLiterals, hliteral⟩ := hliteral
  rw [List.mem_ofFn'] at hrowLiterals
  obtain ⟨row, rfl⟩ := hrowLiterals
  rw [List.mem_ofFn'] at hliteral
  obtain ⟨position, rfl⟩ := hliteral
  apply r5EdgeLiteralFromBool_true
  rw [← r5ExteriorPatternCode_testBit]
  rw [hcodes row]
  rfl

theorem r5CanonicalE042Units_allTrue
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (child : Fin 20)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (horbit : ∀ left right : Fin 5,
      decide (G.Adj (r5NeighborVertex left)
        (r5NeighborVertex right)) =
      r5FiveVertexAdjacency
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode 19))
        left right)
    (hcodes : ∀ row : Fin 20,
      r5ExteriorPatternCode G ((row : Nat) + 6) =
        r5CrossPatternSortedCode child row) :
    R5NamedClause.AllTrue G (r5CanonicalE042Units child) := by
  intro literal hliteral
  rw [r5CanonicalE042Units, List.mem_append] at hliteral
  rcases hliteral with hbranch | hcross
  · exact r5CanonicalBranchUnits_allTrue
      G 19 hneighbor horbit literal hbranch
  · exact r5CanonicalCrossPatternUnits_allTrue
      G child hcodes literal hcross

end Erdos617
