/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.OrderFifteenStructure

/-!
# Small independence-four obstruction

This module formalizes the order-23, order-22, and order-21 obstruction for
admissible graphs with no independent five-set.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

universe u

/-- An admissible order-fifteen graph with no independent four-set and
non-three-colorable complement has at least thirty-five edges. This direct
kernel proof replaces the specialized Kang--Pikhurko endpoint used in the
manuscript. -/
theorem card_edges_ge_thirtyFive_of_admissible_indepSetFree_four_card_fifteen_not_colorable
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (hcard : Fintype.card V = 15) (hnotColorable : ¬Gᶜ.Colorable 3) :
    35 ≤ #G.edgeFinset := by
  classical
  by_contra hnot
  have hedgeUpper : #G.edgeFinset ≤ 34 := by omega
  obtain ⟨v, hmin, hdegree⟩ :=
    exists_minimal_degree_four_of_admissible_indepSetFree_four_card_fifteen
      G hG hfree hcard (by omega)
  let U := exteriorFinset G v
  let R := G.induce (U : Set V)
  have hUcardRaw := card_exterior_type_add_degree_add_one G v
  have hUcard : Fintype.card (U : Set V) = 10 := by
    rw [hcard, hdegree] at hUcardRaw
    simpa [U] using
      (show Fintype.card (exteriorFinset G v : Set V) = 10 by omega)
  have hRadmissible : Admissible R := by
    simpa [R, U] using admissible_induce G hG U
  have hRfree : R.IndepSetFree 3 := by
    simpa [R, U] using
      (indepSetFree_exterior_induce G (k := 3) (by simpa using hfree) v)
  have hsplit := exterior_edges_add_degree_add_choose_le_edges G v hmin
  have hRupper : #R.edgeFinset ≤ 24 := by
    have hsplit' : #R.edgeFinset + G.degree v + (G.degree v).choose 2 ≤
        #G.edgeFinset := by simpa [R, U] using hsplit
    rw [hdegree] at hsplit'
    norm_num [Nat.choose] at hsplit'
    omega
  by_cases hbip : Rᶜ.IsBipartite
  · exact hnotColorable
      (compl_colorable_three_of_bipartite_compl_exterior_degree_four
        G hG hfree hcard v hdegree (by simpa [R, U] using hbip))
  · have hLupper :=
      card_compl_edges_le_twenty_of_admissible_order_ten_nonbipartite
        R hRadmissible hRfree hUcard hbip
    have hpartition := card_edgeFinset_add_card_compl R
    rw [hUcard] at hpartition
    norm_num [Nat.choose] at hpartition
    omega

/-- An admissible order-twenty-three graph with no independent five-set has at
least sixty-two edges. -/
theorem card_edges_ge_sixtyTwo_of_admissible_indepSetFree_five_card_twentyThree
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 5)
    (hcard : Fintype.card V = 23) :
    62 ≤ #G.edgeFinset := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  by_contra hnot
  have hedgeUpper : #G.edgeFinset ≤ 61 := by omega
  obtain ⟨v, hmin, havg⟩ :=
    exists_minimal_vertex_card_mul_degree_le_twice_edges G
  have hdegreeCap : G.degree v ≤ 5 := by
    rw [hcard] at havg
    omega
  let U := exteriorFinset G v
  let R := G.induce (U : Set V)
  have hUcard := card_exterior_type_add_degree_add_one G v
  rw [hcard] at hUcard
  have hUcardU : Fintype.card (U : Set V) + G.degree v + 1 = 23 := by
    simpa [U] using hUcard
  have hRadmissible : Admissible R := by
    simpa [R] using admissible_induce G hG U
  have hRfree : R.IndepSetFree 4 := by
    simpa [R, U] using
      (indepSetFree_exterior_induce G (k := 4) (by simpa using hfree) v)
  have hsplit := exterior_edges_add_degree_add_choose_le_edges G v hmin
  have hsplitR : #R.edgeFinset + G.degree v + (G.degree v).choose 2 ≤
      #G.edgeFinset := by simpa [R, U] using hsplit
  interval_cases hdegree : G.degree v
  · have hRcard : Fintype.card (U : Set V) = 22 := by omega
    have hRbound :=
      card_edges_ge_seventySix_of_admissible_indepSetFree_four_card_twentyTwo
        R hRadmissible hRfree hRcard
    omega
  · have hRcard : Fintype.card (U : Set V) = 21 := by omega
    have hRbound :=
      card_edges_ge_sixtyNine_of_admissible_indepSetFree_four_card_twentyOne
        R hRadmissible hRfree hRcard
    norm_num [hdegree, Nat.choose] at hsplitR
    omega
  · have hRcard : Fintype.card (U : Set V) = 20 := by omega
    have hRbound :=
      card_edges_ge_sixtyTwo_of_admissible_indepSetFree_four_card_twenty
        R hRadmissible hRfree hRcard
    norm_num [hdegree, Nat.choose] at hsplitR
    omega
  · have hRcard : Fintype.card (U : Set V) = 19 := by omega
    have hRbound :=
      card_edges_ge_fiftySix_of_admissible_indepSetFree_four_card_nineteen
        R hRadmissible hRfree hRcard
    norm_num [hdegree, Nat.choose] at hsplitR
    omega
  · have hRcard : Fintype.card (U : Set V) = 18 := by omega
    have hRbound :=
      card_edges_ge_fiftyFour_of_admissible_indepSetFree_four_card_eighteen
        R hRadmissible hRfree hRcard
    norm_num [hdegree, Nat.choose] at hsplitR
    omega
  · have hRcard : Fintype.card (U : Set V) = 17 := by omega
    have hRbound :=
      card_edges_ge_fifty_of_admissible_indepSetFree_four_card_seventeen
        R hRadmissible hRfree hRcard
    norm_num [hdegree, Nat.choose] at hsplitR
    omega

/-- An admissible order-twenty-two graph with no independent five-set has at
least fifty-nine edges. -/
theorem card_edges_ge_fiftyNine_of_admissible_indepSetFree_five_card_twentyTwo
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 5)
    (hcard : Fintype.card V = 22) :
    59 ≤ #G.edgeFinset := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  by_contra hnot
  have hedgeUpper : #G.edgeFinset ≤ 58 := by omega
  obtain ⟨v, hmin, havg⟩ :=
    exists_minimal_vertex_card_mul_degree_le_twice_edges G
  have hdegreeCap : G.degree v ≤ 5 := by
    rw [hcard] at havg
    omega
  let U := exteriorFinset G v
  let R := G.induce (U : Set V)
  have hUcard := card_exterior_type_add_degree_add_one G v
  rw [hcard] at hUcard
  have hUcardU : Fintype.card (U : Set V) + G.degree v + 1 = 22 := by
    simpa [U] using hUcard
  have hRadmissible : Admissible R := by
    simpa [R] using admissible_induce G hG U
  have hRfree : R.IndepSetFree 4 := by
    simpa [R, U] using
      (indepSetFree_exterior_induce G (k := 4) (by simpa using hfree) v)
  have hsplit := exterior_edges_add_degree_add_choose_le_edges G v hmin
  have hsplitR : #R.edgeFinset + G.degree v + (G.degree v).choose 2 ≤
      #G.edgeFinset := by simpa [R, U] using hsplit
  interval_cases hdegree : G.degree v
  · have hRcard : Fintype.card (U : Set V) = 21 := by omega
    have hRbound :=
      card_edges_ge_sixtyNine_of_admissible_indepSetFree_four_card_twentyOne
        R hRadmissible hRfree hRcard
    omega
  · have hRcard : Fintype.card (U : Set V) = 20 := by omega
    have hRbound :=
      card_edges_ge_sixtyTwo_of_admissible_indepSetFree_four_card_twenty
        R hRadmissible hRfree hRcard
    norm_num [hdegree, Nat.choose] at hsplitR
    omega
  · have hRcard : Fintype.card (U : Set V) = 19 := by omega
    have hRbound :=
      card_edges_ge_fiftySix_of_admissible_indepSetFree_four_card_nineteen
        R hRadmissible hRfree hRcard
    norm_num [hdegree, Nat.choose] at hsplitR
    omega
  · have hRcard : Fintype.card (U : Set V) = 18 := by omega
    have hRbound :=
      card_edges_ge_fiftyFour_of_admissible_indepSetFree_four_card_eighteen
        R hRadmissible hRfree hRcard
    norm_num [hdegree, Nat.choose] at hsplitR
    omega
  · have hRcard : Fintype.card (U : Set V) = 17 := by omega
    have hRbound :=
      card_edges_ge_fifty_of_admissible_indepSetFree_four_card_seventeen
        R hRadmissible hRfree hRcard
    norm_num [hdegree, Nat.choose] at hsplitR
    omega
  · have hRcard : Fintype.card (U : Set V) = 16 := by omega
    have hRbound :=
      card_edges_ge_fortyFive_of_admissible_indepSetFree_four_card_sixteen
        R hRadmissible hRfree hRcard
    norm_num [hdegree, Nat.choose] at hsplitR
    omega

/-- A vertex outside an admissible five-clique has at most one neighbor in
that clique. Otherwise the resulting six-set spans at least twelve edges. -/
theorem card_filter_adj_le_one_of_admissible_clique_five
    {V : Type u} [Finite V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : Admissible G)
    (A : Finset V) (hAcard : #A = 5) (hAclique : G.IsClique (A : Set V))
    (x : V) (hxNotA : x ∉ A) :
    #(A.filter (G.Adj x)) ≤ 1 := by
  classical
  letI := Fintype.ofFinite V
  let B : Finset V := {x}
  let D := G.between (B : Set V) (A : Set V)
  have hxB : x ∈ B := by simp [B]
  have hdis : Disjoint B A := by
    rw [Finset.disjoint_left]
    intro y hyB hyA
    have hyx : y = x := by simpa [B] using hyB
    exact hxNotA (hyx ▸ hyA)
  have hAindComp : Gᶜ.IsIndepSet (A : Set V) := by simpa using hAclique
  have hSix : #(insert x A) = 6 := by
    rw [Finset.card_insert_of_notMem hxNotA, hAcard]
  have hfour := four_le_card_induced_compl_of_admissible_six
    G hG (insert x A) hSix
  have hfourNat :
      4 ≤ Nat.card (Gᶜ.induce (((insert x A : Finset V) : Set V))).edgeSet := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
    exact hfour
  have hexact := card_induce_insert_eq_between_degree_of_independent
    Gᶜ A B x hxB hdis.symm hAindComp
  rw [hexact] at hfourNat
  have hcomm := degree_between_comm Gᶜ A B x
  rw [hcomm] at hfourNat
  have hpartition :=
    degree_between_add_compl_between_eq_card G B A hdis x hxB
  rw [hAcard] at hpartition
  have hDdegree : D.degree x ≤ 1 := by simpa [D] using (show
    (G.between (B : Set V) (A : Set V)).degree x ≤ 1 by omega)
  calc
    #(A.filter (G.Adj x)) = #(D.neighborFinset x) := by
      congr 1
      ext y
      simp [D, B, SimpleGraph.between_adj, hxNotA, and_comm]
    _ = D.degree x := SimpleGraph.card_neighborFinset_eq_degree D x
    _ ≤ 1 := hDdegree

/-- A three-coloring of the complement of an admissible order-fifteen graph
is an exact partition into three five-cliques of the original graph. -/
theorem exists_three_five_clique_partition_of_compl_colorable_order_fifteen
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hcard : Fintype.card V = 15)
    (hcolor : Gᶜ.Colorable 3) :
    ∃ A B C : Finset V,
      #A = 5 ∧ #B = 5 ∧ #C = 5 ∧
      Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧
      (A ∪ B) ∪ C = Finset.univ ∧
      G.IsClique (A : Set V) ∧ G.IsClique (B : Set V) ∧
      G.IsClique (C : Set V) := by
  classical
  obtain ⟨c⟩ := hcolor
  let A : Finset V := Finset.univ.filter fun v => c v = (0 : Fin 3)
  let B : Finset V := Finset.univ.filter fun v => c v = (1 : Fin 3)
  let C : Finset V := Finset.univ.filter fun v => c v = (2 : Fin 3)
  have hABdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have hx0 : c x = (0 : Fin 3) := by simpa [A] using hxA
    have hx1 : c x = (1 : Fin 3) := by simpa [B] using hxB
    omega
  have hACdis : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro x hxA hxC
    have hx0 : c x = (0 : Fin 3) := by simpa [A] using hxA
    have hx2 : c x = (2 : Fin 3) := by simpa [C] using hxC
    omega
  have hBCdis : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro x hxB hxC
    have hx1 : c x = (1 : Fin 3) := by simpa [B] using hxB
    have hx2 : c x = (2 : Fin 3) := by simpa [C] using hxC
    omega
  have hcover : (A ∪ B) ∪ C = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    have hx : c x = (0 : Fin 3) ∨ c x = (1 : Fin 3) ∨
        c x = (2 : Fin 3) := by omega
    rcases hx with hx0 | hx1 | hx2
    · exact Or.inl (Or.inl (by simpa [A] using hx0))
    · exact Or.inl (Or.inr (by simpa [B] using hx1))
    · exact Or.inr (by simpa [C] using hx2)
  have hAclique : G.IsClique (A : Set V) := by
    intro x hxA y hyA hxy
    have hx0 : c x = (0 : Fin 3) := by simpa [A] using hxA
    have hy0 : c y = (0 : Fin 3) := by simpa [A] using hyA
    by_contra hnot
    exact c.valid ⟨hxy, hnot⟩ (hx0.trans hy0.symm)
  have hBclique : G.IsClique (B : Set V) := by
    intro x hxB y hyB hxy
    have hx1 : c x = (1 : Fin 3) := by simpa [B] using hxB
    have hy1 : c y = (1 : Fin 3) := by simpa [B] using hyB
    by_contra hnot
    exact c.valid ⟨hxy, hnot⟩ (hx1.trans hy1.symm)
  have hCclique : G.IsClique (C : Set V) := by
    intro x hxC y hyC hxy
    have hx2 : c x = (2 : Fin 3) := by simpa [C] using hxC
    have hy2 : c y = (2 : Fin 3) := by simpa [C] using hyC
    by_contra hnot
    exact c.valid ⟨hxy, hnot⟩ (hx2.trans hy2.symm)
  have hpartUpper (P : Finset V) (hPclique : G.IsClique (P : Set V)) :
      #P ≤ 5 := by
    by_contra hnot
    have hlarge : 6 ≤ #P := by omega
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hlarge
    have hSclique : G.IsClique (S : Set V) := by
      intro x hx y hy hxy
      exact hPclique (hSsub hx) (hSsub hy) hxy
    exact (admissible_cliqueFree_six G hG) S ⟨hSclique, hScard⟩
  have hAle : #A ≤ 5 := hpartUpper A hAclique
  have hBle : #B ≤ 5 := hpartUpper B hBclique
  have hCle : #C ≤ 5 := hpartUpper C hCclique
  have hABCdis : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    intro x hxAB hxC
    rcases Finset.mem_union.mp hxAB with hxA | hxB
    · exact (Finset.disjoint_left.mp hACdis) hxA hxC
    · exact (Finset.disjoint_left.mp hBCdis) hxB hxC
  have hsum : #A + #B + #C = 15 := by
    calc
      #A + #B + #C = #(A ∪ B) + #C := by
        rw [Finset.card_union_of_disjoint hABdis]
      _ = #((A ∪ B) ∪ C) :=
        (Finset.card_union_of_disjoint hABCdis).symm
      _ = 15 := by rw [hcover, Finset.card_univ, hcard]
  have hAcard : #A = 5 := by omega
  have hBcard : #B = 5 := by omega
  have hCcard : #C = 5 := by omega
  exact ⟨A, B, C, hAcard, hBcard, hCcard, hABdis, hACdis, hBCdis,
    hcover, hAclique, hBclique, hCclique⟩

/-- Five pairwise distinct, pairwise nonadjacent vertices contradict
`IndepSetFree 5`. -/
theorem false_of_indepSetFree_five_of_pairwise_nonadj
    {V : Type u} (G : SimpleGraph V)
    (hfree : G.IndepSetFree 5) {a b c d e : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hnab : ¬G.Adj a b) (hnac : ¬G.Adj a c)
    (hnad : ¬G.Adj a d) (hnae : ¬G.Adj a e)
    (hnbc : ¬G.Adj b c) (hnbd : ¬G.Adj b d)
    (hnbe : ¬G.Adj b e) (hncd : ¬G.Adj c d)
    (hnce : ¬G.Adj c e) (hnde : ¬G.Adj d e) :
    False := by
  classical
  let S : Finset V := {a, b, c, d, e}
  apply hfree S
  constructor
  · intro x hx y hy hxy hxyG
    have hx' : x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e := by
      simpa [S] using hx
    have hy' : y = a ∨ y = b ∨ y = c ∨ y = d ∨ y = e := by
      simpa [S] using hy
    rcases hx' with rfl | rfl | rfl | rfl | rfl <;>
      rcases hy' with rfl | rfl | rfl | rfl | rfl <;>
      simp_all only [SimpleGraph.irrefl, SimpleGraph.adj_comm] <;>
      contradiction
  · simp [S, hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde]

/-- If the order-fifteen exterior complement at a degree-five vertex is
three-colorable, the open neighborhood is a clique. The proof extracts three
five-cliques and greedily chooses common avoiders in sizes three, two, and
one. -/
theorem neighborhood_isClique_of_colorable_compl_exterior_degree_five_card_twentyOne
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 5)
    (hcard : Fintype.card V = 21) (v : V) (hdegree : G.degree v = 5)
    (hcolor : (G.induce (exteriorFinset G v : Set V))ᶜ.Colorable 3) :
    G.IsClique (G.neighborFinset v : Set V) := by
  classical
  let N := G.neighborFinset v
  let U := exteriorFinset G v
  let R := G.induce (U : Set V)
  have hUcardRaw := card_exterior_type_add_degree_add_one G v
  have hUcard : Fintype.card (U : Set V) = 15 := by
    rw [hcard, hdegree] at hUcardRaw
    simpa [U] using
      (show Fintype.card (exteriorFinset G v : Set V) = 15 by omega)
  have hRadmissible : Admissible R := by
    simpa [R, U] using admissible_induce G hG U
  obtain ⟨A, B, C, hAcard, hBcard, hCcard, hABdis, hACdis, hBCdis,
      hABCcover, hAclique, hBclique, hCclique⟩ :=
    exists_three_five_clique_partition_of_compl_colorable_order_fifteen
      R hRadmissible hUcard (by simpa [R, U] using hcolor)
  let f : (U : Set V) ↪ V := Function.Embedding.subtype _
  let A₀ : Finset V := A.map f
  let B₀ : Finset V := B.map f
  let C₀ : Finset V := C.map f
  have hA₀card : #A₀ = 5 := by simp [A₀, hAcard]
  have hB₀card : #B₀ = 5 := by simp [B₀, hBcard]
  have hC₀card : #C₀ = 5 := by simp [C₀, hCcard]
  have hA₀clique : G.IsClique (A₀ : Set V) := by
    intro x hx y hy hxy
    obtain ⟨x', hx'A, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy'A, rfl⟩ := Finset.mem_map.mp hy
    have hxy' : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
    change G.Adj (x' : V) (y' : V)
    simpa [R] using hAclique hx'A hy'A hxy'
  have hB₀clique : G.IsClique (B₀ : Set V) := by
    intro x hx y hy hxy
    obtain ⟨x', hx'B, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy'B, rfl⟩ := Finset.mem_map.mp hy
    have hxy' : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
    change G.Adj (x' : V) (y' : V)
    simpa [R] using hBclique hx'B hy'B hxy'
  have hC₀clique : G.IsClique (C₀ : Set V) := by
    intro x hx y hy hxy
    obtain ⟨x', hx'C, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy'C, rfl⟩ := Finset.mem_map.mp hy
    have hxy' : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
    change G.Adj (x' : V) (y' : V)
    simpa [R] using hCclique hx'C hy'C hxy'
  have hNUdis : Disjoint N U := by
    rw [Finset.disjoint_left]
    intro x hxN hxU
    have hvx : G.Adj v x := by simpa [N] using hxN
    have hxU' : x ≠ v ∧ ¬G.Adj v x := by
      simpa [U, exteriorFinset] using hxU
    exact hxU'.2 hvx
  have hNA₀dis : Disjoint N A₀ := by
    rw [Finset.disjoint_left]
    intro x hxN hxA₀
    obtain ⟨x', hx'A, rfl⟩ := Finset.mem_map.mp hxA₀
    exact (Finset.disjoint_left.mp hNUdis) hxN x'.property
  have hNB₀dis : Disjoint N B₀ := by
    rw [Finset.disjoint_left]
    intro x hxN hxB₀
    obtain ⟨x', hx'B, rfl⟩ := Finset.mem_map.mp hxB₀
    exact (Finset.disjoint_left.mp hNUdis) hxN x'.property
  have hNC₀dis : Disjoint N C₀ := by
    rw [Finset.disjoint_left]
    intro x hxN hxC₀
    obtain ⟨x', hx'C, rfl⟩ := Finset.mem_map.mp hxC₀
    exact (Finset.disjoint_left.mp hNUdis) hxN x'.property
  have hA₀B₀dis : Disjoint A₀ B₀ := by
    rw [Finset.disjoint_left]
    intro x hxA₀ hxB₀
    obtain ⟨xA, hxA, hxAval⟩ := Finset.mem_map.mp hxA₀
    obtain ⟨xB, hxB, hxBval⟩ := Finset.mem_map.mp hxB₀
    have hEq : xA = xB := Subtype.ext (hxAval.trans hxBval.symm)
    exact (Finset.disjoint_left.mp hABdis) hxA (hEq ▸ hxB)
  have hA₀C₀dis : Disjoint A₀ C₀ := by
    rw [Finset.disjoint_left]
    intro x hxA₀ hxC₀
    obtain ⟨xA, hxA, hxAval⟩ := Finset.mem_map.mp hxA₀
    obtain ⟨xC, hxC, hxCval⟩ := Finset.mem_map.mp hxC₀
    have hEq : xA = xC := Subtype.ext (hxAval.trans hxCval.symm)
    exact (Finset.disjoint_left.mp hACdis) hxA (hEq ▸ hxC)
  have hB₀C₀dis : Disjoint B₀ C₀ := by
    rw [Finset.disjoint_left]
    intro x hxB₀ hxC₀
    obtain ⟨xB, hxB, hxBval⟩ := Finset.mem_map.mp hxB₀
    obtain ⟨xC, hxC, hxCval⟩ := Finset.mem_map.mp hxC₀
    have hEq : xB = xC := Subtype.ext (hxBval.trans hxCval.symm)
    exact (Finset.disjoint_left.mp hBCdis) hxB (hEq ▸ hxC)
  intro a haN b hbN hab
  by_contra hnab
  have haNotA₀ : a ∉ A₀ := fun ha =>
    (Finset.disjoint_left.mp hNA₀dis) haN ha
  have hbNotA₀ : b ∉ A₀ := fun hb =>
    (Finset.disjoint_left.mp hNA₀dis) hbN hb
  have haNotB₀ : a ∉ B₀ := fun ha =>
    (Finset.disjoint_left.mp hNB₀dis) haN ha
  have hbNotB₀ : b ∉ B₀ := fun hb =>
    (Finset.disjoint_left.mp hNB₀dis) hbN hb
  have haNotC₀ : a ∉ C₀ := fun ha =>
    (Finset.disjoint_left.mp hNC₀dis) haN ha
  have hbNotC₀ : b ∉ C₀ := fun hb =>
    (Finset.disjoint_left.mp hNC₀dis) hbN hb
  let badA := A₀.filter (G.Adj a) ∪ A₀.filter (G.Adj b)
  let goodA := A₀ \ badA
  have hbadAsub : badA ⊆ A₀ :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hbadAcard : #badA ≤ 2 := by
    have hu := Finset.card_union_le (A₀.filter (G.Adj a))
      (A₀.filter (G.Adj b))
    have haLe := card_filter_adj_le_one_of_admissible_clique_five
      G hG A₀ hA₀card hA₀clique a haNotA₀
    have hbLe := card_filter_adj_le_one_of_admissible_clique_five
      G hG A₀ hA₀card hA₀clique b hbNotA₀
    change #(A₀.filter (G.Adj a) ∪ A₀.filter (G.Adj b)) ≤ 2
    omega
  have hgoodAcard : 3 ≤ #goodA := by
    have hs := Finset.card_sdiff_of_subset hbadAsub
    rw [hA₀card] at hs
    have hs' : #goodA = 5 - #badA := by simpa [goodA] using hs
    omega
  obtain ⟨x, hxgood⟩ := Finset.card_pos.mp (by omega : 0 < #goodA)
  have hxA₀ : x ∈ A₀ := (Finset.mem_sdiff.mp hxgood).1
  have hxAvoid : ¬G.Adj a x ∧ ¬G.Adj b x := by
    have hxnot := (Finset.mem_sdiff.mp hxgood).2
    simpa [badA, hxA₀] using hxnot
  have hxNotB₀ : x ∉ B₀ := fun hxB₀ =>
    (Finset.disjoint_left.mp hA₀B₀dis) hxA₀ hxB₀
  have hxNotC₀ : x ∉ C₀ := fun hxC₀ =>
    (Finset.disjoint_left.mp hA₀C₀dis) hxA₀ hxC₀
  let badB := (B₀.filter (G.Adj a) ∪ B₀.filter (G.Adj b)) ∪
    B₀.filter (G.Adj x)
  let goodB := B₀ \ badB
  have hbadBsub : badB ⊆ B₀ :=
    Finset.union_subset
      (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
      (Finset.filter_subset _ _)
  have hbadBcard : #badB ≤ 3 := by
    have habUnion := Finset.card_union_le
      (B₀.filter (G.Adj a)) (B₀.filter (G.Adj b))
    have hallUnion := Finset.card_union_le
      (B₀.filter (G.Adj a) ∪ B₀.filter (G.Adj b))
      (B₀.filter (G.Adj x))
    have haLe := card_filter_adj_le_one_of_admissible_clique_five
      G hG B₀ hB₀card hB₀clique a haNotB₀
    have hbLe := card_filter_adj_le_one_of_admissible_clique_five
      G hG B₀ hB₀card hB₀clique b hbNotB₀
    have hxLe := card_filter_adj_le_one_of_admissible_clique_five
      G hG B₀ hB₀card hB₀clique x hxNotB₀
    change #((B₀.filter (G.Adj a) ∪ B₀.filter (G.Adj b)) ∪
      B₀.filter (G.Adj x)) ≤ 3
    omega
  have hgoodBcard : 2 ≤ #goodB := by
    have hs := Finset.card_sdiff_of_subset hbadBsub
    rw [hB₀card] at hs
    have hs' : #goodB = 5 - #badB := by simpa [goodB] using hs
    omega
  obtain ⟨y, hygood⟩ := Finset.card_pos.mp (by omega : 0 < #goodB)
  have hyB₀ : y ∈ B₀ := (Finset.mem_sdiff.mp hygood).1
  have hyAvoid : ¬G.Adj a y ∧ ¬G.Adj b y ∧ ¬G.Adj x y := by
    have hynot := (Finset.mem_sdiff.mp hygood).2
    simpa [badB, hyB₀] using hynot
  have hyNotC₀ : y ∉ C₀ := fun hyC₀ =>
    (Finset.disjoint_left.mp hB₀C₀dis) hyB₀ hyC₀
  let badC := ((C₀.filter (G.Adj a) ∪ C₀.filter (G.Adj b)) ∪
    C₀.filter (G.Adj x)) ∪ C₀.filter (G.Adj y)
  let goodC := C₀ \ badC
  have hbadCsub : badC ⊆ C₀ :=
    Finset.union_subset
      (Finset.union_subset
        (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
        (Finset.filter_subset _ _))
      (Finset.filter_subset _ _)
  have hbadCcard : #badC ≤ 4 := by
    have habUnion := Finset.card_union_le
      (C₀.filter (G.Adj a)) (C₀.filter (G.Adj b))
    have habxUnion := Finset.card_union_le
      (C₀.filter (G.Adj a) ∪ C₀.filter (G.Adj b))
      (C₀.filter (G.Adj x))
    have hallUnion := Finset.card_union_le
      ((C₀.filter (G.Adj a) ∪ C₀.filter (G.Adj b)) ∪
        C₀.filter (G.Adj x)) (C₀.filter (G.Adj y))
    have haLe := card_filter_adj_le_one_of_admissible_clique_five
      G hG C₀ hC₀card hC₀clique a haNotC₀
    have hbLe := card_filter_adj_le_one_of_admissible_clique_five
      G hG C₀ hC₀card hC₀clique b hbNotC₀
    have hxLe := card_filter_adj_le_one_of_admissible_clique_five
      G hG C₀ hC₀card hC₀clique x hxNotC₀
    have hyLe := card_filter_adj_le_one_of_admissible_clique_five
      G hG C₀ hC₀card hC₀clique y hyNotC₀
    change #(((C₀.filter (G.Adj a) ∪ C₀.filter (G.Adj b)) ∪
      C₀.filter (G.Adj x)) ∪ C₀.filter (G.Adj y)) ≤ 4
    omega
  have hgoodCcard : 1 ≤ #goodC := by
    have hs := Finset.card_sdiff_of_subset hbadCsub
    rw [hC₀card] at hs
    have hs' : #goodC = 5 - #badC := by simpa [goodC] using hs
    omega
  obtain ⟨z, hzgood⟩ := Finset.card_pos.mp (by omega : 0 < #goodC)
  have hzC₀ : z ∈ C₀ := (Finset.mem_sdiff.mp hzgood).1
  have hzAvoid : ¬G.Adj a z ∧ ¬G.Adj b z ∧
      ¬G.Adj x z ∧ ¬G.Adj y z := by
    have hznot := (Finset.mem_sdiff.mp hzgood).2
    simpa [badC, hzC₀] using hznot
  have hax : a ≠ x := fun h =>
    (Finset.disjoint_left.mp hNA₀dis) haN (h ▸ hxA₀)
  have hay : a ≠ y := fun h =>
    (Finset.disjoint_left.mp hNB₀dis) haN (h ▸ hyB₀)
  have haz : a ≠ z := fun h =>
    (Finset.disjoint_left.mp hNC₀dis) haN (h ▸ hzC₀)
  have hbx : b ≠ x := fun h =>
    (Finset.disjoint_left.mp hNA₀dis) hbN (h ▸ hxA₀)
  have hby : b ≠ y := fun h =>
    (Finset.disjoint_left.mp hNB₀dis) hbN (h ▸ hyB₀)
  have hbz : b ≠ z := fun h =>
    (Finset.disjoint_left.mp hNC₀dis) hbN (h ▸ hzC₀)
  have hxy : x ≠ y := fun h =>
    (Finset.disjoint_left.mp hA₀B₀dis) hxA₀ (h ▸ hyB₀)
  have hxz : x ≠ z := fun h =>
    (Finset.disjoint_left.mp hA₀C₀dis) hxA₀ (h ▸ hzC₀)
  have hyz : y ≠ z := fun h =>
    (Finset.disjoint_left.mp hB₀C₀dis) hyB₀ (h ▸ hzC₀)
  exact false_of_indepSetFree_five_of_pairwise_nonadj G hfree
    hab hax hay haz hbx hby hbz hxy hxz hyz hnab hxAvoid.1
    hyAvoid.1 hzAvoid.1 hxAvoid.2 hyAvoid.2.1 hzAvoid.2.1
    hyAvoid.2.2 hzAvoid.2.2.1 hzAvoid.2.2.2

/-- The three-colorable order-fifteen exterior branch makes a forbidden
six-clique with the center. -/
theorem false_of_colorable_compl_exterior_degree_five_card_twentyOne
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 5)
    (hcard : Fintype.card V = 21) (v : V) (hdegree : G.degree v = 5)
    (hcolor : (G.induce (exteriorFinset G v : Set V))ᶜ.Colorable 3) :
    False := by
  classical
  let N := G.neighborFinset v
  let S : Finset V := insert v N
  have hNclique : G.IsClique (N : Set V) := by
    simpa [N] using
      neighborhood_isClique_of_colorable_compl_exterior_degree_five_card_twentyOne
        G hG hfree hcard v hdegree hcolor
  have hScard : #S = 6 := by
    simp [S, N, G.notMem_neighborFinset_self v,
      SimpleGraph.card_neighborFinset_eq_degree, hdegree]
  have hSclique : G.IsClique (S : Set V) := by
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with rfl | haN
    · have hbN : b ∈ N := by
        rcases Finset.mem_insert.mp hb with hbv | hbN
        · exact (hab hbv.symm).elim
        · exact hbN
      simpa [N] using hbN
    · rcases Finset.mem_insert.mp hb with hbv | hbN
      · subst b
        have hva : G.Adj v a := by simpa [N] using haN
        exact hva.symm
      · exact hNclique haN hbN hab
  exact (admissible_cliqueFree_six G hG) S ⟨hSclique, hScard⟩

/-- The non-three-colorable order-fifteen exterior branch at order twenty-one
forces E053's isolated five-clique and then a vertex cover of size at most five
in the canonical residual complement, whose cover number is six. -/
theorem false_of_not_colorable_compl_exterior_degree_five_card_twentyOne
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 5)
    (hcard : Fintype.card V = 21) (hedgeUpper : #G.edgeFinset ≤ 54)
    (v : V) (hdegree : G.degree v = 5)
    (hmin : ∀ w, G.degree v ≤ G.degree w)
    (hnotColor : ¬(G.induce (exteriorFinset G v : Set V))ᶜ.Colorable 3) :
    False := by
  classical
  let N := G.neighborFinset v
  let U := exteriorFinset G v
  let R := G.induce (U : Set V)
  let D := G.between (N : Set V) (U : Set V)
  let H := G.induce (N : Set V)
  let M := Hᶜ
  have hNcard : #N = 5 := by
    simp [N, SimpleGraph.card_neighborFinset_eq_degree, hdegree]
  have hNtype : Fintype.card (N : Set V) = 5 := by simpa using hNcard
  have hUcardRaw := card_exterior_type_add_degree_add_one G v
  have hUcard : Fintype.card (U : Set V) = 15 := by
    rw [hcard, hdegree] at hUcardRaw
    simpa [U] using
      (show Fintype.card (exteriorFinset G v : Set V) = 15 by omega)
  have hRadmissible : Admissible R := by
    simpa [R, U] using admissible_induce G hG U
  have hRfree : R.IndepSetFree 4 := by
    simpa [R, U] using
      (indepSetFree_exterior_induce G (k := 4) (by simpa using hfree) v)
  have hRlower :=
    card_edges_ge_thirtyFive_of_admissible_indepSetFree_four_card_fifteen_not_colorable
      R hRadmissible hRfree hUcard (by simpa [R, U] using hnotColor)
  have hstrong :=
    exterior_edges_add_nineteen_le_edges_of_admissible_degree_five
      G hG v hdegree hmin
  have hstrongR : #R.edgeFinset + 19 ≤ #G.edgeFinset := by
    simpa [R, U] using hstrong
  have hRedges : #R.edgeFinset = 35 := by omega
  have hGedges : #G.edgeFinset = 54 := by omega
  have haccountExact :=
    card_edges_eq_exterior_add_degree_add_accounting G v
  have haccount : neighborhoodCrossEdgeCount G v +
      neighborhoodInternalEdgeCount G v = 14 := by
    have haccount' : #R.edgeFinset + G.degree v +
        (neighborhoodCrossEdgeCount G v +
          neighborhoodInternalEdgeCount G v) = #G.edgeFinset := by
      simpa [R, U] using haccountExact
    rw [hRedges, hdegree, hGedges] at haccount'
    omega
  have hYupper :=
    neighborhoodInternalEdgeCount_le_six_of_admissible_degree_five
      G hG v hdegree
  have htwice := neighborhood_cross_add_twice_internal_ge G v hmin
  rw [hdegree] at htwice
  norm_num at htwice
  have hY : neighborhoodInternalEdgeCount G v = 6 := by omega
  have hX : neighborhoodCrossEdgeCount G v = 8 := by omega
  have hHedges : #H.edgeFinset = 6 := by
    have hi := neighborhoodInternalEdgeCount_eq_induce G v
    rw [hY] at hi
    simpa [H, N] using hi.symm
  have hMpartition := card_edgeFinset_add_card_compl H
  rw [hNtype, hHedges] at hMpartition
  norm_num [Nat.choose] at hMpartition
  have hMedges : #M.edgeFinset = 4 := by
    simpa [M] using (show #Hᶜ.edgeFinset = 4 by omega)
  have hNUdis : Disjoint N U := by
    rw [Finset.disjoint_left]
    intro x hxN hxU
    have hvx : G.Adj v x := by simpa [N] using hxN
    have hxU' : x ≠ v ∧ ¬G.Adj v x := by
      simpa [U, exteriorFinset] using hxU
    exact hxU'.2 hvx
  have hNUdisSet : Disjoint (N : Set V) (U : Set V) :=
    Finset.disjoint_coe.mpr hNUdis
  have hDbip : D.IsBipartiteWith (N : Set V) (U : Set V) := by
    simpa [D] using SimpleGraph.between_isBipartiteWith (G := G) hNUdisSet
  have hDedges : #D.edgeFinset = 8 := by
    simpa [D, N, U, neighborhoodCrossEdgeCount] using hX
  have hInternalDegree (a : (N : Set V)) :
      H.degree a = (neighborhoodInternalGraph G v).degree (a : V) := by
    let fN : (N : Set V) ↪ V := Function.Embedding.subtype _
    have hmap :
        ((G.induce (N : Set V)).neighborFinset a).map fN =
          G.neighborFinset (a : V) ∩ N := by
      ext x
      simp [fN]
    have hva : G.Adj v (a : V) := by simpa [N] using a.property
    have hneighbors :
        G.neighborFinset (a : V) ∩ N =
          (neighborhoodInternalGraph G v).neighborFinset (a : V) := by
      ext x
      simp [N, neighborhoodInternalGraph, SimpleGraph.between_adj,
        hva, and_comm]
    change (G.induce (N : Set V)).degree a =
      (neighborhoodInternalGraph G v).degree (a : V)
    calc
      (G.induce (N : Set V)).degree a =
          #((G.induce (N : Set V)).neighborFinset a) := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
      _ = #(((G.induce (N : Set V)).neighborFinset a).map fN) := by simp
      _ = #(G.neighborFinset (a : V) ∩ N) := congrArg Finset.card hmap
      _ = #((neighborhoodInternalGraph G v).neighborFinset (a : V)) :=
        congrArg Finset.card hneighbors
      _ = (neighborhoodInternalGraph G v).degree (a : V) :=
        SimpleGraph.card_neighborFinset_eq_degree _ _
  have hPointLe (a : (N : Set V)) : M.degree a ≤ D.degree (a : V) := by
    have hdecomp := degree_neighbor_eq_one_add_internal_add_cross
      G v (a : V) a.property
    have hminimum : 5 ≤ G.degree (a : V) := by
      simpa [hdegree] using hmin (a : V)
    have hMdegree := SimpleGraph.degree_compl H a
    rw [hNtype] at hMdegree
    norm_num at hMdegree
    have hI := hInternalDegree a
    change Hᶜ.degree a ≤
      (G.between (N : Set V) (U : Set V)).degree (a : V)
    have hdecomp' : G.degree (a : V) =
        1 + (neighborhoodInternalGraph G v).degree (a : V) +
          (G.between (N : Set V) (U : Set V)).degree (a : V) := by
      simpa [N, U] using hdecomp
    omega
  have hSumM : (∑ a : (N : Set V), M.degree a) = 8 := by
    have hs := M.sum_degrees_eq_twice_card_edges
    rw [hMedges] at hs
    norm_num at hs ⊢
    exact hs
  have hSumDbase : (∑ a ∈ N, D.degree a) = 8 := by
    have hs := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hDbip
    rw [hDedges] at hs
    exact hs
  have hSumD : (∑ a : (N : Set V), D.degree (a : V)) = 8 := by
    have hs := Finset.sum_attach N (fun a => D.degree a)
    rw [Finset.attach_eq_univ] at hs
    calc
      (∑ a : (N : Set V), D.degree (a : V)) = ∑ a ∈ N, D.degree a := hs
      _ = 8 := hSumDbase
  have hPointEq (a : (N : Set V)) : M.degree a = D.degree (a : V) := by
    have hsumEq : (∑ x : (N : Set V), M.degree x) =
        ∑ x : (N : Set V), D.degree (x : V) := by omega
    have hp := (Finset.sum_eq_sum_iff_of_le
      (s := (Finset.univ : Finset (N : Set V)))
      (fun x _ => hPointLe x)).mp hsumEq
    exact hp a (Finset.mem_univ a)
  have hstructure :=
    orderFifteenThirtyFiveStructure_of_admissible
      R hRadmissible hRfree hUcard hRedges (by simpa [R, U] using hnotColor)
  rcases hstructure with ⟨C, hCcard, hCisolated, hiso⟩
  let Q : Finset (U : Set V) := Cᶜ
  let T := (R.induce (Q : Set (U : Set V)))ᶜ
  have hisoT : Nonempty (T ≃g balancedC5Blowup) := by
    simpa [T, Q] using hiso
  obtain ⟨isoT⟩ := hisoT
  have hTcoverEq : T.vertexCoverNum = 6 :=
    (SimpleGraph.vertexCoverNum_congr isoT).trans
      balancedC5Blowup_vertexCoverNum
  let fU : (U : Set V) ↪ V := Function.Embedding.subtype _
  let C₀ : Finset V := C.map fU
  have hC₀card : #C₀ = 5 := by simp [C₀, hCcard]
  have hC₀clique : G.IsClique (C₀ : Set V) := by
    intro x hx y hy hxy
    obtain ⟨x', hx'C, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy'C, rfl⟩ := Finset.mem_map.mp hy
    have hxy' : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
    change G.Adj (x' : V) (y' : V)
    simpa [R] using hCisolated.1 hx'C hy'C hxy'
  have hNC₀dis : Disjoint N C₀ := by
    rw [Finset.disjoint_left]
    intro x hxN hxC₀
    obtain ⟨x', hx'C, rfl⟩ := Finset.mem_map.mp hxC₀
    exact (Finset.disjoint_left.mp hNUdis) hxN x'.property
  have hMnonempty : M.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨e, he⟩ := hMnonempty
  induction e using Sym2.inductionOn with
  | hf a b =>
    have habM : M.Adj a b := by simpa using he
    have hMpair := degree_add_degree_le_card_edges_add_one_of_adj M habM
    rw [hMedges] at hMpair
    have hDpair : D.degree (a : V) + D.degree (b : V) ≤ 5 := by
      rw [← hPointEq a, ← hPointEq b]
      exact hMpair
    have haNotC₀ : (a : V) ∉ C₀ := fun ha =>
      (Finset.disjoint_left.mp hNC₀dis) a.property ha
    have hbNotC₀ : (b : V) ∉ C₀ := fun hb =>
      (Finset.disjoint_left.mp hNC₀dis) b.property hb
    let badC := C₀.filter (G.Adj (a : V)) ∪
      C₀.filter (G.Adj (b : V))
    let goodC := C₀ \ badC
    have hbadCsub : badC ⊆ C₀ :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hbadCcard : #badC ≤ 2 := by
      have hu := Finset.card_union_le
        (C₀.filter (G.Adj (a : V))) (C₀.filter (G.Adj (b : V)))
      have haLe := card_filter_adj_le_one_of_admissible_clique_five
        G hG C₀ hC₀card hC₀clique (a : V) haNotC₀
      have hbLe := card_filter_adj_le_one_of_admissible_clique_five
        G hG C₀ hC₀card hC₀clique (b : V) hbNotC₀
      change #(C₀.filter (G.Adj (a : V)) ∪
        C₀.filter (G.Adj (b : V))) ≤ 2
      omega
    have hgoodCcard : 3 ≤ #goodC := by
      have hs := Finset.card_sdiff_of_subset hbadCsub
      rw [hC₀card] at hs
      have hs' : #goodC = 5 - #badC := by simpa [goodC] using hs
      omega
    obtain ⟨c₀, hc₀good⟩ := Finset.card_pos.mp (by omega : 0 < #goodC)
    have hc₀C₀ : c₀ ∈ C₀ := (Finset.mem_sdiff.mp hc₀good).1
    have hc₀Avoid : ¬G.Adj (a : V) c₀ ∧ ¬G.Adj (b : V) c₀ := by
      have hc₀not := (Finset.mem_sdiff.mp hc₀good).2
      simpa [badC, hc₀C₀] using hc₀not
    obtain ⟨c, hcC, hcval⟩ := Finset.mem_map.mp hc₀C₀
    subst c₀
    let Kₐ : Finset (Q : Set (U : Set V)) :=
      Finset.univ.filter fun x => G.Adj (a : V) (x : V)
    let Kb : Finset (Q : Set (U : Set V)) :=
      Finset.univ.filter fun x => G.Adj (b : V) (x : V)
    let K : Finset (Q : Set (U : Set V)) := Kₐ ∪ Kb
    let fQ : (Q : Set (U : Set V)) ↪ V :=
      ⟨fun x => (x : V), fun x y h => Subtype.ext (Subtype.ext h)⟩
    have hKₐmapSub : Kₐ.map fQ ⊆ D.neighborFinset (a : V) := by
      intro x hx
      obtain ⟨x', hx'K, rfl⟩ := Finset.mem_map.mp hx
      have hxAdj : G.Adj (a : V) (x' : V) := by simpa [Kₐ] using hx'K
      rw [SimpleGraph.mem_neighborFinset]
      exact ⟨by simpa [fQ] using hxAdj,
        Or.inl ⟨a.property, x'.val.property⟩⟩
    have hKbmapSub : Kb.map fQ ⊆ D.neighborFinset (b : V) := by
      intro x hx
      obtain ⟨x', hx'K, rfl⟩ := Finset.mem_map.mp hx
      have hxAdj : G.Adj (b : V) (x' : V) := by simpa [Kb] using hx'K
      rw [SimpleGraph.mem_neighborFinset]
      exact ⟨by simpa [fQ] using hxAdj,
        Or.inl ⟨b.property, x'.val.property⟩⟩
    have hKₐcard : #Kₐ ≤ D.degree (a : V) := by
      calc
        #Kₐ = #(Kₐ.map fQ) := by simp
        _ ≤ #(D.neighborFinset (a : V)) := Finset.card_le_card hKₐmapSub
        _ = D.degree (a : V) := SimpleGraph.card_neighborFinset_eq_degree _ _
    have hKbcard : #Kb ≤ D.degree (b : V) := by
      calc
        #Kb = #(Kb.map fQ) := by simp
        _ ≤ #(D.neighborFinset (b : V)) := Finset.card_le_card hKbmapSub
        _ = D.degree (b : V) := SimpleGraph.card_neighborFinset_eq_degree _ _
    have hKcard : #K ≤ 5 := by
      have hu := Finset.card_union_le Kₐ Kb
      change #(Kₐ ∪ Kb) ≤ 5
      omega
    have habG : ¬G.Adj (a : V) (b : V) := by
      have habComp : Hᶜ.Adj a b := by simpa [M] using habM
      have habHnot : ¬H.Adj a b := habComp.2
      simpa [H] using habHnot
    have hKcover : T.IsVertexCover (K : Set (Q : Set (U : Set V))) := by
      intro x y hxyT
      by_contra hnot
      have hxNotK : x ∉ K := by
        intro hx
        exact hnot (Or.inl hx)
      have hyNotK : y ∉ K := by
        intro hy
        exact hnot (Or.inr hy)
      have hxAvoid : ¬G.Adj (a : V) (x : V) ∧
          ¬G.Adj (b : V) (x : V) := by
        simpa [K, Kₐ, Kb] using hxNotK
      have hyAvoid : ¬G.Adj (a : V) (y : V) ∧
          ¬G.Adj (b : V) (y : V) := by
        simpa [K, Kₐ, Kb] using hyNotK
      have hcNotX : c ∉ Q := by
        simpa [Q] using hcC
      have hxNotC : (x : (U : Set V)) ∉ C := by
        simpa [Q] using x.property
      have hyNotC : (y : (U : Set V)) ∉ C := by
        simpa [Q] using y.property
      have hcxG : ¬G.Adj (c : V) (x : V) := by
        have hcxR := hCisolated.2 hcC hxNotC
        simpa [R] using hcxR
      have hcyG : ¬G.Adj (c : V) (y : V) := by
        have hcyR := hCisolated.2 hcC hyNotC
        simpa [R] using hcyR
      have hxyG : ¬G.Adj (x : V) (y : V) := by
        have hxyNotInduce : ¬(R.induce (Q : Set (U : Set V))).Adj x y := hxyT.2
        simpa [R] using hxyNotInduce
      have hab : (a : V) ≠ (b : V) := fun h => habM.ne (Subtype.ext h)
      have hac : (a : V) ≠ (c : V) := fun h =>
        (Finset.disjoint_left.mp hNUdis) a.property (h ▸ c.property)
      have hax : (a : V) ≠ (x : V) := fun h =>
        (Finset.disjoint_left.mp hNUdis) a.property (h ▸ x.val.property)
      have hay : (a : V) ≠ (y : V) := fun h =>
        (Finset.disjoint_left.mp hNUdis) a.property (h ▸ y.val.property)
      have hbc : (b : V) ≠ (c : V) := fun h =>
        (Finset.disjoint_left.mp hNUdis) b.property (h ▸ c.property)
      have hbx : (b : V) ≠ (x : V) := fun h =>
        (Finset.disjoint_left.mp hNUdis) b.property (h ▸ x.val.property)
      have hby : (b : V) ≠ (y : V) := fun h =>
        (Finset.disjoint_left.mp hNUdis) b.property (h ▸ y.val.property)
      have hcx : (c : V) ≠ (x : V) := fun h =>
        hxNotC (Subtype.ext h.symm ▸ hcC)
      have hcy : (c : V) ≠ (y : V) := fun h =>
        hyNotC (Subtype.ext h.symm ▸ hcC)
      have hxy : (x : V) ≠ (y : V) := fun h =>
        hxyT.ne (Subtype.ext (Subtype.ext h))
      exact false_of_indepSetFree_five_of_pairwise_nonadj G hfree
        hab hac hax hay hbc hbx hby hcx hcy hxy habG hc₀Avoid.1
        hxAvoid.1 hyAvoid.1 hc₀Avoid.2 hxAvoid.2 hyAvoid.2 hcxG hcyG hxyG
    have hcoverUpper : T.vertexCoverNum ≤ (5 : ℕ∞) := by
      calc
        T.vertexCoverNum ≤ (K : Set (Q : Set (U : Set V))).encard :=
          hKcover.vertexCoverNum_le
        _ = (#K : ℕ∞) := by simp
        _ ≤ (5 : ℕ∞) := by exact_mod_cast hKcard
    rw [hTcoverEq] at hcoverUpper
    norm_num at hcoverUpper

/-- An admissible order-twenty-one graph with no independent five-set has at
least fifty-five edges. The degree-five endpoint exhausts the colorable and
non-colorable order-fifteen exterior branches. -/
theorem card_edges_ge_fiftyFive_of_admissible_indepSetFree_five_card_twentyOne
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 5)
    (hcard : Fintype.card V = 21) :
    55 ≤ #G.edgeFinset := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  by_contra hnot
  have hedgeUpper : #G.edgeFinset ≤ 54 := by omega
  obtain ⟨v, hmin, havg⟩ :=
    exists_minimal_vertex_card_mul_degree_le_twice_edges G
  have hdegreeCap : G.degree v ≤ 5 := by
    rw [hcard] at havg
    omega
  let U := exteriorFinset G v
  let R := G.induce (U : Set V)
  have hUcard := card_exterior_type_add_degree_add_one G v
  rw [hcard] at hUcard
  have hUcardU : Fintype.card (U : Set V) + G.degree v + 1 = 21 := by
    simpa [U] using hUcard
  have hRadmissible : Admissible R := by
    simpa [R] using admissible_induce G hG U
  have hRfree : R.IndepSetFree 4 := by
    simpa [R, U] using
      (indepSetFree_exterior_induce G (k := 4) (by simpa using hfree) v)
  have hsplit := exterior_edges_add_degree_add_choose_le_edges G v hmin
  have hsplitR : #R.edgeFinset + G.degree v + (G.degree v).choose 2 ≤
      #G.edgeFinset := by simpa [R, U] using hsplit
  interval_cases hdegree : G.degree v
  · have hRcard : Fintype.card (U : Set V) = 20 := by omega
    have hRbound :=
      card_edges_ge_sixtyTwo_of_admissible_indepSetFree_four_card_twenty
        R hRadmissible hRfree hRcard
    omega
  · have hRcard : Fintype.card (U : Set V) = 19 := by omega
    have hRbound :=
      card_edges_ge_fiftySix_of_admissible_indepSetFree_four_card_nineteen
        R hRadmissible hRfree hRcard
    norm_num [hdegree, Nat.choose] at hsplitR
    omega
  · have hRcard : Fintype.card (U : Set V) = 18 := by omega
    have hRbound :=
      card_edges_ge_fiftyFour_of_admissible_indepSetFree_four_card_eighteen
        R hRadmissible hRfree hRcard
    norm_num [hdegree, Nat.choose] at hsplitR
    omega
  · have hRcard : Fintype.card (U : Set V) = 17 := by omega
    have hRbound :=
      card_edges_ge_fifty_of_admissible_indepSetFree_four_card_seventeen
        R hRadmissible hRfree hRcard
    norm_num [hdegree, Nat.choose] at hsplitR
    omega
  · have hRcard : Fintype.card (U : Set V) = 16 := by omega
    have hRbound :=
      card_edges_ge_fortyFive_of_admissible_indepSetFree_four_card_sixteen
        R hRadmissible hRfree hRcard
    norm_num [hdegree, Nat.choose] at hsplitR
    omega
  · by_cases hcolor : Rᶜ.Colorable 3
    · exact false_of_colorable_compl_exterior_degree_five_card_twentyOne
        G hG hfree hcard v hdegree (by simpa [R, U] using hcolor)
    · exact false_of_not_colorable_compl_exterior_degree_five_card_twentyOne
        G hG hfree hcard hedgeUpper v hdegree
          (fun w => by simpa [hdegree] using hmin w)
          (by simpa [R, U] using hcolor)

/-- Exact graph-theoretic form of the three small independence-four
obstructions: none of the manuscript's three order/edge ranges is possible. -/
theorem false_of_admissible_indepSetFree_five_small_range
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 5)
    (hrange :
      (Fintype.card V = 23 ∧ #G.edgeFinset ≤ 61) ∨
      (Fintype.card V = 22 ∧ #G.edgeFinset ≤ 58) ∨
      (Fintype.card V = 21 ∧ #G.edgeFinset ≤ 54)) :
    False := by
  rcases hrange with h23 | h22 | h21
  · have hlower :=
      card_edges_ge_sixtyTwo_of_admissible_indepSetFree_five_card_twentyThree
        G hG hfree h23.1
    omega
  · have hlower :=
      card_edges_ge_fiftyNine_of_admissible_indepSetFree_five_card_twentyTwo
        G hG hfree h22.1
    omega
  · have hlower :=
      card_edges_ge_fiftyFive_of_admissible_indepSetFree_five_card_twentyOne
        G hG hfree h21.1
    omega

end Erdos617
