/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.AlphaTwoLarge
public import Mathlib.Tactic.IntervalCases

/-!
# Propagating admissible independence bounds

This module proves the induced-subgraph and edge-partition bridges needed to
propagate the large independence-two estimate through a minimum-degree
decomposition.  It then derives the large admissible independence-three and
independence-four numerical bounds used in the fixed-`r = 5` argument without
Kang--Pikhurko or a solver.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

universe u

/-- The edges of a graph split into those inside a finite set, those crossing
to its complement, and those inside the complement. -/
theorem card_edgeFinset_eq_induce_add_between_add_induce_compl
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    #G.edgeFinset =
      #(G.induce (S : Set V)).edgeFinset +
        #(G.between (S : Set V) ((Sᶜ : Finset V) : Set V)).edgeFinset +
          #(G.induce ((Sᶜ : Finset V) : Set V)).edgeFinset := by
  let T : Finset V := Sᶜ
  let GI := G.between (S : Set V) (S : Set V)
  let GC := G.between (S : Set V) (T : Set V)
  let GO := G.between (T : Set V) (T : Set V)
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    simp [T, hxS] at hxT
  have hparts : G = GI ⊔ GC ⊔ GO := by
    ext a b
    simp only [SimpleGraph.sup_adj, SimpleGraph.between_adj, GI, GC, GO]
    constructor
    · intro hab
      by_cases haS : a ∈ S
      · by_cases hbS : b ∈ S
        · exact Or.inl (Or.inl ⟨hab, Or.inl ⟨haS, hbS⟩⟩)
        · have hbT : b ∈ T := by simpa [T] using hbS
          exact Or.inl (Or.inr ⟨hab, Or.inl ⟨haS, hbT⟩⟩)
      · have haT : a ∈ T := by simpa [T] using haS
        by_cases hbS : b ∈ S
        · exact Or.inl (Or.inr ⟨hab, Or.inr ⟨haT, hbS⟩⟩)
        · have hbT : b ∈ T := by simpa [T] using hbS
          exact Or.inr ⟨hab, Or.inl ⟨haT, hbT⟩⟩
    · rintro ((⟨hab, _⟩ | ⟨hab, _⟩) | ⟨hab, _⟩)
      · exact hab
      · exact hab
      · exact hab
  have hIC : Disjoint GI GC := by
    rw [SimpleGraph.disjoint_left]
    intro a b habI habC
    have hi := (SimpleGraph.between_adj.mp habI).2
    have hc := (SimpleGraph.between_adj.mp habC).2
    rcases hi with ⟨haS, hbS⟩ | ⟨haS, hbS⟩ <;>
      rcases hc with ⟨haS', hbT⟩ | ⟨haT, hbS'⟩
    · exact (Finset.disjoint_left.mp hST) hbS hbT
    · exact (Finset.disjoint_left.mp hST) haS haT
    · exact (Finset.disjoint_left.mp hST) hbS hbT
    · exact (Finset.disjoint_left.mp hST) haS haT
  have hIO : Disjoint GI GO := by
    rw [SimpleGraph.disjoint_left]
    intro a b habI habO
    have hi := (SimpleGraph.between_adj.mp habI).2
    have ho := (SimpleGraph.between_adj.mp habO).2
    rcases hi with ⟨haS, _⟩ | ⟨haS, _⟩ <;>
      rcases ho with ⟨haT, _⟩ | ⟨haT, _⟩ <;>
      exact (Finset.disjoint_left.mp hST) haS haT
  have hCO : Disjoint GC GO := by
    rw [SimpleGraph.disjoint_left]
    intro a b habC habO
    have hc := (SimpleGraph.between_adj.mp habC).2
    have ho := (SimpleGraph.between_adj.mp habO).2
    rcases hc with ⟨haS, _⟩ | ⟨_, hbS⟩
    · rcases ho with ⟨haT, _⟩ | ⟨haT, _⟩ <;>
        exact (Finset.disjoint_left.mp hST) haS haT
    · rcases ho with ⟨_, hbT⟩ | ⟨_, hbT⟩ <;>
        exact (Finset.disjoint_left.mp hST) hbS hbT
  have hdisLeft : Disjoint (GI ⊔ GC) GO :=
    disjoint_sup_left.mpr ⟨hIO, hCO⟩
  have hcardParts :
      #G.edgeFinset = #GI.edgeFinset + #GC.edgeFinset + #GO.edgeFinset := by
    calc
      #G.edgeFinset = #(GI ⊔ GC ⊔ GO).edgeFinset :=
        congrArg Finset.card (SimpleGraph.edgeFinset_inj.mpr hparts)
      _ = #(GI ⊔ GC).edgeFinset + #GO.edgeFinset := by
        rw [SimpleGraph.edgeFinset_sup,
          Finset.card_union_of_disjoint
            (SimpleGraph.disjoint_edgeFinset.mpr hdisLeft)]
      _ = #GI.edgeFinset + #GC.edgeFinset + #GO.edgeFinset := by
        rw [SimpleGraph.edgeFinset_sup,
          Finset.card_union_of_disjoint
            (SimpleGraph.disjoint_edgeFinset.mpr hIC)]
  have hGI := card_between_self_eq_card_induce G S
  have hGO := card_between_self_eq_card_induce G T
  simpa [T, GI, GC, GO, hGI, hGO] using hcardParts

/-- Admissibility is inherited by every induced subgraph. -/
theorem admissible_induce
    {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (S : Finset V) :
    Admissible (G.induce (S : Set V)) := by
  classical
  intro T hT
  let f : (S : Set V) ↪ V := Function.Embedding.subtype _
  let T0 : Finset V := T.map f
  have hT0 : #T0 = 6 := by simpa [T0] using hT
  have hbound := hG T0 hT0
  have hset : (T0 : Set V) = Subtype.val '' (T : Set (S : Set V)) := by
    simp [T0, f]
  let e := (Equiv.Set.image (fun x : (S : Set V) => (x : V))
    (T : Set (S : Set V)) Subtype.val_injective).trans
      (Equiv.setCongr hset.symm)
  let iso :
      (G.induce (S : Set V)).induce (T : Set (S : Set V)) ≃g
        G.induce (T0 : Set V) := {
    toEquiv := e
    map_rel_iff' := by
      intro a b
      rfl
  }
  have hedge := iso.card_edgeFinset_eq
  rw [hedge]
  exact hbound

/-- In the closed-neighborhood partition, the crossing graph is exactly the
usual neighborhood-to-exterior graph: the center has no exterior neighbors. -/
theorem between_closedNeighborhood_exterior_eq_between_neighbor_exterior
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.between (insert v (G.neighborFinset v) : Finset V)
        (exteriorFinset G v : Set V) =
      G.between (G.neighborFinset v : Set V)
        (exteriorFinset G v : Set V) := by
  ext a b
  rw [SimpleGraph.between_adj, SimpleGraph.between_adj]
  constructor
  · rintro ⟨hab, hparts⟩
    refine ⟨hab, ?_⟩
    rcases hparts with ⟨haS, hbU⟩ | ⟨haU, hbS⟩
    · rcases Finset.mem_insert.mp haS with hav | haN
      · subst a
        have hbU' : ¬G.Adj v b ∧ b ≠ v := by
          simpa [exteriorFinset] using hbU
        exact (hbU'.1 hab).elim
      · exact Or.inl ⟨haN, hbU⟩
    · rcases Finset.mem_insert.mp hbS with hbv | hbN
      · subst b
        have haU' : ¬G.Adj v a ∧ a ≠ v := by
          simpa [exteriorFinset] using haU
        exact (haU'.1 hab.symm).elim
      · exact Or.inr ⟨haU, hbN⟩
  · rintro ⟨hab, hparts⟩
    refine ⟨hab, ?_⟩
    rcases hparts with ⟨haN, hbU⟩ | ⟨haU, hbN⟩
    · exact Or.inl ⟨Finset.mem_insert_of_mem haN, hbU⟩
    · exact Or.inr ⟨haU, Finset.mem_insert_of_mem hbN⟩

/-- Edges in the exterior, the center star, and the two neighborhood
accounting terms are disjoint contributions to the whole graph. -/
theorem exterior_edges_add_degree_add_accounting_le_edges
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    #(G.induce (exteriorFinset G v : Set V)).edgeFinset + G.degree v +
        (neighborhoodCrossEdgeCount G v +
          neighborhoodInternalEdgeCount G v) ≤
      #G.edgeFinset := by
  let S : Finset V := insert v (G.neighborFinset v)
  let U : Finset V := exteriorFinset G v
  have hpartition :=
    card_edgeFinset_eq_induce_add_between_add_induce_compl G S
  have hU : U = Sᶜ := by rfl
  have hcrossGraph :
      G.between (S : Set V) (U : Set V) =
        G.between (G.neighborFinset v : Set V) (U : Set V) := by
    simpa [S, U] using
      between_closedNeighborhood_exterior_eq_between_neighbor_exterior G v
  have hcrossCard :
      #(G.between (S : Set V) (U : Set V)).edgeFinset =
        #(G.between (G.neighborFinset v : Set V) (U : Set V)).edgeFinset :=
    congrArg Finset.card (SimpleGraph.edgeFinset_inj.mpr hcrossGraph)
  have hclosed := degree_add_internal_le_closedNeighborhood G v
  rw [← hU, hcrossCard] at hpartition
  dsimp [S, U, neighborhoodCrossEdgeCount,
    neighborhoodInternalEdgeCount] at hpartition hclosed ⊢
  omega

/-- Passing to the nonneighbors of a vertex lowers the forbidden independent
set size by one: adjoining the center would lift any exterior witness. -/
theorem indepSetFree_exterior_induce
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hfree : G.IndepSetFree (k + 1)) (v : V) :
    (G.induce (exteriorFinset G v : Set V)).IndepSetFree k := by
  classical
  intro T hT
  let U := exteriorFinset G v
  let f : (U : Set V) ↪ V := Function.Embedding.subtype _
  let T0 : Finset V := T.map f
  have hT0 : G.IsNIndepSet k T0 := by
    constructor
    · intro a ha b hb hab
      obtain ⟨aU, haT, rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨bU, hbT, rfl⟩ := Finset.mem_map.mp hb
      exact hT.isIndepSet haT hbT (fun h => hab (congrArg f h))
    · simpa [T0] using hT.card_eq
  have hT0U : ∀ x ∈ T0, x ∈ U := by
    intro x hx
    obtain ⟨y, hyT, hyx⟩ := Finset.mem_map.mp hx
    rw [← hyx]
    exact y.property
  have hvNot : v ∉ T0 := by
    intro hv
    have hvU := hT0U v hv
    simp [U, exteriorFinset] at hvU
  apply hfree (insert v T0)
  constructor
  · intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hav | haT
    · subst a
      rcases Finset.mem_insert.mp hb with hbv | hbT
      · exact (hab hbv.symm).elim
      · have hbU := hT0U b hbT
        have hbU' : b ≠ v ∧ ¬G.Adj v b := by
          simpa [U, exteriorFinset] using hbU
        exact hbU'.2
    · rcases Finset.mem_insert.mp hb with hbv | hbT
      · subst b
        have haU := hT0U a haT
        intro hav
        have haU' : a ≠ v ∧ ¬G.Adj v a := by
          simpa [U, exteriorFinset] using haU
        exact haU'.2 hav.symm
      · exact hT0.isIndepSet haT hbT hab
  · rw [Finset.card_insert_of_notMem hvNot]
    have hcard := hT0.card_eq
    omega

/-- A nonempty finite graph has a minimum-degree vertex whose degree obeys
the average-degree inequality in subtraction-free form. -/
theorem exists_minimal_vertex_card_mul_degree_le_twice_edges
    {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ v : V, (∀ w, G.degree v ≤ G.degree w) ∧
      Fintype.card V * G.degree v ≤ 2 * #G.edgeFinset := by
  obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  have hmin : ∀ w, G.degree v ≤ G.degree w := by
    intro w
    rw [← hv]
    exact G.minDegree_le_degree w
  have hsumLower :
      Fintype.card V * G.degree v ≤ ∑ w, G.degree w := by
    calc
      Fintype.card V * G.degree v = ∑ _w : V, G.degree v := by
        simp
      _ ≤ ∑ w, G.degree w :=
        Finset.sum_le_sum fun w _ => hmin w
  rw [G.sum_degrees_eq_twice_card_edges] at hsumLower
  exact ⟨v, hmin, hsumLower⟩

/-- Cardinality of the nonneighbors outside a vertex's closed neighborhood. -/
theorem card_exteriorFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    #(exteriorFinset G v) =
      Fintype.card V - (G.degree v + 1) := by
  change #((insert v (G.neighborFinset v))ᶜ) = _
  rw [Finset.card_compl,
    Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v),
    SimpleGraph.card_neighborFinset_eq_degree]

/-- Subtype cardinality form of `card_exteriorFinset`, with the closed
neighborhood added back. -/
theorem card_exterior_type_add_degree_add_one
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Fintype.card (exteriorFinset G v : Set V) + G.degree v + 1 =
      Fintype.card V := by
  have hcoe : Fintype.card (exteriorFinset G v : Set V) =
      #(exteriorFinset G v) := by simp
  rw [hcoe]
  have hcard := card_exteriorFinset G v
  have hdegree := G.degree_lt_card_verts v
  omega

/-- Basic minimum-degree propagation: the exterior edge count, the center
degree, and `choose degree 2` fit inside the full edge count. -/
theorem exterior_edges_add_degree_add_choose_le_edges
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hmin : ∀ w, G.degree v ≤ G.degree w) :
    #(G.induce (exteriorFinset G v : Set V)).edgeFinset + G.degree v +
        (G.degree v).choose 2 ≤ #G.edgeFinset := by
  have hsplit := exterior_edges_add_degree_add_accounting_le_edges G v
  have haccount :=
    neighborhood_cross_add_internal_ge_choose_degree G v hmin
  omega

/-- At degree five, admissibility strengthens the propagated accounting
contribution from ten to fourteen. -/
theorem exterior_edges_add_nineteen_le_edges_of_admissible_degree_five
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : Admissible G)
    (v : V) (hdegree : G.degree v = 5)
    (hmin : ∀ w, G.degree v ≤ G.degree w) :
    #(G.induce (exteriorFinset G v : Set V)).edgeFinset + 19 ≤
      #G.edgeFinset := by
  have hsplit := exterior_edges_add_degree_add_accounting_le_edges G v
  have haccount := neighborhood_cross_add_internal_ge_fourteen
    G hG v hdegree hmin
  omega

/-- Numerical propagation from the large independence-two terminal theorem to
an admissible graph with no independent four-set.  The three arithmetic
hypotheses isolate the finite endpoint calculation from the graph argument. -/
theorem card_edges_ge_of_admissible_indepSetFree_four
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    {n lower degreeCap : ℕ} (hcard : Fintype.card V = n)
    (hlower : 0 < lower)
    (hcap : ∀ d, n * d < 2 * lower → d ≤ degreeCap)
    (hlarge : ∀ d, d ≤ degreeCap → 12 + d + 1 ≤ n)
    (harith : ∀ d exteriorOrder, d ≤ degreeCap →
      exteriorOrder + d + 1 = n →
      lower + 2 * exteriorOrder ≤
        exteriorOrder.choose 2 + d + d.choose 2) :
    lower ≤ #G.edgeFinset := by
  classical
  have hnpos : 0 < Fintype.card V := by
    have hcapZero := hcap 0 (by simpa using hlower)
    have hlargeZero := hlarge 0 hcapZero
    rw [← hcard] at hlargeZero
    omega
  letI : Nonempty V := Fintype.card_pos_iff.mp hnpos
  by_contra hnot
  have hedgeLt : #G.edgeFinset < lower := by omega
  obtain ⟨v, hmin, havg⟩ :=
    exists_minimal_vertex_card_mul_degree_le_twice_edges G
  have hdegreeProduct : n * G.degree v < 2 * lower := by
    rw [hcard] at havg
    omega
  have hdegreeCap : G.degree v ≤ degreeCap :=
    hcap (G.degree v) hdegreeProduct
  let U := exteriorFinset G v
  let R := G.induce (U : Set V)
  have hUcardRaw := card_exteriorFinset G v
  have hdegreeCard := G.degree_lt_card_verts v
  have hUcoe : Fintype.card (U : Set V) = #U := by simp
  have hUcard : Fintype.card (U : Set V) + G.degree v + 1 = n := by
    rw [hUcoe]
    rw [hcard] at hUcardRaw hdegreeCard
    have hUcardRaw' : #U = n - (G.degree v + 1) := by
      simpa [U] using hUcardRaw
    omega
  have hUlarge : 12 ≤ Fintype.card (U : Set V) := by
    have := hlarge (G.degree v) hdegreeCap
    omega
  have hRadmissible : Admissible R := by
    simpa [R] using admissible_induce G hG U
  have hRfree : R.IndepSetFree 3 := by
    simpa [R, U] using
      (indepSetFree_exterior_induce G (k := 3) (by simpa using hfree) v)
  have hterminal :=
    choose_card_le_edges_add_twice_card_of_admissible_indepSetFree_three
      R hRadmissible hRfree hUlarge
  have hsplit := exterior_edges_add_degree_add_choose_le_edges G v hmin
  have hnumeric := harith (G.degree v) (Fintype.card (U : Set V))
    hdegreeCap hUcard
  dsimp [R, U] at hUcard hUlarge hterminal hsplit hnumeric
  omega

/-- Admissible order-18 graphs with independence number at most three have at
least 54 edges. -/
theorem card_edges_ge_fiftyFour_of_admissible_indepSetFree_four_card_eighteen
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (hcard : Fintype.card V = 18) :
    54 ≤ #G.edgeFinset := by
  apply card_edges_ge_of_admissible_indepSetFree_four G hG hfree
    (n := 18) (lower := 54) (degreeCap := 5) hcard (by norm_num)
  · intro d hd
    norm_num at hd ⊢
    omega
  · intro d hd
    omega
  · intro d exteriorOrder hd horder
    have hExteriorOrder : exteriorOrder ≤ 18 := by omega
    interval_cases d <;>
      interval_cases exteriorOrder <;>
      norm_num [Nat.choose] at *

/-- The first large manuscript specialization, now under the admissibility
hypothesis actually available for every color graph. -/
theorem card_edges_ge_fiftySix_of_admissible_indepSetFree_four_card_nineteen
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (hcard : Fintype.card V = 19) :
    56 ≤ #G.edgeFinset := by
  apply card_edges_ge_of_admissible_indepSetFree_four G hG hfree
    (n := 19) (lower := 56) (degreeCap := 5) hcard (by norm_num)
  · intro d hd
    norm_num at hd ⊢
    omega
  · intro d hd
    omega
  · intro d exteriorOrder hd horder
    have hExteriorOrder : exteriorOrder ≤ 19 := by omega
    interval_cases d <;>
      interval_cases exteriorOrder <;>
      norm_num [Nat.choose] at *

/-- The order-20 admissible independence-three bound. -/
theorem card_edges_ge_sixtyTwo_of_admissible_indepSetFree_four_card_twenty
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (hcard : Fintype.card V = 20) :
    62 ≤ #G.edgeFinset := by
  apply card_edges_ge_of_admissible_indepSetFree_four G hG hfree
    (n := 20) (lower := 62) (degreeCap := 6) hcard (by norm_num)
  · intro d hd
    norm_num at hd ⊢
    omega
  · intro d hd
    omega
  · intro d exteriorOrder hd horder
    have hExteriorOrder : exteriorOrder ≤ 20 := by omega
    interval_cases d <;>
      interval_cases exteriorOrder <;>
      norm_num [Nat.choose] at *

/-- The order-21 admissible independence-three bound. -/
theorem card_edges_ge_sixtyNine_of_admissible_indepSetFree_four_card_twentyOne
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (hcard : Fintype.card V = 21) :
    69 ≤ #G.edgeFinset := by
  apply card_edges_ge_of_admissible_indepSetFree_four G hG hfree
    (n := 21) (lower := 69) (degreeCap := 6) hcard (by norm_num)
  · intro d hd
    norm_num at hd ⊢
    omega
  · intro d hd
    omega
  · intro d exteriorOrder hd horder
    have hExteriorOrder : exteriorOrder ≤ 21 := by omega
    interval_cases d <;>
      interval_cases exteriorOrder <;>
      norm_num [Nat.choose] at *

/-- The order-22 admissible independence-three bound. -/
theorem card_edges_ge_seventySix_of_admissible_indepSetFree_four_card_twentyTwo
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (hcard : Fintype.card V = 22) :
    76 ≤ #G.edgeFinset := by
  apply card_edges_ge_of_admissible_indepSetFree_four G hG hfree
    (n := 22) (lower := 76) (degreeCap := 6) hcard (by norm_num)
  · intro d hd
    norm_num at hd ⊢
    omega
  · intro d hd
    omega
  · intro d exteriorOrder hd horder
    have hExteriorOrder : exteriorOrder ≤ 22 := by omega
    interval_cases d <;>
      interval_cases exteriorOrder <;>
      norm_num [Nat.choose] at *

/-- A stronger auxiliary order-23 bound used one level later. -/
theorem card_edges_ge_eightyThree_of_admissible_indepSetFree_four_card_twentyThree
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (hcard : Fintype.card V = 23) :
    83 ≤ #G.edgeFinset := by
  apply card_edges_ge_of_admissible_indepSetFree_four G hG hfree
    (n := 23) (lower := 83) (degreeCap := 7) hcard (by norm_num)
  · intro d hd
    norm_num at hd ⊢
    omega
  · intro d hd
    omega
  · intro d exteriorOrder hd horder
    have hExteriorOrder : exteriorOrder ≤ 23 := by omega
    interval_cases d <;>
      interval_cases exteriorOrder <;>
      norm_num [Nat.choose] at *

/-- A stronger auxiliary order-24 bound used one level later. -/
theorem card_edges_ge_ninety_of_admissible_indepSetFree_four_card_twentyFour
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (hcard : Fintype.card V = 24) :
    90 ≤ #G.edgeFinset := by
  apply card_edges_ge_of_admissible_indepSetFree_four G hG hfree
    (n := 24) (lower := 90) (degreeCap := 7) hcard (by norm_num)
  · intro d hd
    norm_num at hd ⊢
    omega
  · intro d hd
    omega
  · intro d exteriorOrder hd horder
    have hExteriorOrder : exteriorOrder ≤ 24 := by omega
    interval_cases d <;>
      interval_cases exteriorOrder <;>
      norm_num [Nat.choose] at *

/-- The order-24 independence-four specialization needed by the initial
minimum-degree reduction, derived only from admissibility and the preceding
independence-three bounds. -/
theorem card_edges_ge_sixtyFive_of_admissible_indepSetFree_five_card_twentyFour
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 5)
    (hcard : Fintype.card V = 24) :
    65 ≤ #G.edgeFinset := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  by_contra hnot
  have hedgeLt : #G.edgeFinset < 65 := by omega
  obtain ⟨v, hmin, havg⟩ :=
    exists_minimal_vertex_card_mul_degree_le_twice_edges G
  have hdegreeCap : G.degree v ≤ 5 := by
    rw [hcard] at havg
    omega
  let U := exteriorFinset G v
  let R := G.induce (U : Set V)
  have hUcard := card_exterior_type_add_degree_add_one G v
  rw [hcard] at hUcard
  have hUcardU : Fintype.card (U : Set V) + G.degree v + 1 = 24 := by
    simpa [U] using hUcard
  have hRadmissible : Admissible R := by
    simpa [R] using admissible_induce G hG U
  have hRfree : R.IndepSetFree 4 := by
    simpa [R, U] using
      (indepSetFree_exterior_induce G (k := 4) (by simpa using hfree) v)
  have hsplit := exterior_edges_add_degree_add_choose_le_edges G v hmin
  have hsplitR : #R.edgeFinset + G.degree v + (G.degree v).choose 2 ≤
      #G.edgeFinset := by
    simpa [R, U] using hsplit
  interval_cases hdegree : G.degree v
  · have hRcard : Fintype.card (U : Set V) = 23 := by omega
    have hRbound :=
      card_edges_ge_eightyThree_of_admissible_indepSetFree_four_card_twentyThree
        R hRadmissible hRfree hRcard
    have hRbound' : 83 ≤ #R.edgeFinset := hRbound
    norm_num [hdegree, Nat.choose] at hsplitR
    omega
  · have hRcard : Fintype.card (U : Set V) = 22 := by omega
    have hRbound :=
      card_edges_ge_seventySix_of_admissible_indepSetFree_four_card_twentyTwo
        R hRadmissible hRfree hRcard
    norm_num [hdegree, Nat.choose] at hsplitR
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

/-- The order-25 independence-four specialization used to rule out an
isolated vertex in a least color graph. -/
theorem card_edges_ge_seventyOne_of_admissible_indepSetFree_five_card_twentyFive
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 5)
    (hcard : Fintype.card V = 25) :
    71 ≤ #G.edgeFinset := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  by_contra hnot
  have hedgeLt : #G.edgeFinset < 71 := by omega
  obtain ⟨v, hmin, havg⟩ :=
    exists_minimal_vertex_card_mul_degree_le_twice_edges G
  have hdegreeCap : G.degree v ≤ 5 := by
    rw [hcard] at havg
    omega
  let U := exteriorFinset G v
  let R := G.induce (U : Set V)
  have hUcard := card_exterior_type_add_degree_add_one G v
  rw [hcard] at hUcard
  have hUcardU : Fintype.card (U : Set V) + G.degree v + 1 = 25 := by
    simpa [U] using hUcard
  have hRadmissible : Admissible R := by
    simpa [R] using admissible_induce G hG U
  have hRfree : R.IndepSetFree 4 := by
    simpa [R, U] using
      (indepSetFree_exterior_induce G (k := 4) (by simpa using hfree) v)
  have hsplit := exterior_edges_add_degree_add_choose_le_edges G v hmin
  have hsplitR : #R.edgeFinset + G.degree v + (G.degree v).choose 2 ≤
      #G.edgeFinset := by
    simpa [R, U] using hsplit
  interval_cases hdegree : G.degree v
  · have hRcard : Fintype.card (U : Set V) = 24 := by omega
    have hRbound :=
      card_edges_ge_ninety_of_admissible_indepSetFree_four_card_twentyFour
        R hRadmissible hRfree hRcard
    norm_num [hdegree, Nat.choose] at hsplitR
    omega
  · have hRcard : Fintype.card (U : Set V) = 23 := by omega
    have hRbound :=
      card_edges_ge_eightyThree_of_admissible_indepSetFree_four_card_twentyThree
        R hRadmissible hRfree hRcard
    norm_num [hdegree, Nat.choose] at hsplitR
    omega
  · have hRcard : Fintype.card (U : Set V) = 22 := by omega
    have hRbound :=
      card_edges_ge_seventySix_of_admissible_indepSetFree_four_card_twentyTwo
        R hRadmissible hRfree hRcard
    norm_num [hdegree, Nat.choose] at hsplitR
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

end Erdos617
