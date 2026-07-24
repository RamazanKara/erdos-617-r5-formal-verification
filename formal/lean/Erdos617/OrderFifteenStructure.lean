/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.AlphaThreeSmall

/-!
# Near-extremal structure on fifteen vertices

This module formalizes the two order-fifteen classifications used by the
fixed-`r = 5` independence-four and equality-recursion arguments.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

universe u

/-- The induced closed neighborhood consists exactly of the center star and
the graph internal to the open neighborhood. -/
theorem card_induce_closedNeighborhood_eq_degree_add_internal
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    #(G.induce (insert v (G.neighborFinset v) : Finset V)).edgeFinset =
      G.degree v + neighborhoodInternalEdgeCount G v := by
  classical
  let N := G.neighborFinset v
  let S := insert v N
  let V0 : Finset V := {v}
  let Star := G.between (V0 : Set V) (N : Set V)
  let Inside := neighborhoodInternalGraph G v
  let J := Star ⊔ Inside
  let K := G.between (S : Set V) (S : Set V)
  have hvN : v ∉ N := G.notMem_neighborFinset_self v
  have hdisVNFin : Disjoint V0 N :=
    Finset.disjoint_singleton_left.mpr hvN
  have hdisVNSet : Disjoint (V0 : Set V) (N : Set V) :=
    Finset.disjoint_coe.mpr hdisVNFin
  have hstarBip : Star.IsBipartiteWith (V0 : Set V) (N : Set V) :=
    SimpleGraph.between_isBipartiteWith hdisVNSet
  have hstarSum : (∑ a ∈ V0, Star.degree a) = #Star.edgeFinset :=
    SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hstarBip
  have hstarNeighbors : Star.neighborFinset v = G.neighborFinset v := by
    ext w
    simp [Star, V0, SimpleGraph.between_adj, N]
  have hstarDegree : Star.degree v = G.degree v := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree, hstarNeighbors]
  have hstarCard : #Star.edgeFinset = G.degree v := by
    simpa [V0, hstarDegree] using hstarSum.symm
  have hdisGraphs : Disjoint Star Inside := by
    rw [SimpleGraph.disjoint_left]
    intro a b habStar habInside
    have hstarParts := (SimpleGraph.between_adj.mp habStar).2
    have hinParts := (SimpleGraph.between_adj.mp habInside).2
    rcases hinParts with ⟨haN, hbN⟩ | ⟨haN, hbN⟩ <;>
      rcases hstarParts with ⟨haV, _⟩ | ⟨_, hbV⟩
    · have haEq : a = v := by simpa [V0] using haV
      exact hvN (haEq ▸ haN)
    · have hbEq : b = v := by simpa [V0] using hbV
      exact hvN (hbEq ▸ hbN)
    · have haEq : a = v := by simpa [V0] using haV
      exact hvN (haEq ▸ haN)
    · have hbEq : b = v := by simpa [V0] using hbV
      exact hvN (hbEq ▸ hbN)
  have hJcard : #J.edgeFinset = #Star.edgeFinset + #Inside.edgeFinset := by
    change #(Star ⊔ Inside).edgeFinset = _
    rw [SimpleGraph.edgeFinset_sup,
      Finset.card_union_of_disjoint
        (SimpleGraph.disjoint_edgeFinset.mpr hdisGraphs)]
  have hJK : J = K := by
    apply le_antisymm
    · apply sup_le
      · intro a b hab
        have hparts := SimpleGraph.between_adj.mp hab
        rcases hparts.2 with ⟨haV, hbN⟩ | ⟨haN, hbV⟩
        · have haS : a ∈ S := by
            exact Finset.mem_insert.mpr (Or.inl (by simpa [V0] using haV))
          exact SimpleGraph.between_adj.mpr
            ⟨hparts.1, Or.inl ⟨haS, Finset.mem_insert_of_mem hbN⟩⟩
        · have hbS : b ∈ S := by
            exact Finset.mem_insert.mpr (Or.inl (by simpa [V0] using hbV))
          exact SimpleGraph.between_adj.mpr
            ⟨hparts.1, Or.inl ⟨Finset.mem_insert_of_mem haN, hbS⟩⟩
      · intro a b hab
        have hparts := SimpleGraph.between_adj.mp hab
        rcases hparts.2 with ⟨haN, hbN⟩ | ⟨haN, hbN⟩
        · exact SimpleGraph.between_adj.mpr
            ⟨hparts.1, Or.inl
              ⟨Finset.mem_insert_of_mem haN, Finset.mem_insert_of_mem hbN⟩⟩
        · exact SimpleGraph.between_adj.mpr
            ⟨hparts.1, Or.inl
              ⟨Finset.mem_insert_of_mem haN, Finset.mem_insert_of_mem hbN⟩⟩
    · intro a b hab
      have hparts := SimpleGraph.between_adj.mp hab
      have haS : a ∈ S := hparts.2.elim And.left And.left
      have hbS : b ∈ S := hparts.2.elim And.right And.right
      rcases Finset.mem_insert.mp haS with hav | haN
      · subst a
        have hbN : b ∈ N := by simpa [N] using hparts.1
        change Star.Adj v b ∨ Inside.Adj v b
        exact Or.inl ⟨hparts.1, Or.inl ⟨by simp [V0], hbN⟩⟩
      · rcases Finset.mem_insert.mp hbS with hbv | hbN
        · subst b
          have haNv : a ∈ N := haN
          change Star.Adj a v ∨ Inside.Adj a v
          exact Or.inl ⟨hparts.1, Or.inr ⟨haNv, by simp [V0]⟩⟩
        · change Star.Adj a b ∨ Inside.Adj a b
          exact Or.inr ⟨hparts.1, Or.inl ⟨haN, hbN⟩⟩
  have hKcard : #K.edgeFinset =
      #(G.induce (S : Set V)).edgeFinset := by
    simpa [K] using card_between_self_eq_card_induce G S
  have hJKcard : #J.edgeFinset = #K.edgeFinset :=
    congrArg Finset.card (SimpleGraph.edgeFinset_inj.mpr hJK)
  calc
    #(G.induce (insert v (G.neighborFinset v) : Finset V)).edgeFinset =
        #K.edgeFinset := by simpa [S] using hKcard.symm
    _ = #J.edgeFinset := hJKcard.symm
    _ = #Star.edgeFinset + #Inside.edgeFinset := hJcard
    _ = G.degree v + neighborhoodInternalEdgeCount G v := by
      simp [hstarCard, Inside, neighborhoodInternalEdgeCount]

/-- Exact version of the exterior accounting identity. -/
theorem card_edges_eq_exterior_add_degree_add_accounting
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    #(G.induce (exteriorFinset G v : Set V)).edgeFinset + G.degree v +
        (neighborhoodCrossEdgeCount G v +
          neighborhoodInternalEdgeCount G v) = #G.edgeFinset := by
  classical
  let S : Finset V := insert v (G.neighborFinset v)
  let U : Finset V := exteriorFinset G v
  have hpartition := card_edgeFinset_eq_induce_add_between_add_induce_compl G S
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
  have hclosed := card_induce_closedNeighborhood_eq_degree_add_internal G v
  rw [← hU, hcrossCard, hclosed] at hpartition
  dsimp [S, U, neighborhoodCrossEdgeCount,
    neighborhoodInternalEdgeCount] at hpartition ⊢
  omega

/-- Three cliques covering a graph's vertices give a three-coloring of its
complement. The cliques need not be disjoint. -/
theorem compl_colorable_three_of_three_clique_cover
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B C : Finset V)
    (hcover : (A ∪ B) ∪ C = Finset.univ)
    (hA : G.IsClique (A : Set V))
    (hB : G.IsClique (B : Set V))
    (hC : G.IsClique (C : Set V)) :
    Gᶜ.Colorable 3 := by
  classical
  let color : V → Fin 3 := fun x =>
    if x ∈ A then 0 else if x ∈ B then 1 else 2
  refine ⟨SimpleGraph.Coloring.mk color ?_⟩
  intro x y hxy hsame
  have hxyne : x ≠ y := hxy.1
  have hnotG : ¬G.Adj x y := hxy.2
  by_cases hxA : x ∈ A
  · have hyA : y ∈ A := by
      by_contra hyA
      simp [color, hxA, hyA] at hsame
      split at hsame <;> simp_all
    exact hnotG (hA hxA hyA hxyne)
  · by_cases hxB : x ∈ B
    · have hyNotA : y ∉ A := by
        intro hyA
        simp [color, hxA, hxB, hyA] at hsame
      have hyB : y ∈ B := by
        by_contra hyB
        simp [color, hxA, hxB, hyNotA, hyB] at hsame
      exact hnotG (hB hxB hyB hxyne)
    · have hxC : x ∈ C := by
        have hx : x ∈ (A ∪ B) ∪ C := by rw [hcover]; simp
        simpa [hxA, hxB] using hx
      have hyNotA : y ∉ A := by
        intro hyA
        simp [color, hxA, hxB, hyA] at hsame
      have hyNotB : y ∉ B := by
        intro hyB
        simp [color, hxA, hxB, hyNotA, hyB] at hsame
      have hyC : y ∈ C := by
        have hy : y ∈ (A ∪ B) ∪ C := by rw [hcover]; simp
        simpa [hyNotA, hyNotB] using hy
      exact hnotG (hC hxC hyC hxyne)

/-- If the ten-vertex exterior complement is bipartite, the open neighborhood
of the center is a clique. -/
theorem neighborhood_isClique_of_bipartite_compl_exterior_order_ten
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4) (v : V)
    (hUcard : Fintype.card (exteriorFinset G v : Set V) = 10)
    (hbip : (G.induce (exteriorFinset G v : Set V))ᶜ.IsBipartite) :
    G.IsClique (G.neighborFinset v : Set V) := by
  classical
  let N := G.neighborFinset v
  let U := exteriorFinset G v
  let R := G.induce (U : Set V)
  have hUcard' : Fintype.card (U : Set V) = 10 := by simpa [U] using hUcard
  have hRadmissible : Admissible R := by
    simpa [R, U] using admissible_induce G hG U
  obtain ⟨A, B, hAcard, hBcard, hABdis, hABcover,
      hAclique, hBclique, hAmatch, hBmatch⟩ :=
    exists_bipartition_order_ten R hRadmissible hUcard'
      (by simpa [R, U] using hbip)
  let f : (U : Set V) ↪ V := Function.Embedding.subtype _
  let A0 : Finset V := A.map f
  let B0 : Finset V := B.map f
  have hA0card : #A0 = 5 := by simp [A0, hAcard]
  have hB0card : #B0 = 5 := by simp [B0, hBcard]
  have hNUdis : Disjoint N U := by
    rw [Finset.disjoint_left]
    intro x hxN hxU
    have hvx : G.Adj v x := by simpa [N] using hxN
    have hxU' : x ≠ v ∧ ¬G.Adj v x := by
      simpa [U, exteriorFinset] using hxU
    exact hxU'.2 hvx
  have hNA0dis : Disjoint N A0 := by
    rw [Finset.disjoint_left]
    intro x hxN hxA0
    obtain ⟨x', hx'A, rfl⟩ := Finset.mem_map.mp hxA0
    exact (Finset.disjoint_left.mp hNUdis) hxN x'.property
  have hNB0dis : Disjoint N B0 := by
    rw [Finset.disjoint_left]
    intro x hxN hxB0
    obtain ⟨x', hx'B, rfl⟩ := Finset.mem_map.mp hxB0
    exact (Finset.disjoint_left.mp hNUdis) hxN x'.property
  have hA0clique : G.IsClique (A0 : Set V) := by
    intro x hx y hy hxy
    obtain ⟨x', hx'A, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy'B, rfl⟩ := Finset.mem_map.mp hy
    have hxy' : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
    change G.Adj (x' : V) (y' : V)
    simpa [R] using hAclique hx'A hy'B hxy'
  have hB0clique : G.IsClique (B0 : Set V) := by
    intro x hx y hy hxy
    obtain ⟨x', hx'A, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy'B, rfl⟩ := Finset.mem_map.mp hy
    have hxy' : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
    change G.Adj (x' : V) (y' : V)
    simpa [R] using hBclique hx'A hy'B hxy'
  have hA0indComp : Gᶜ.IsIndepSet (A0 : Set V) := by simpa using hA0clique
  have hB0indComp : Gᶜ.IsIndepSet (B0 : Set V) := by simpa using hB0clique
  have hANeighborLe (a : V) (haN : a ∈ N) :
      (G.between (N : Set V) (A0 : Set V)).degree a ≤ 1 := by
    have haNotA : a ∉ A0 := fun haA =>
      (Finset.disjoint_left.mp hNA0dis) haN haA
    have hSix : #(insert a A0) = 6 := by
      rw [Finset.card_insert_of_notMem haNotA, hA0card]
    have hfour :=
      four_le_card_induced_compl_of_admissible_six G hG (insert a A0) hSix
    have hfourNat :
        4 ≤ Nat.card (Gᶜ.induce (((insert a A0 : Finset V) : Set V))).edgeSet := by
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
      exact hfour
    have hexact := card_induce_insert_eq_between_degree_of_independent
      Gᶜ A0 N a haN hNA0dis.symm hA0indComp
    rw [hexact] at hfourNat
    have hcomm := degree_between_comm Gᶜ A0 N a
    have hpartition :=
      degree_between_add_compl_between_eq_card G N A0 hNA0dis a haN
    rw [hcomm] at hfourNat
    rw [hA0card] at hpartition
    omega
  have hBNeighborLe (a : V) (haN : a ∈ N) :
      (G.between (N : Set V) (B0 : Set V)).degree a ≤ 1 := by
    have haNotB : a ∉ B0 := fun haB =>
      (Finset.disjoint_left.mp hNB0dis) haN haB
    have hSix : #(insert a B0) = 6 := by
      rw [Finset.card_insert_of_notMem haNotB, hB0card]
    have hfour :=
      four_le_card_induced_compl_of_admissible_six G hG (insert a B0) hSix
    have hfourNat :
        4 ≤ Nat.card (Gᶜ.induce (((insert a B0 : Finset V) : Set V))).edgeSet := by
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
      exact hfour
    have hexact := card_induce_insert_eq_between_degree_of_independent
      Gᶜ B0 N a haN hNB0dis.symm hB0indComp
    rw [hexact] at hfourNat
    have hcomm := degree_between_comm Gᶜ B0 N a
    have hpartition :=
      degree_between_add_compl_between_eq_card G N B0 hNB0dis a haN
    rw [hcomm] at hfourNat
    rw [hB0card] at hpartition
    omega
  have hAFilterLe (a : V) (haN : a ∈ N) :
      #(A.filter fun x : (U : Set V) => G.Adj a (x : V)) ≤ 1 := by
    let C := G.between (N : Set V) (A0 : Set V)
    have hdisSet : Disjoint (N : Set V) (A0 : Set V) :=
      Finset.disjoint_coe.mpr hNA0dis
    have hCbip : C.IsBipartiteWith (N : Set V) (A0 : Set V) := by
      simpa [C] using SimpleGraph.between_isBipartiteWith (G := G) hdisSet
    have haNotA0 : a ∉ A0 := fun haA0 =>
      (Finset.disjoint_left.mp hNA0dis) haN haA0
    have hmap :
        (A.filter fun x : (U : Set V) => G.Adj a (x : V)).map f =
          A0.filter (G.Adj a) := by
      ext x
      simp [A0, f]
    calc
      #(A.filter fun x : (U : Set V) => G.Adj a (x : V)) =
          #((A.filter fun x : (U : Set V) => G.Adj a (x : V)).map f) := by simp
      _ = #(A0.filter (G.Adj a)) := congrArg Finset.card hmap
      _ = #(C.neighborFinset a) := by
        congr 1
        ext x
        simp [C, SimpleGraph.between_adj, haN, haNotA0, and_comm]
      _ = C.degree a := SimpleGraph.card_neighborFinset_eq_degree C a
      _ ≤ 1 := by simpa [C] using hANeighborLe a haN
  have hBFilterLe (a : V) (haN : a ∈ N) :
      #(B.filter fun x : (U : Set V) => G.Adj a (x : V)) ≤ 1 := by
    let C := G.between (N : Set V) (B0 : Set V)
    have hdisSet : Disjoint (N : Set V) (B0 : Set V) :=
      Finset.disjoint_coe.mpr hNB0dis
    have hCbip : C.IsBipartiteWith (N : Set V) (B0 : Set V) := by
      simpa [C] using SimpleGraph.between_isBipartiteWith (G := G) hdisSet
    have haNotB0 : a ∉ B0 := fun haB0 =>
      (Finset.disjoint_left.mp hNB0dis) haN haB0
    have hmap :
        (B.filter fun x : (U : Set V) => G.Adj a (x : V)).map f =
          B0.filter (G.Adj a) := by
      ext x
      simp [B0, f]
    calc
      #(B.filter fun x : (U : Set V) => G.Adj a (x : V)) =
          #((B.filter fun x : (U : Set V) => G.Adj a (x : V)).map f) := by simp
      _ = #(B0.filter (G.Adj a)) := congrArg Finset.card hmap
      _ = #(C.neighborFinset a) := by
        congr 1
        ext x
        simp [C, SimpleGraph.between_adj, haN, haNotB0, and_comm]
      _ = C.degree a := SimpleGraph.card_neighborFinset_eq_degree C a
      _ ≤ 1 := by simpa [C] using hBNeighborLe a haN
  intro a haN b hbN hab
  by_contra hnab
  let badA := (A.filter fun x : (U : Set V) => G.Adj a (x : V)) ∪
    (A.filter fun x : (U : Set V) => G.Adj b (x : V))
  let goodA := A \ badA
  let badB := (B.filter fun x : (U : Set V) => G.Adj a (x : V)) ∪
    (B.filter fun x : (U : Set V) => G.Adj b (x : V))
  let goodB := B \ badB
  have hbadAsub : badA ⊆ A :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hbadBsub : badB ⊆ B :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hbadAcard : #badA ≤ 2 := by
    have hu := Finset.card_union_le
      (A.filter fun x : (U : Set V) => G.Adj a (x : V))
      (A.filter fun x : (U : Set V) => G.Adj b (x : V))
    have ha := hAFilterLe a haN
    have hb := hAFilterLe b hbN
    change #((A.filter fun x : (U : Set V) => G.Adj a (x : V)) ∪
      (A.filter fun x : (U : Set V) => G.Adj b (x : V))) ≤ 2
    omega
  have hbadBcard : #badB ≤ 2 := by
    have hu := Finset.card_union_le
      (B.filter fun x : (U : Set V) => G.Adj a (x : V))
      (B.filter fun x : (U : Set V) => G.Adj b (x : V))
    have ha := hBFilterLe a haN
    have hb := hBFilterLe b hbN
    change #((B.filter fun x : (U : Set V) => G.Adj a (x : V)) ∪
      (B.filter fun x : (U : Set V) => G.Adj b (x : V))) ≤ 2
    omega
  have hgoodAcard : 3 ≤ #goodA := by
    have hs := Finset.card_sdiff_of_subset hbadAsub
    rw [hAcard] at hs
    have hs' : #goodA = 5 - #badA := by simpa [goodA] using hs
    omega
  have hgoodBcard : 3 ≤ #goodB := by
    have hs := Finset.card_sdiff_of_subset hbadBsub
    rw [hBcard] at hs
    have hs' : #goodB = 5 - #badB := by simpa [goodB] using hs
    omega
  obtain ⟨x, hxgood⟩ := Finset.card_pos.mp (by omega : 0 < #goodA)
  have hxA : x ∈ A := (Finset.mem_sdiff.mp hxgood).1
  have hxavoid : ¬G.Adj a (x : V) ∧ ¬G.Adj b (x : V) := by
    have hxnot := (Finset.mem_sdiff.mp hxgood).2
    simpa [badA, hxA] using hxnot
  let T := goodB.filter (R.Adj x)
  have hTneighborSub :
      T ⊆ (R.between (A : Set _) (B : Set _)).neighborFinset x := by
    intro y hy
    have hy' := Finset.mem_filter.mp hy
    have hyB : y ∈ B := (Finset.mem_sdiff.mp hy'.1).1
    rw [SimpleGraph.mem_neighborFinset]
    exact ⟨hy'.2, Or.inl ⟨hxA, hyB⟩⟩
  have hTcard : #T ≤ 1 := by
    calc
      #T ≤ #((R.between (A : Set _) (B : Set _)).neighborFinset x) :=
        Finset.card_le_card hTneighborSub
      _ = (R.between (A : Set _) (B : Set _)).degree x :=
        SimpleGraph.card_neighborFinset_eq_degree _ _
      _ ≤ 1 := hAmatch x hxA
  have hnotSub : ¬goodB ⊆ T := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨y, hygood, hyNotT⟩ := Finset.not_subset.mp hnotSub
  have hyB : y ∈ B := (Finset.mem_sdiff.mp hygood).1
  have hyavoid : ¬G.Adj a (y : V) ∧ ¬G.Adj b (y : V) := by
    have hynot := (Finset.mem_sdiff.mp hygood).2
    simpa [badB, hyB] using hynot
  have hxyR : ¬R.Adj x y := by
    intro hxy
    exact hyNotT (Finset.mem_filter.mpr ⟨hygood, hxy⟩)
  have hxyG : ¬G.Adj (x : V) (y : V) := by simpa [R] using hxyR
  have hax : a ≠ (x : V) := fun h =>
    (Finset.disjoint_left.mp hNUdis) haN (h ▸ x.property)
  have hay : a ≠ (y : V) := fun h =>
    (Finset.disjoint_left.mp hNUdis) haN (h ▸ y.property)
  have hbx : b ≠ (x : V) := fun h =>
    (Finset.disjoint_left.mp hNUdis) hbN (h ▸ x.property)
  have hby : b ≠ (y : V) := fun h =>
    (Finset.disjoint_left.mp hNUdis) hbN (h ▸ y.property)
  have hxy : (x : V) ≠ (y : V) := by
    intro h
    have hsub : x = y := Subtype.ext h
    subst y
    exact (Finset.disjoint_left.mp hABdis) hxA hyB
  exact false_of_indepSetFree_four_of_pairwise_nonadj G hfree
    hab hax hay hbx hby hxy hnab hxavoid.1 hyavoid.1
    hxavoid.2 hyavoid.2 hxyG

/-- At order fifteen and degree four, a bipartite exterior complement gives
an explicit three-coloring of the whole complement. -/
theorem compl_colorable_three_of_bipartite_compl_exterior_degree_four
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (hcard : Fintype.card V = 15) (v : V) (hdegree : G.degree v = 4)
    (hbip : (G.induce (exteriorFinset G v : Set V))ᶜ.IsBipartite) :
    Gᶜ.Colorable 3 := by
  classical
  let N := G.neighborFinset v
  let U := exteriorFinset G v
  let R := G.induce (U : Set V)
  let C : Finset V := insert v N
  have hUcardRaw := card_exterior_type_add_degree_add_one G v
  have hUcard : Fintype.card (U : Set V) = 10 := by
    rw [hcard, hdegree] at hUcardRaw
    simpa [U] using (show Fintype.card (exteriorFinset G v : Set V) = 10 by omega)
  have hRadmissible : Admissible R := by
    simpa [R, U] using admissible_induce G hG U
  obtain ⟨A, B, hAcard, hBcard, hABdis, hABcover,
      hAclique, hBclique, hAmatch, hBmatch⟩ :=
    exists_bipartition_order_ten R hRadmissible hUcard
      (by simpa [R, U] using hbip)
  let f : (U : Set V) ↪ V := Function.Embedding.subtype _
  let A0 : Finset V := A.map f
  let B0 : Finset V := B.map f
  have hA0clique : G.IsClique (A0 : Set V) := by
    intro x hx y hy hxy
    obtain ⟨x', hx'A, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy'B, rfl⟩ := Finset.mem_map.mp hy
    have hxy' : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
    change G.Adj (x' : V) (y' : V)
    simpa [R] using hAclique hx'A hy'B hxy'
  have hB0clique : G.IsClique (B0 : Set V) := by
    intro x hx y hy hxy
    obtain ⟨x', hx'A, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy'B, rfl⟩ := Finset.mem_map.mp hy
    have hxy' : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
    change G.Adj (x' : V) (y' : V)
    simpa [R] using hBclique hx'A hy'B hxy'
  have hNclique : G.IsClique (N : Set V) := by
    simpa [N, U, R] using
      neighborhood_isClique_of_bipartite_compl_exterior_order_ten
        G hG hfree v (by simpa [U] using hUcard) (by simpa [R, U] using hbip)
  have hCclique : G.IsClique (C : Set V) := by
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with rfl | hxN
    · have hyN : y ∈ N := by
        rcases Finset.mem_insert.mp hy with hyv | hyN
        · exact (hxy hyv.symm).elim
        · exact hyN
      simpa [N] using hyN
    · rcases Finset.mem_insert.mp hy with hyv | hyN
      · subst y
        have hvx : G.Adj v x := by simpa [N] using hxN
        exact hvx.symm
      · exact hNclique hxN hyN hxy
  have hcover : (C ∪ A0) ∪ B0 = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hxC : x ∈ C
    · exact Or.inl (Or.inl hxC)
    · have hxU : x ∈ U := by simpa [C, U, exteriorFinset, N] using hxC
      let xU : (U : Set V) := ⟨x, hxU⟩
      have hxAB : xU ∈ A ∪ B := by rw [hABcover]; simp
      rcases Finset.mem_union.mp hxAB with hxA | hxB
      · exact Or.inl (Or.inr (by
          exact Finset.mem_map.mpr ⟨xU, hxA, rfl⟩))
      · exact Or.inr (by exact Finset.mem_map.mpr ⟨xU, hxB, rfl⟩)
  exact compl_colorable_three_of_three_clique_cover
    G C A0 B0 hcover hCclique hA0clique hB0clique

/-- An admissible graph on ten vertices with bipartite complement has at most
twenty-five edges: each complementary color class has size five, and the
original edges between the two classes form a matching. -/
theorem card_edges_le_twentyFive_of_admissible_order_ten_compl_bipartite
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hcard : Fintype.card V = 10)
    (hbip : Gᶜ.IsBipartite) :
    #G.edgeFinset ≤ 25 := by
  classical
  obtain ⟨A, B, hAcard, hBcard, hABdis, hABcover,
      hAclique, hBclique, hAmatch, hBmatch⟩ :=
    exists_bipartition_order_ten G hG hcard hbip
  have hBcompl : B = Aᶜ := by
    ext x
    constructor
    · intro hxB
      have hxNotA : x ∉ A := fun hxA =>
        (Finset.disjoint_left.mp hABdis) hxA hxB
      simpa using hxNotA
    · intro hxComp
      have hxNotA : x ∉ A := by simpa using hxComp
      have hxCover : x ∈ A ∪ B := by rw [hABcover]; simp
      rcases Finset.mem_union.mp hxCover with hxA | hxB
      · exact (hxNotA hxA).elim
      · exact hxB
  subst B
  let D := G.between (A : Set V) ((Aᶜ : Finset V) : Set V)
  have hDdisSet : Disjoint (A : Set V) ((Aᶜ : Finset V) : Set V) :=
    Finset.disjoint_coe.mpr hABdis
  have hDbip : D.IsBipartiteWith (A : Set V)
      ((Aᶜ : Finset V) : Set V) := by
    simpa [D] using SimpleGraph.between_isBipartiteWith (G := G) hDdisSet
  have hDsum : (∑ a ∈ A, D.degree a) = #D.edgeFinset :=
    SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hDbip
  have hDsumUpper : (∑ a ∈ A, D.degree a) ≤ ∑ _a ∈ A, 1 :=
    Finset.sum_le_sum fun a ha => by simpa [D] using hAmatch a ha
  have hDupper : #D.edgeFinset ≤ 5 := by
    rw [hDsum] at hDsumUpper
    simpa [hAcard] using hDsumUpper
  have hAupper :=
    SimpleGraph.card_edgeFinset_le_card_choose_two
      (G := G.induce (A : Set V))
  have hAtype : Fintype.card (A : Set V) = 5 := by simpa using hAcard
  rw [hAtype] at hAupper
  norm_num [Nat.choose] at hAupper
  have hBupper :=
    SimpleGraph.card_edgeFinset_le_card_choose_two
      (G := G.induce ((Aᶜ : Finset V) : Set V))
  have hBtype : Fintype.card ((Aᶜ : Finset V) : Set V) = 5 := by
    change Fintype.card (Aᶜ : Finset V) = 5
    calc
      Fintype.card (Aᶜ : Finset V) = #(Aᶜ : Finset V) :=
        Fintype.card_coe _
      _ = 5 := hBcard
  rw [hBtype] at hBupper
  norm_num [Nat.choose] at hBupper
  have hpartition :=
    card_edgeFinset_eq_induce_add_between_add_induce_compl G A
  have hpartition' : #G.edgeFinset =
      #(G.induce (A : Set V)).edgeFinset + #D.edgeFinset +
        #(G.induce ((Aᶜ : Finset V) : Set V)).edgeFinset := by
    simpa [D] using hpartition
  omega

/-- At order fifteen and at most 36 edges, the minimum degree is exactly four. -/
theorem exists_minimal_degree_four_of_admissible_indepSetFree_four_card_fifteen
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (hcard : Fintype.card V = 15) (hedges : #G.edgeFinset ≤ 36) :
    ∃ v : V, (∀ w, G.degree v ≤ G.degree w) ∧ G.degree v = 4 := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v, hmin, havg⟩ :=
    exists_minimal_vertex_card_mul_degree_le_twice_edges G
  have hdegreeCap : G.degree v ≤ 4 := by
    rw [hcard] at havg
    omega
  let U := exteriorFinset G v
  let R := G.induce (U : Set V)
  have hUcard := card_exterior_type_add_degree_add_one G v
  rw [hcard] at hUcard
  have hUcardU : Fintype.card (U : Set V) + G.degree v + 1 = 15 := by
    simpa [U] using hUcard
  have hRadmissible : Admissible R := by
    simpa [R] using admissible_induce G hG U
  have hRfree : R.IndepSetFree 3 := by
    simpa [R, U] using
      (indepSetFree_exterior_induce G (k := 3) (by simpa using hfree) v)
  have hsplit := exterior_edges_add_degree_add_choose_le_edges G v hmin
  have hsplitR : #R.edgeFinset + G.degree v + (G.degree v).choose 2 ≤
      #G.edgeFinset := by simpa [R, U] using hsplit
  have hdegreeLower : 4 ≤ G.degree v := by
    by_contra hnot
    have hle : G.degree v ≤ 3 := by omega
    interval_cases hdegree : G.degree v
    · have hRcard : Fintype.card (U : Set V) = 14 := by omega
      have hRbound :=
        choose_card_le_edges_add_twice_card_of_admissible_indepSetFree_three
          R hRadmissible hRfree (by omega : 12 ≤ Fintype.card (U : Set V))
      rw [hRcard] at hRbound
      norm_num [hdegree, Nat.choose] at hsplitR hRbound
      omega
    · have hRcard : Fintype.card (U : Set V) = 13 := by omega
      have hRbound :=
        choose_card_le_edges_add_twice_card_of_admissible_indepSetFree_three
          R hRadmissible hRfree (by omega : 12 ≤ Fintype.card (U : Set V))
      rw [hRcard] at hRbound
      norm_num [hdegree, Nat.choose] at hsplitR hRbound
      omega
    · have hRcard : Fintype.card (U : Set V) = 12 := by omega
      have hRbound :=
        choose_card_le_edges_add_twice_card_of_admissible_indepSetFree_three
          R hRadmissible hRfree (by omega : 12 ≤ Fintype.card (U : Set V))
      rw [hRcard] at hRbound
      norm_num [hdegree, Nat.choose] at hsplitR hRbound
      omega
    · have hRcard : Fintype.card (U : Set V) = 11 := by omega
      have hRbound :=
        card_edges_ge_thirtySix_of_admissible_indepSetFree_three_card_eleven
          R hRadmissible hRfree hRcard
      norm_num [hdegree, Nat.choose] at hsplitR
      omega
  exact ⟨v, hmin, by omega⟩

/-- A maximum-size internal graph on the open neighborhood makes the closed
neighborhood a clique. No assertion about edges leaving that clique is made. -/
theorem closedNeighborhood_isClique_of_internal_eq_choose
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hinternal : neighborhoodInternalEdgeCount G v =
      (G.degree v).choose 2) :
    G.IsClique (insert v (G.neighborFinset v) : Set V) := by
  classical
  let N := G.neighborFinset v
  let F := G.induce (N : Set V)
  have hcardN : Fintype.card (N : Set V) = G.degree v := by
    calc
      Fintype.card (N : Set V) = #N := by simp
      _ = G.degree v := SimpleGraph.card_neighborFinset_eq_degree G v
  have hFcard : #F.edgeFinset = (G.degree v).choose 2 := by
    calc
      #F.edgeFinset = neighborhoodInternalEdgeCount G v := by
        exact (neighborhoodInternalEdgeCount_eq_induce G v).symm
      _ = (G.degree v).choose 2 := hinternal
  have htopCard : #((⊤ : SimpleGraph (N : Set V)).edgeFinset) =
      (G.degree v).choose 2 := by
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, hcardN]
  have hFedges : F.edgeFinset =
      (⊤ : SimpleGraph (N : Set V)).edgeFinset := by
    apply Finset.eq_of_subset_of_card_le
    · exact SimpleGraph.edgeFinset_mono le_top
    · rw [htopCard, hFcard]
  have hFtop : F = (⊤ : SimpleGraph (N : Set V)) :=
    SimpleGraph.edgeFinset_inj.mp hFedges
  intro a ha b hb hab
  simp only [Set.mem_insert_iff] at ha hb
  rcases ha with rfl | haN
  · have hbN : b ∈ N := by
      rcases hb with hbv | hbN
      · exact (hab hbv.symm).elim
      · exact hbN
    simpa [N] using hbN
  · rcases hb with hbv | hbN
    · subst b
      have hva : G.Adj v a := by simpa [N] using haN
      exact hva.symm
    · let aN : (N : Set V) := ⟨a, haN⟩
      let bN : (N : Set V) := ⟨b, hbN⟩
      have habN : aN ≠ bN := by
        intro h
        exact hab (congrArg Subtype.val h)
      have hFab : F.Adj aN bN :=
        (SimpleGraph.eq_top_iff_forall_ne_adj.mp hFtop) aN bN habN
      simpa [F, aN, bN, SimpleGraph.induce_adj] using hFab

/-- The exact structure required from an order-fifteen, thirty-five-edge
graph: an isolated five-clique and the canonical ten-vertex residual
complement. -/
def OrderFifteenThirtyFiveStructure
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ C : Finset V,
    #C = 5 ∧ IsIsolatedCliqueOn G C ∧
      Nonempty ((G.induce ((Cᶜ : Finset V) : Set V))ᶜ ≃g
        balancedC5Blowup)

/-- The first thirty-six-edge alternative: a five-clique with exactly one
edge leaving it and the canonical ten-vertex residual complement. -/
def OrderFifteenThirtySixOneCrossStructure
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ C : Finset V,
    #C = 5 ∧ G.IsClique (C : Set V) ∧
      #(G.between (C : Set V) ((Cᶜ : Finset V) : Set V)).edgeFinset = 1 ∧
        Nonempty ((G.induce ((Cᶜ : Finset V) : Set V))ᶜ ≃g
          balancedC5Blowup)

/-- The second thirty-six-edge alternative: an isolated five-clique and a
nineteen-edge, triangle-free residual complement with no independent
five-set. -/
def OrderFifteenThirtySixIsolatedStructure
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ C : Finset V,
    #C = 5 ∧ IsIsolatedCliqueOn G C ∧
      let L := (G.induce ((Cᶜ : Finset V) : Set V))ᶜ
      L.CliqueFree 3 ∧ #L.edgeFinset = 19 ∧ L.IndepSetFree 5

/-- Every admissible order-fifteen, thirty-five-edge graph with no independent
four-set and non-three-colorable complement has the exact isolated-`K₅`
structure used in the fixed-`r = 5` argument. -/
theorem orderFifteenThirtyFiveStructure_of_admissible
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (hcard : Fintype.card V = 15) (hedges : #G.edgeFinset = 35)
    (hnotColorable : ¬Gᶜ.Colorable 3) :
    OrderFifteenThirtyFiveStructure G := by
  classical
  obtain ⟨v, hmin, hdegree⟩ :=
    exists_minimal_degree_four_of_admissible_indepSetFree_four_card_fifteen
      G hG hfree hcard (by omega)
  let N := G.neighborFinset v
  let U := exteriorFinset G v
  let R := G.induce (U : Set V)
  let C : Finset V := insert v N
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
  have hRupper : #R.edgeFinset ≤ 25 := by
    have hsplit' : #R.edgeFinset + G.degree v + (G.degree v).choose 2 ≤
        #G.edgeFinset := by simpa [R, U] using hsplit
    rw [hdegree, hedges] at hsplit'
    norm_num [Nat.choose] at hsplit'
    omega
  have hRnotLeTwentyFour : ¬#R.edgeFinset ≤ 24 := by
    intro hRle
    have hpartition := card_edgeFinset_add_card_compl R
    rw [hUcard] at hpartition
    norm_num [Nat.choose] at hpartition
    by_cases hbip : Rᶜ.IsBipartite
    · exact hnotColorable
        (compl_colorable_three_of_bipartite_compl_exterior_degree_four
          G hG hfree hcard v hdegree (by simpa [R, U] using hbip))
    · have hLupper :=
        card_compl_edges_le_twenty_of_admissible_order_ten_nonbipartite
          R hRadmissible hRfree hUcard hbip
      omega
  have hRedges : #R.edgeFinset = 25 := by omega
  have haccountExact :=
    card_edges_eq_exterior_add_degree_add_accounting G v
  have haccount : neighborhoodCrossEdgeCount G v +
      neighborhoodInternalEdgeCount G v = 6 := by
    have haccount' : #R.edgeFinset + G.degree v +
        (neighborhoodCrossEdgeCount G v +
          neighborhoodInternalEdgeCount G v) = #G.edgeFinset := by
      simpa [R, U] using haccountExact
    rw [hRedges, hdegree, hedges] at haccount'
    omega
  have haccountChoose : neighborhoodCrossEdgeCount G v +
      neighborhoodInternalEdgeCount G v = (G.degree v).choose 2 := by
    rw [hdegree]
    norm_num [Nat.choose]
    exact haccount
  have hisolated :=
    neighborhood_accounting_equality_isolatedClique G v hmin haccountChoose
  have hCcard : #C = 5 := by
    simp [C, N, G.notMem_neighborFinset_self v,
      SimpleGraph.card_neighborFinset_eq_degree, hdegree]
  have hnotbip : ¬Rᶜ.IsBipartite := by
    intro hbip
    exact hnotColorable
      (compl_colorable_three_of_bipartite_compl_exterior_degree_four
        G hG hfree hcard v hdegree (by simpa [R, U] using hbip))
  have hpartition := card_edgeFinset_add_card_compl R
  rw [hUcard, hRedges] at hpartition
  norm_num [Nat.choose] at hpartition
  have hLedges : #Rᶜ.edgeFinset = 20 := by omega
  have hiso :=
    compl_iso_balancedC5Blowup_of_admissible_order_ten_equality
      R hRadmissible hRfree hUcard hnotbip hLedges
  refine ⟨C, hCcard, ?_, ?_⟩
  · simpa [C, N] using hisolated
  · change Nonempty ((G.induce (((Cᶜ : Finset V) : Set V)))ᶜ ≃g
      balancedC5Blowup)
    rw [show (Cᶜ : Finset V) = U by rfl]
    simpa [R] using hiso

/-- The twenty-six-edge exterior branch of the thirty-six-edge
classification yields the isolated-clique alternative. -/
theorem orderFifteenThirtySixIsolatedStructure_of_exterior_twentySix
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (hcard : Fintype.card V = 15) (hedges : #G.edgeFinset = 36)
    (v : V) (hmin : ∀ w, G.degree v ≤ G.degree w)
    (hdegree : G.degree v = 4)
    (hRedges : #(G.induce (exteriorFinset G v : Set V)).edgeFinset = 26) :
    OrderFifteenThirtySixIsolatedStructure G := by
  classical
  let N := G.neighborFinset v
  let U := exteriorFinset G v
  let R := G.induce (U : Set V)
  let C : Finset V := insert v N
  let L := Rᶜ
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
  have hRedgesR : #R.edgeFinset = 26 := by simpa [R, U] using hRedges
  have haccountExact :=
    card_edges_eq_exterior_add_degree_add_accounting G v
  have haccount : neighborhoodCrossEdgeCount G v +
      neighborhoodInternalEdgeCount G v = 6 := by
    have haccount' : #R.edgeFinset + G.degree v +
        (neighborhoodCrossEdgeCount G v +
          neighborhoodInternalEdgeCount G v) = #G.edgeFinset := by
      simpa [R, U] using haccountExact
    rw [hRedgesR, hdegree, hedges] at haccount'
    omega
  have haccountChoose : neighborhoodCrossEdgeCount G v +
      neighborhoodInternalEdgeCount G v = (G.degree v).choose 2 := by
    rw [hdegree]
    norm_num [Nat.choose]
    exact haccount
  have hisolated :=
    neighborhood_accounting_equality_isolatedClique G v hmin haccountChoose
  have hCcard : #C = 5 := by
    simp [C, N, G.notMem_neighborFinset_self v,
      SimpleGraph.card_neighborFinset_eq_degree, hdegree]
  have hpartition := card_edgeFinset_add_card_compl R
  rw [hUcard, hRedgesR] at hpartition
  norm_num [Nat.choose] at hpartition
  have hLedges : #L.edgeFinset = 19 := by
    simpa [L] using (show #Rᶜ.edgeFinset = 19 by omega)
  have hnotbip : ¬L.IsBipartite := by
    intro hbip
    have hRupper :=
      card_edges_le_twentyFive_of_admissible_order_ten_compl_bipartite
        R hRadmissible hUcard (by simpa [L] using hbip)
    omega
  have hLtriangle : L.CliqueFree 3 := by simpa [L] using hRfree
  have hLfree : L.IndepSetFree 5 := by
    simpa [L] using
      (compl_indepSetFree_five_of_admissible_order_ten_nineteen_edges
        R hRadmissible hUcard (by simpa [L] using hLedges))
  refine ⟨C, hCcard, ?_, ?_⟩
  · simpa [C, N] using hisolated
  · dsimp
    rw [show (Cᶜ : Finset V) = U by rfl]
    simpa [R, L] using And.intro hLtriangle (And.intro hLedges hLfree)

/-- In the twenty-five-edge exterior branch, five internal neighborhood edges
would turn the unique missing neighborhood edge's two endpoints into a
vertex cover of size at most two in the residual complement. The certified
cover number is six, so this branch is impossible. -/
theorem false_of_orderFifteen_exterior_twentyFive_internal_five
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (hcard : Fintype.card V = 15) (hedges : #G.edgeFinset = 36)
    (hnotColorable : ¬Gᶜ.Colorable 3)
    (v : V) (hdegree : G.degree v = 4)
    (hRedges : #(G.induce (exteriorFinset G v : Set V)).edgeFinset = 25)
    (hinternal : neighborhoodInternalEdgeCount G v = 5) :
    False := by
  classical
  let N := G.neighborFinset v
  let U := exteriorFinset G v
  let R := G.induce (U : Set V)
  let L := Rᶜ
  let D := G.between (N : Set V) (U : Set V)
  let H := G.induce (N : Set V)
  let M := Hᶜ
  have hNcard : #N = 4 := by
    simp [N, SimpleGraph.card_neighborFinset_eq_degree, hdegree]
  have hNtype : Fintype.card (N : Set V) = 4 := by simpa using hNcard
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
  have hRedgesR : #R.edgeFinset = 25 := by simpa [R, U] using hRedges
  have hnotbip : ¬L.IsBipartite := by
    intro hbip
    exact hnotColorable
      (compl_colorable_three_of_bipartite_compl_exterior_degree_four
        G hG hfree hcard v hdegree (by simpa [L, R, U] using hbip))
  have hpartitionR := card_edgeFinset_add_card_compl R
  rw [hUcard, hRedgesR] at hpartitionR
  norm_num [Nat.choose] at hpartitionR
  have hLedges : #L.edgeFinset = 20 := by
    simpa [L] using (show #Rᶜ.edgeFinset = 20 by omega)
  have hcoverEq : L.vertexCoverNum = 6 := by
    simpa [L] using
      (compl_vertexCoverNum_eq_six_of_admissible_order_ten_equality
        R hRadmissible hRfree hUcard (by simpa [L] using hnotbip)
          (by simpa [L] using hLedges))
  have hHedges : #H.edgeFinset = 5 := by
    have hi := neighborhoodInternalEdgeCount_eq_induce G v
    rw [hinternal] at hi
    simpa [H, N] using hi.symm
  have hMpartition := card_edgeFinset_add_card_compl H
  rw [hNtype, hHedges] at hMpartition
  norm_num [Nat.choose] at hMpartition
  have hMedges : #M.edgeFinset = 1 := by
    simpa [M] using (show #Hᶜ.edgeFinset = 1 by omega)
  have haccountExact :=
    card_edges_eq_exterior_add_degree_add_accounting G v
  have hX : neighborhoodCrossEdgeCount G v = 2 := by
    have haccount' : #R.edgeFinset + G.degree v +
        (neighborhoodCrossEdgeCount G v +
          neighborhoodInternalEdgeCount G v) = #G.edgeFinset := by
      simpa [R, U] using haccountExact
    rw [hRedgesR, hdegree, hinternal, hedges] at haccount'
    omega
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
  have hDedges : #D.edgeFinset = 2 := by
    simpa [D, N, U, neighborhoodCrossEdgeCount] using hX
  have hSumDbase : (∑ a ∈ N, D.degree a) = 2 := by
    have hs := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hDbip
    rw [hDedges] at hs
    exact hs
  have hSumD : (∑ a : (N : Set V), D.degree (a : V)) = 2 := by
    have hs := Finset.sum_attach N (fun a => D.degree a)
    rw [Finset.attach_eq_univ] at hs
    calc
      (∑ a : (N : Set V), D.degree (a : V)) = ∑ a ∈ N, D.degree a := hs
      _ = 2 := hSumDbase
  have hMnonempty : M.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨e, he⟩ := hMnonempty
  induction e using Sym2.inductionOn with
  | hf a b =>
    have habM : M.Adj a b := by simpa using he
    have hpairDegree : D.degree (a : V) + D.degree (b : V) ≤ 2 := by
      have hsub : ({a, b} : Finset (N : Set V)) ⊆ Finset.univ :=
        Finset.subset_univ _
      have hsumLe := Finset.sum_le_sum_of_subset
        (f := fun x : (N : Set V) => D.degree (x : V)) hsub
      rw [hSumD] at hsumLe
      simpa [habM.ne] using hsumLe
    let K0 : Finset V :=
      D.neighborFinset (a : V) ∪ D.neighborFinset (b : V)
    have hDaSub : D.neighborFinset (a : V) ⊆ U :=
      SimpleGraph.isBipartiteWith_neighborFinset_subset hDbip a.property
    have hDbSub : D.neighborFinset (b : V) ⊆ U :=
      SimpleGraph.isBipartiteWith_neighborFinset_subset hDbip b.property
    have hK0sub : K0 ⊆ U := Finset.union_subset hDaSub hDbSub
    let fU : (U : Set V) ↪ V := Function.Embedding.subtype _
    let K : Finset (U : Set V) :=
      Finset.univ.filter fun x => (x : V) ∈ K0
    have hKmap : K.map fU = K0 := by
      ext x
      constructor
      · intro hx
        obtain ⟨x', hx'K, hx'eq⟩ := Finset.mem_map.mp hx
        subst x
        change (x' : V) ∈ K0
        simpa [K] using hx'K
      · intro hx
        have hxU := hK0sub hx
        refine Finset.mem_map.mpr ⟨⟨x, hxU⟩, ?_, ?_⟩
        · simp [K, hx]
        · rfl
    have hKcardBase : #K = #K0 := by
      calc
        #K = #(K.map fU) := by simp
        _ = #K0 := congrArg Finset.card hKmap
    have hKcard : #K ≤ 2 := by
      have hu := Finset.card_union_le
        (D.neighborFinset (a : V)) (D.neighborFinset (b : V))
      simp only [SimpleGraph.card_neighborFinset_eq_degree] at hu
      calc
        #K = #K0 := hKcardBase
        _ = #(D.neighborFinset (a : V) ∪
            D.neighborFinset (b : V)) := by rfl
        _ ≤ D.degree (a : V) + D.degree (b : V) := hu
        _ ≤ 2 := hpairDegree
    have habG : ¬G.Adj (a : V) (b : V) := by
      have habComp : Hᶜ.Adj a b := by simpa [M] using habM
      have habHnot : ¬H.Adj a b := habComp.2
      simpa [H] using habHnot
    have hKcover : L.IsVertexCover (K : Set (U : Set V)) := by
      intro x y hxyL
      by_contra hnot
      have hxNotK : x ∉ K := by
        intro hx
        exact hnot (Or.inl hx)
      have hyNotK : y ∉ K := by
        intro hy
        exact hnot (Or.inr hy)
      have hxNotK0 : (x : V) ∉ K0 := by simpa [K] using hxNotK
      have hyNotK0 : (y : V) ∉ K0 := by simpa [K] using hyNotK
      have hxAvoid : ¬G.Adj (a : V) (x : V) ∧
          ¬G.Adj (b : V) (x : V) := by
        have hxParts :
            (x : V) ∉ D.neighborFinset (a : V) ∧
              (x : V) ∉ D.neighborFinset (b : V) := by
          simpa [K0] using hxNotK0
        constructor
        · intro hax
          exact hxParts.1 (by
            rw [SimpleGraph.mem_neighborFinset]
            exact ⟨hax, Or.inl ⟨a.property, x.property⟩⟩)
        · intro hbx
          exact hxParts.2 (by
            rw [SimpleGraph.mem_neighborFinset]
            exact ⟨hbx, Or.inl ⟨b.property, x.property⟩⟩)
      have hyAvoid : ¬G.Adj (a : V) (y : V) ∧
          ¬G.Adj (b : V) (y : V) := by
        have hyParts :
            (y : V) ∉ D.neighborFinset (a : V) ∧
              (y : V) ∉ D.neighborFinset (b : V) := by
          simpa [K0] using hyNotK0
        constructor
        · intro hay
          exact hyParts.1 (by
            rw [SimpleGraph.mem_neighborFinset]
            exact ⟨hay, Or.inl ⟨a.property, y.property⟩⟩)
        · intro hby
          exact hyParts.2 (by
            rw [SimpleGraph.mem_neighborFinset]
            exact ⟨hby, Or.inl ⟨b.property, y.property⟩⟩)
      have hxyG : ¬G.Adj (x : V) (y : V) := by
        have hxyComp : Rᶜ.Adj x y := by simpa [L] using hxyL
        have hxyRnot : ¬R.Adj x y := hxyComp.2
        simpa [R] using hxyRnot
      have hab : (a : V) ≠ (b : V) := fun h =>
        habM.ne (Subtype.ext h)
      have hax : (a : V) ≠ (x : V) := fun h =>
        (Finset.disjoint_left.mp hNUdis) a.property (h ▸ x.property)
      have hay : (a : V) ≠ (y : V) := fun h =>
        (Finset.disjoint_left.mp hNUdis) a.property (h ▸ y.property)
      have hbx : (b : V) ≠ (x : V) := fun h =>
        (Finset.disjoint_left.mp hNUdis) b.property (h ▸ x.property)
      have hby : (b : V) ≠ (y : V) := fun h =>
        (Finset.disjoint_left.mp hNUdis) b.property (h ▸ y.property)
      have hxy : (x : V) ≠ (y : V) := fun h =>
        hxyL.ne (Subtype.ext h)
      exact false_of_indepSetFree_four_of_pairwise_nonadj G hfree
        hab hax hay hbx hby hxy habG hxAvoid.1 hyAvoid.1
        hxAvoid.2 hyAvoid.2 hxyG
    have hcoverUpper : L.vertexCoverNum ≤ (2 : ℕ∞) := by
      calc
        L.vertexCoverNum ≤ (K : Set (U : Set V)).encard :=
          hKcover.vertexCoverNum_le
        _ = (#K : ℕ∞) := by simp
        _ ≤ (2 : ℕ∞) := by exact_mod_cast hKcard
    rw [hcoverEq] at hcoverUpper
    norm_num at hcoverUpper

/-- The twenty-five-edge exterior branch of the thirty-six-edge
classification yields the exact one-cross-edge alternative. -/
theorem orderFifteenThirtySixOneCrossStructure_of_exterior_twentyFive
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (hcard : Fintype.card V = 15) (hedges : #G.edgeFinset = 36)
    (hnotColorable : ¬Gᶜ.Colorable 3)
    (v : V) (hmin : ∀ w, G.degree v ≤ G.degree w)
    (hdegree : G.degree v = 4)
    (hRedges : #(G.induce (exteriorFinset G v : Set V)).edgeFinset = 25) :
    OrderFifteenThirtySixOneCrossStructure G := by
  classical
  let N := G.neighborFinset v
  let U := exteriorFinset G v
  let R := G.induce (U : Set V)
  let C : Finset V := insert v N
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
  have hRedgesR : #R.edgeFinset = 25 := by simpa [R, U] using hRedges
  have hnotbip : ¬Rᶜ.IsBipartite := by
    intro hbip
    exact hnotColorable
      (compl_colorable_three_of_bipartite_compl_exterior_degree_four
        G hG hfree hcard v hdegree (by simpa [R, U] using hbip))
  have hpartition := card_edgeFinset_add_card_compl R
  rw [hUcard, hRedgesR] at hpartition
  norm_num [Nat.choose] at hpartition
  have hLedges : #Rᶜ.edgeFinset = 20 := by omega
  have hiso :=
    compl_iso_balancedC5Blowup_of_admissible_order_ten_equality
      R hRadmissible hRfree hUcard hnotbip hLedges
  have haccountExact :=
    card_edges_eq_exterior_add_degree_add_accounting G v
  have haccount : neighborhoodCrossEdgeCount G v +
      neighborhoodInternalEdgeCount G v = 7 := by
    have haccount' : #R.edgeFinset + G.degree v +
        (neighborhoodCrossEdgeCount G v +
          neighborhoodInternalEdgeCount G v) = #G.edgeFinset := by
      simpa [R, U] using haccountExact
    rw [hRedgesR, hdegree, hedges] at haccount'
    omega
  have htwice := neighborhood_cross_add_twice_internal_ge G v hmin
  rw [hdegree] at htwice
  norm_num at htwice
  have hYupper := neighborhoodInternalEdgeCount_le_choose_degree G v
  rw [hdegree] at hYupper
  norm_num [Nat.choose] at hYupper
  have hYlower : 5 ≤ neighborhoodInternalEdgeCount G v := by omega
  have hY : neighborhoodInternalEdgeCount G v = 6 := by
    by_contra hne
    have hYfive : neighborhoodInternalEdgeCount G v = 5 := by omega
    exact false_of_orderFifteen_exterior_twentyFive_internal_five
      G hG hfree hcard hedges hnotColorable v hdegree hRedges hYfive
  have hX : neighborhoodCrossEdgeCount G v = 1 := by omega
  have hYchoose : neighborhoodInternalEdgeCount G v =
      (G.degree v).choose 2 := by
    rw [hdegree]
    norm_num [Nat.choose]
    exact hY
  have hCclique :=
    closedNeighborhood_isClique_of_internal_eq_choose G v hYchoose
  have hCcard : #C = 5 := by
    simp [C, N, G.notMem_neighborFinset_self v,
      SimpleGraph.card_neighborFinset_eq_degree, hdegree]
  have hcrossGraphs :
      G.between (C : Set V) (U : Set V) =
        G.between (N : Set V) (U : Set V) := by
    simpa [C, N, U] using
      between_closedNeighborhood_exterior_eq_between_neighbor_exterior G v
  have hcrossCard :
      #(G.between (C : Set V) (U : Set V)).edgeFinset =
        #(G.between (N : Set V) (U : Set V)).edgeFinset :=
    congrArg Finset.card (SimpleGraph.edgeFinset_inj.mpr hcrossGraphs)
  have hCcross :
      #(G.between (C : Set V) ((Cᶜ : Finset V) : Set V)).edgeFinset = 1 := by
    rw [show (Cᶜ : Finset V) = U by rfl]
    calc
      #(G.between (C : Set V) (U : Set V)).edgeFinset =
          #(G.between (N : Set V) (U : Set V)).edgeFinset := hcrossCard
      _ = 1 := by simpa [N, U, neighborhoodCrossEdgeCount] using hX
  refine ⟨C, hCcard, ?_, hCcross, ?_⟩
  · simpa [C, N] using hCclique
  · rw [show (Cᶜ : Finset V) = U by rfl]
    simpa [R] using hiso

/-- The two stated thirty-six-edge structures exhaust all admissible
order-fifteen graphs in the non-three-colorable independence-four branch. -/
theorem orderFifteenThirtySixStructure_or_of_admissible
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (hcard : Fintype.card V = 15) (hedges : #G.edgeFinset = 36)
    (hnotColorable : ¬Gᶜ.Colorable 3) :
    OrderFifteenThirtySixOneCrossStructure G ∨
      OrderFifteenThirtySixIsolatedStructure G := by
  classical
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
  have hRupper : #R.edgeFinset ≤ 26 := by
    have hsplit' : #R.edgeFinset + G.degree v + (G.degree v).choose 2 ≤
        #G.edgeFinset := by simpa [R, U] using hsplit
    rw [hdegree, hedges] at hsplit'
    norm_num [Nat.choose] at hsplit'
    omega
  have hRnotLeTwentyFour : ¬#R.edgeFinset ≤ 24 := by
    intro hRle
    have hpartition := card_edgeFinset_add_card_compl R
    rw [hUcard] at hpartition
    norm_num [Nat.choose] at hpartition
    by_cases hbip : Rᶜ.IsBipartite
    · exact hnotColorable
        (compl_colorable_three_of_bipartite_compl_exterior_degree_four
          G hG hfree hcard v hdegree (by simpa [R, U] using hbip))
    · have hLupper :=
        card_compl_edges_le_twenty_of_admissible_order_ten_nonbipartite
          R hRadmissible hRfree hUcard hbip
      omega
  have hRcases : #R.edgeFinset = 25 ∨ #R.edgeFinset = 26 := by omega
  rcases hRcases with hRtwentyFive | hRtwentySix
  · exact Or.inl
      (orderFifteenThirtySixOneCrossStructure_of_exterior_twentyFive
        G hG hfree hcard hedges hnotColorable v hmin hdegree
          (by simpa [R, U] using hRtwentyFive))
  · exact Or.inr
      (orderFifteenThirtySixIsolatedStructure_of_exterior_twentySix
        G hG hfree hcard hedges v hmin hdegree
          (by simpa [R, U] using hRtwentySix))

/-- No edge crosses from an isolated clique to its finite complement. -/
theorem card_between_compl_eq_zero_of_isIsolatedCliqueOn
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V)
    (hC : IsIsolatedCliqueOn G C) :
    #(G.between (C : Set V) ((Cᶜ : Finset V) : Set V)).edgeFinset = 0 := by
  classical
  have hbot :
      G.between (C : Set V) ((Cᶜ : Finset V) : Set V) = ⊥ := by
    rw [SimpleGraph.eq_bot_iff_forall_not_adj]
    intro a b hab
    have hparts := SimpleGraph.between_adj.mp hab
    rcases hparts.2 with ⟨haC, hbComp⟩ | ⟨haComp, hbC⟩
    · exact hC.2 haC (by simpa using hbComp) hparts.1
    · exact hC.2 hbC (by simpa using haComp) hparts.1.symm
  have hedgeEq :=
    congrArg Finset.card (SimpleGraph.edgeFinset_inj.mpr hbot)
  simpa using hedgeEq

/-- The one-cross-edge and isolated-clique alternatives are incompatible,
even before fixing the total edge count. -/
theorem orderFifteenThirtySixStructures_incompatible
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ¬(OrderFifteenThirtySixOneCrossStructure G ∧
      OrderFifteenThirtySixIsolatedStructure G) := by
  classical
  rintro ⟨hone, hisolated⟩
  rcases hone with
    ⟨C₁, hC₁card, hC₁clique, hC₁cross, hC₁residual⟩
  rcases hisolated with
    ⟨C₂, hC₂card, hC₂isolated, hC₂residual⟩
  dsimp at hC₂residual
  have hdis : Disjoint C₁ C₂ := by
    rw [Finset.disjoint_left]
    intro x hxC₁ hxC₂
    have hsub : C₁ ⊆ C₂ := by
      intro y hyC₁
      by_contra hyC₂
      have hxy : x ≠ y := by
        intro h
        subst y
        exact hyC₂ hxC₂
      have hGxy : G.Adj x y := hC₁clique hxC₁ hyC₁ hxy
      exact hC₂isolated.2 hxC₂ hyC₂ hGxy
    have hCeq : C₁ = C₂ := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [hC₁card, hC₂card]
    subst C₁
    have hzero :=
      card_between_compl_eq_zero_of_isIsolatedCliqueOn
        G C₂ hC₂isolated
    omega
  let U : Finset V := C₂ᶜ
  have hC₁sub : C₁ ⊆ U := by
    intro x hxC₁
    have hxNotC₂ : x ∉ C₂ := fun hxC₂ =>
      (Finset.disjoint_left.mp hdis) hxC₁ hxC₂
    simpa [U] using hxNotC₂
  let fU : (U : Set V) ↪ V := Function.Embedding.subtype _
  let S : Finset (U : Set V) :=
    Finset.univ.filter fun x => (x : V) ∈ C₁
  have hSmap : S.map fU = C₁ := by
    ext x
    constructor
    · intro hx
      obtain ⟨x', hx'S, hx'eq⟩ := Finset.mem_map.mp hx
      subst x
      change (x' : V) ∈ C₁
      simpa [S] using hx'S
    · intro hx
      have hxU := hC₁sub hx
      refine Finset.mem_map.mpr ⟨⟨x, hxU⟩, ?_, ?_⟩
      · simp [S, hx]
      · rfl
  have hScard : #S = 5 := by
    calc
      #S = #(S.map fU) := by simp
      _ = #C₁ := congrArg Finset.card hSmap
      _ = 5 := hC₁card
  let L := (G.induce (U : Set V))ᶜ
  have hLfree : L.IndepSetFree 5 := by
    simpa [L, U] using hC₂residual.2.2
  have hSind : L.IsIndepSet (S : Set (U : Set V)) := by
    intro x hxS y hyS hxy hxyL
    have hxC₁ : (x : V) ∈ C₁ := by simpa [S] using hxS
    have hyC₁ : (y : V) ∈ C₁ := by simpa [S] using hyS
    have hxyVal : (x : V) ≠ (y : V) := fun h => hxy (Subtype.ext h)
    have hGxy : G.Adj (x : V) (y : V) :=
      hC₁clique hxC₁ hyC₁ hxyVal
    have hnotGxy : ¬G.Adj (x : V) (y : V) := by
      simpa [L, U] using hxyL.2
    exact hnotGxy hGxy
  exact hLfree S ⟨hSind, hScard⟩

/-- Exact exclusive form of the order-fifteen, thirty-six-edge
classification. -/
theorem orderFifteenThirtySixStructure_xor_of_admissible
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (hcard : Fintype.card V = 15) (hedges : #G.edgeFinset = 36)
    (hnotColorable : ¬Gᶜ.Colorable 3) :
    Xor (OrderFifteenThirtySixOneCrossStructure G)
      (OrderFifteenThirtySixIsolatedStructure G) := by
  have hor := orderFifteenThirtySixStructure_or_of_admissible
    G hG hfree hcard hedges hnotColorable
  have hinc := orderFifteenThirtySixStructures_incompatible G
  rcases hor with hone | hisolated
  · exact Or.inl ⟨hone, fun hiso => hinc ⟨hone, hiso⟩⟩
  · exact Or.inr ⟨hisolated, fun hone => hinc ⟨hone, hisolated⟩⟩

end Erdos617
