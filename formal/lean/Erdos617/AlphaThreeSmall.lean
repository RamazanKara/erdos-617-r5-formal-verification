/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.OrderTenStructure
public import Mathlib.Tactic.IntervalCases

/-!
# Small admissible independence-three obstructions

This module propagates the kernel-checked order-ten and order-eleven terminal
theorems through the remaining small minimum-degree cases.  The only
structural branch is order sixteen at minimum degree five.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

universe u

/-- Four pairwise distinct, pairwise nonadjacent vertices contradict
`IndepSetFree 4`. -/
theorem false_of_indepSetFree_four_of_pairwise_nonadj
    {V : Type u} (G : SimpleGraph V)
    (hfree : G.IndepSetFree 4) {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hnab : ¬G.Adj a b) (hnac : ¬G.Adj a c) (hnad : ¬G.Adj a d)
    (hnbc : ¬G.Adj b c) (hnbd : ¬G.Adj b d) (hncd : ¬G.Adj c d) :
    False := by
  classical
  let S : Finset V := {a, b, c, d}
  apply hfree S
  constructor
  · intro x hx y hy hxy hxyG
    have hx' : x = a ∨ x = b ∨ x = c ∨ x = d := by
      simpa [S] using hx
    have hy' : y = a ∨ y = b ∨ y = c ∨ y = d := by
      simpa [S] using hy
    rcases hx' with rfl | rfl | rfl | rfl <;>
      rcases hy' with rfl | rfl | rfl | rfl <;>
      simp_all only [SimpleGraph.irrefl, SimpleGraph.adj_comm] <;>
      contradiction
  · simp [S, hab, hac, had, hbc, hbd, hcd]

/-- The incidences at the endpoints of an edge overlap in exactly that edge. -/
theorem degree_add_degree_le_card_edges_add_one_of_adj
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V}
    (hab : G.Adj a b) :
    G.degree a + G.degree b ≤ #G.edgeFinset + 1 := by
  classical
  let Ia := G.incidenceFinset a
  let Ib := G.incidenceFinset b
  have hUnionSub : Ia ∪ Ib ⊆ G.edgeFinset :=
    Finset.union_subset (G.incidenceFinset_subset a) (G.incidenceFinset_subset b)
  have hUnionCard : #(Ia ∪ Ib) ≤ #G.edgeFinset :=
    Finset.card_le_card hUnionSub
  have hInter : Ia ∩ Ib = {s(a, b)} := by
    apply Finset.coe_injective
    simpa [Ia, Ib] using G.incidenceSet_inter_incidenceSet_of_adj hab
  have hIdentity := Finset.card_union_add_card_inter Ia Ib
  calc
    G.degree a + G.degree b = #Ia + #Ib := by simp [Ia, Ib]
    _ = #(Ia ∪ Ib) + #(Ia ∩ Ib) := hIdentity.symm
    _ = #(Ia ∪ Ib) + 1 := by simp [hInter]
    _ ≤ #G.edgeFinset + 1 := Nat.add_le_add_right hUnionCard 1

/-- The bipartite-complement order-ten exterior cannot occur at a degree-five
vertex of an admissible order-sixteen graph with no independent four-set. -/
theorem false_of_bipartite_compl_exterior_degree_five_card_sixteen
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (hcard : Fintype.card V = 16) (v : V) (hdegree : G.degree v = 5)
    (hbip : (G.induce (exteriorFinset G v : Set V))ᶜ.IsBipartite) :
    False := by
  classical
  let N := G.neighborFinset v
  let U := exteriorFinset G v
  let R := G.induce (U : Set V)
  have hUcardRaw := card_exterior_type_add_degree_add_one G v
  have hUcard : Fintype.card (U : Set V) = 10 := by
    rw [hcard, hdegree] at hUcardRaw
    simpa [U] using (show Fintype.card (exteriorFinset G v : Set V) = 10 by
      omega)
  have hRadmissible : Admissible R := by
    simpa [R, U] using admissible_induce G hG U
  obtain ⟨A, B, hAcard, hBcard, hABdis, hABcover,
      hAclique, hBclique, hAmatch, hBmatch⟩ :=
    exists_bipartition_order_ten R hRadmissible hUcard (by simpa [R, U] using hbip)
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
  have hA0indComp : Gᶜ.IsIndepSet (A0 : Set V) := by
    simpa using hA0clique
  have hB0indComp : Gᶜ.IsIndepSet (B0 : Set V) := by
    simpa using hB0clique
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
  have hNclique : G.IsClique (N : Set V) := by
    intro a haN b hbN hab
    by_contra hnab
    let badA := (A.filter fun x : (U : Set V) => G.Adj a (x : V)) ∪
      (A.filter fun x : (U : Set V) => G.Adj b (x : V))
    let goodA := A \ badA
    let badB := (B.filter fun x : (U : Set V) => G.Adj a (x : V)) ∪
      (B.filter fun x : (U : Set V) => G.Adj b (x : V))
    let goodB := B \ badB
    have hbadAsub : badA ⊆ A := by
      exact Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hbadBsub : badB ⊆ B := by
      exact Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
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
    have hTsub : T ⊆ goodB := Finset.filter_subset _ _
    have hTneighborSub : T ⊆ (R.between (A : Set _) (B : Set _)).neighborFinset x := by
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
  let S : Finset V := insert v N
  have hvNotN : v ∉ N := by simp [N]
  have hScard : #S = 6 := by
    simp [S, hvNotN, N, SimpleGraph.card_neighborFinset_eq_degree, hdegree]
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

/-- The nonbipartite equality-case order-ten exterior also contradicts a
degree-five minimum vertex in the putative order-sixteen obstruction. -/
theorem false_of_nonbipartite_compl_exterior_degree_five_card_sixteen
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (hcard : Fintype.card V = 16) (hedgeUpper : #G.edgeFinset ≤ 44)
    (v : V) (hdegree : G.degree v = 5)
    (hmin : ∀ w, G.degree v ≤ G.degree w)
    (hnotbip : ¬(G.induce (exteriorFinset G v : Set V))ᶜ.IsBipartite) :
    False := by
  classical
  let N := G.neighborFinset v
  let U := exteriorFinset G v
  let R := G.induce (U : Set V)
  let L := Rᶜ
  let C := G.between (N : Set V) (U : Set V)
  let H := G.induce (N : Set V)
  let M := Hᶜ
  have hNcard : #N = 5 := by simp [N, hdegree]
  have hNtype : Fintype.card (N : Set V) = 5 := by simpa using hNcard
  have hUcardRaw := card_exterior_type_add_degree_add_one G v
  have hUcard : Fintype.card (U : Set V) = 10 := by
    rw [hcard, hdegree] at hUcardRaw
    simpa [U] using (show Fintype.card (exteriorFinset G v : Set V) = 10 by
      omega)
  have hRadmissible : Admissible R := by
    simpa [R, U] using admissible_induce G hG U
  have hRfree : R.IndepSetFree 3 := by
    simpa [R, U] using
      (indepSetFree_exterior_induce G (k := 3) (by simpa using hfree) v)
  have hRupperRaw :=
    exterior_edges_add_nineteen_le_edges_of_admissible_degree_five
      G hG v hdegree hmin
  have hRupper : #R.edgeFinset ≤ 25 := by
    simpa [R, U] using (show #(G.induce (exteriorFinset G v : Set V)).edgeFinset ≤ 25 by
      omega)
  have hLupper :=
    card_compl_edges_le_twenty_of_admissible_order_ten_nonbipartite
      R hRadmissible hRfree hUcard (by simpa [L, R, U] using hnotbip)
  have hpartitionR := card_edgeFinset_add_card_compl R
  rw [hUcard] at hpartitionR
  norm_num [Nat.choose] at hpartitionR
  have hRedges : #R.edgeFinset = 25 := by omega
  have hLedges : #L.edgeFinset = 20 := by
    simpa [L] using (show #Rᶜ.edgeFinset = 20 by omega)
  have hRcontribution : #R.edgeFinset + 19 ≤ #G.edgeFinset := by
    simpa [R, U] using hRupperRaw
  have hGedges : #G.edgeFinset = 44 := by omega
  have hsplit := exterior_edges_add_degree_add_accounting_le_edges G v
  have haccount := neighborhood_cross_add_internal_ge_fourteen
    G hG v hdegree hmin
  have hYupper := neighborhoodInternalEdgeCount_le_six_of_admissible_degree_five
    G hG v hdegree
  have htwice := neighborhood_cross_add_twice_internal_ge G v hmin
  rw [hdegree] at htwice
  norm_num at htwice
  have hX : neighborhoodCrossEdgeCount G v = 8 := by
    have hsplit' : 25 + 5 +
        (neighborhoodCrossEdgeCount G v + neighborhoodInternalEdgeCount G v) ≤ 44 := by
      simpa [R, U, hRedges, hGedges, hdegree] using hsplit
    omega
  have hY : neighborhoodInternalEdgeCount G v = 6 := by
    have hsplit' : 25 + 5 +
        (neighborhoodCrossEdgeCount G v + neighborhoodInternalEdgeCount G v) ≤ 44 := by
      simpa [R, U, hRedges, hGedges, hdegree] using hsplit
    omega
  have hHedges : #H.edgeFinset = 6 := by
    have hi := neighborhoodInternalEdgeCount_eq_induce G v
    rw [hY] at hi
    simpa [H, N] using hi.symm
  have hMpartition := card_edgeFinset_add_card_compl H
  rw [hNtype, hHedges] at hMpartition
  norm_num [Nat.choose] at hMpartition
  have hMedges : #M.edgeFinset = 4 := by
    change #Hᶜ.edgeFinset = 4
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
  have hCbip : C.IsBipartiteWith (N : Set V) (U : Set V) := by
    simpa [C] using SimpleGraph.between_isBipartiteWith (G := G) hNUdisSet
  have hCedges : #C.edgeFinset = 8 := by
    simpa [C, neighborhoodCrossEdgeCount, N, U] using hX
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
      _ = #(G.neighborFinset (a : V) ∩ N) := by
        exact congrArg Finset.card hmap
      _ = #((neighborhoodInternalGraph G v).neighborFinset (a : V)) :=
        congrArg Finset.card hneighbors
      _ = (neighborhoodInternalGraph G v).degree (a : V) :=
        SimpleGraph.card_neighborFinset_eq_degree _ _
  have hPointLe (a : (N : Set V)) : M.degree a ≤ C.degree (a : V) := by
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
  have hSumCbase : (∑ a ∈ N, C.degree a) = 8 := by
    have hs := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hCbip
    rw [hCedges] at hs
    exact hs
  have hSumC : (∑ a : (N : Set V), C.degree (a : V)) = 8 := by
    have hs := Finset.sum_attach N (fun a => C.degree a)
    rw [Finset.attach_eq_univ] at hs
    calc
      (∑ a : (N : Set V), C.degree (a : V)) = ∑ a ∈ N, C.degree a := hs
      _ = 8 := hSumCbase
  have hPointEq (a : (N : Set V)) : M.degree a = C.degree (a : V) := by
    have hsumEq : (∑ x : (N : Set V), M.degree x) =
        ∑ x : (N : Set V), C.degree (x : V) := by omega
    have hp := (Finset.sum_eq_sum_iff_of_le
      (s := (Finset.univ : Finset (N : Set V)))
      (fun x _ => hPointLe x)).mp hsumEq
    exact hp a (Finset.mem_univ a)
  have hMnonempty : M.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨e, he⟩ := hMnonempty
  induction e using Sym2.inductionOn with
  | hf a b =>
    have habM : M.Adj a b := by simpa using he
    let K0 : Finset V := C.neighborFinset (a : V) ∪ C.neighborFinset (b : V)
    have hCaSub : C.neighborFinset (a : V) ⊆ U :=
      SimpleGraph.isBipartiteWith_neighborFinset_subset hCbip a.property
    have hCbSub : C.neighborFinset (b : V) ⊆ U :=
      SimpleGraph.isBipartiteWith_neighborFinset_subset hCbip b.property
    have hK0sub : K0 ⊆ U := Finset.union_subset hCaSub hCbSub
    let fU : (U : Set V) ↪ V := Function.Embedding.subtype _
    let K : Finset (U : Set V) := Finset.univ.filter fun x => (x : V) ∈ K0
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
    have hMpair := degree_add_degree_le_card_edges_add_one_of_adj M habM
    rw [hMedges] at hMpair
    have hKcard : #K ≤ 5 := by
      have hu := Finset.card_union_le
        (C.neighborFinset (a : V)) (C.neighborFinset (b : V))
      have haeq := hPointEq a
      have hbeq := hPointEq b
      simp only [SimpleGraph.card_neighborFinset_eq_degree] at hu
      calc
        #K = #K0 := hKcardBase
        _ = #(C.neighborFinset (a : V) ∪ C.neighborFinset (b : V)) := by rfl
        _ ≤ C.degree (a : V) + C.degree (b : V) := hu
        _ = M.degree a + M.degree b := by rw [haeq, hbeq]
        _ ≤ 5 := by omega
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
      have hxAvoid : ¬G.Adj (a : V) (x : V) ∧ ¬G.Adj (b : V) (x : V) := by
        have hxParts :
            (x : V) ∉ C.neighborFinset (a : V) ∧
              (x : V) ∉ C.neighborFinset (b : V) := by
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
      have hyAvoid : ¬G.Adj (a : V) (y : V) ∧ ¬G.Adj (b : V) (y : V) := by
        have hyParts :
            (y : V) ∉ C.neighborFinset (a : V) ∧
              (y : V) ∉ C.neighborFinset (b : V) := by
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
      have hab : (a : V) ≠ (b : V) := fun h => habM.ne (Subtype.ext h)
      have hax : (a : V) ≠ (x : V) := fun h =>
        (Finset.disjoint_left.mp hNUdis) a.property (h ▸ x.property)
      have hay : (a : V) ≠ (y : V) := fun h =>
        (Finset.disjoint_left.mp hNUdis) a.property (h ▸ y.property)
      have hbx : (b : V) ≠ (x : V) := fun h =>
        (Finset.disjoint_left.mp hNUdis) b.property (h ▸ x.property)
      have hby : (b : V) ≠ (y : V) := fun h =>
        (Finset.disjoint_left.mp hNUdis) b.property (h ▸ y.property)
      have hxy : (x : V) ≠ (y : V) := fun h => hxyL.ne (Subtype.ext h)
      exact false_of_indepSetFree_four_of_pairwise_nonadj G hfree
        hab hax hay hbx hby hxy habG hxAvoid.1 hyAvoid.1
        hxAvoid.2 hyAvoid.2 hxyG
    have hcoverUpper : L.vertexCoverNum ≤ (5 : ℕ∞) := by
      calc
        L.vertexCoverNum ≤ (K : Set (U : Set V)).encard := hKcover.vertexCoverNum_le
        _ = (#K : ℕ∞) := by simp
        _ ≤ (5 : ℕ∞) := by exact_mod_cast hKcard
    have hcoverEq :=
      compl_vertexCoverNum_eq_six_of_admissible_order_ten_equality
        R hRadmissible hRfree hUcard (by simpa [L, R, U] using hnotbip)
          (by simpa [L] using hLedges)
    rw [show L.vertexCoverNum = 6 by simpa [L] using hcoverEq] at hcoverUpper
    norm_num at hcoverUpper

/-- An admissible order-sixteen graph with no independent four-set has at
least forty-five edges.  The degree-five endpoint uses the complete
order-ten structure theorem above. -/
theorem card_edges_ge_fortyFive_of_admissible_indepSetFree_four_card_sixteen
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (hcard : Fintype.card V = 16) :
    45 ≤ #G.edgeFinset := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  by_contra hnot
  have hedgeUpper : #G.edgeFinset ≤ 44 := by omega
  obtain ⟨v, hmin, havg⟩ :=
    exists_minimal_vertex_card_mul_degree_le_twice_edges G
  have hdegreeCap : G.degree v ≤ 5 := by
    rw [hcard] at havg
    omega
  let U := exteriorFinset G v
  let R := G.induce (U : Set V)
  have hUcard := card_exterior_type_add_degree_add_one G v
  rw [hcard] at hUcard
  have hUcardU : Fintype.card (U : Set V) + G.degree v + 1 = 16 := by
    simpa [U] using hUcard
  have hRadmissible : Admissible R := by
    simpa [R] using admissible_induce G hG U
  have hRfree : R.IndepSetFree 3 := by
    simpa [R, U] using
      (indepSetFree_exterior_induce G (k := 3) (by simpa using hfree) v)
  have hsplit := exterior_edges_add_degree_add_choose_le_edges G v hmin
  have hsplitR : #R.edgeFinset + G.degree v + (G.degree v).choose 2 ≤
      #G.edgeFinset := by
    simpa [R, U] using hsplit
  interval_cases hdegree : G.degree v
  · have hRcard : Fintype.card (U : Set V) = 15 := by omega
    have hRbound :=
      choose_card_le_edges_add_twice_card_of_admissible_indepSetFree_three
        R hRadmissible hRfree (by omega : 12 ≤ Fintype.card (U : Set V))
    rw [hRcard] at hRbound
    norm_num [hdegree, Nat.choose] at hsplitR hRbound
    omega
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
  · by_cases hbip : Rᶜ.IsBipartite
    · exact false_of_bipartite_compl_exterior_degree_five_card_sixteen
        G hG hfree hcard v hdegree (by simpa [R, U] using hbip)
    · exact false_of_nonbipartite_compl_exterior_degree_five_card_sixteen
        G hG hfree hcard hedgeUpper v hdegree
          (fun w => by simpa [hdegree] using hmin w)
          (by simpa [R, U] using hbip)

/-- An admissible order-seventeen graph with no independent four-set has at
least fifty edges. -/
theorem card_edges_ge_fifty_of_admissible_indepSetFree_four_card_seventeen
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (hcard : Fintype.card V = 17) :
    50 ≤ #G.edgeFinset := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  by_contra hnot
  have hedgeLt : #G.edgeFinset < 50 := by omega
  obtain ⟨v, hmin, havg⟩ :=
    exists_minimal_vertex_card_mul_degree_le_twice_edges G
  have hdegreeCap : G.degree v ≤ 5 := by
    rw [hcard] at havg
    omega
  let U := exteriorFinset G v
  let R := G.induce (U : Set V)
  have hUcard := card_exterior_type_add_degree_add_one G v
  rw [hcard] at hUcard
  have hUcardU : Fintype.card (U : Set V) + G.degree v + 1 = 17 := by
    simpa [U] using hUcard
  have hRadmissible : Admissible R := by
    simpa [R] using admissible_induce G hG U
  have hRfree : R.IndepSetFree 3 := by
    simpa [R, U] using
      (indepSetFree_exterior_induce G (k := 3) (by simpa using hfree) v)
  have hsplit := exterior_edges_add_degree_add_choose_le_edges G v hmin
  have hsplitR : #R.edgeFinset + G.degree v + (G.degree v).choose 2 ≤
      #G.edgeFinset := by
    simpa [R, U] using hsplit
  interval_cases hdegree : G.degree v
  · have hRcard : Fintype.card (U : Set V) = 16 := by omega
    have hRbound :=
      choose_card_le_edges_add_twice_card_of_admissible_indepSetFree_three
        R hRadmissible hRfree (by omega : 12 ≤ Fintype.card (U : Set V))
    rw [hRcard] at hRbound
    norm_num [hdegree, Nat.choose] at hsplitR hRbound
    omega
  · have hRcard : Fintype.card (U : Set V) = 15 := by omega
    have hRbound :=
      choose_card_le_edges_add_twice_card_of_admissible_indepSetFree_three
        R hRadmissible hRfree (by omega : 12 ≤ Fintype.card (U : Set V))
    rw [hRcard] at hRbound
    norm_num [hdegree, Nat.choose] at hsplitR hRbound
    omega
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
    have hstrong :=
      exterior_edges_add_nineteen_le_edges_of_admissible_degree_five
        G hG v hdegree (fun w => by simpa [hdegree] using hmin w)
    have hstrongR : #R.edgeFinset + 19 ≤ #G.edgeFinset := by
      simpa [R, U] using hstrong
    omega

/-- Exact graph-theoretic form of the three small independence-three
obstructions: none of the manuscript's three order/edge ranges is possible. -/
theorem false_of_admissible_indepSetFree_four_small_range
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (hrange :
      (Fintype.card V = 16 ∧ #G.edgeFinset ≤ 44) ∨
      (Fintype.card V = 17 ∧ #G.edgeFinset ≤ 49) ∨
      (Fintype.card V = 18 ∧ #G.edgeFinset ≤ 53)) :
    False := by
  rcases hrange with h16 | h17 | h18
  · have hlower :=
      card_edges_ge_fortyFive_of_admissible_indepSetFree_four_card_sixteen
        G hG hfree h16.1
    omega
  · have hlower :=
      card_edges_ge_fifty_of_admissible_indepSetFree_four_card_seventeen
        G hG hfree h17.1
    omega
  · have hlower :=
      card_edges_ge_fiftyFour_of_admissible_indepSetFree_four_card_eighteen
        G hG hfree h18.1
    omega

end Erdos617
