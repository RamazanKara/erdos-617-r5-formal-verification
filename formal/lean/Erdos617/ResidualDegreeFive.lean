/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.ResidualDegreeFour

/-!
# The minimum-degree-five branch of the final order-21 residual

This module eliminates the final graph-theoretic residual produced by edge
equalization.  The order-fifteen exterior is split by its exact edge count and
the two structures proved in `OrderFifteenStructure`.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

universe u

/-- Cross-neighbors restricted to a residual finset inside an exterior. -/
def residualCrossNeighborFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (N U : Finset V) (Q : Finset (U : Set V)) (a : (N : Set V)) :
    Finset (Q : Set (U : Set V)) :=
  Finset.univ.filter fun x => G.Adj (a : V) (x : V)

@[simp]
theorem mem_residualCrossNeighborFinset_iff
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (N U : Finset V) (Q : Finset (U : Set V))
    (a : (N : Set V)) (x : (Q : Set (U : Set V))) :
    x ∈ residualCrossNeighborFinset G N U Q a ↔
      G.Adj (a : V) (x : V) := by
  simp [residualCrossNeighborFinset]

/-- Restricting the exterior can only decrease a cross-degree. -/
theorem card_residualCrossNeighborFinset_le_between_degree
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (N U : Finset V) (Q : Finset (U : Set V))
    (hNUdis : Disjoint N U) (a : (N : Set V)) :
    #(residualCrossNeighborFinset G N U Q a) ≤
      (G.between (N : Set V) (U : Set V)).degree (a : V) := by
  classical
  let K := residualCrossNeighborFinset G N U Q a
  let fQ : (Q : Set (U : Set V)) ↪ (U : Set V) :=
    Function.Embedding.subtype _
  have hmapSub : K.map fQ ⊆ crossNeighborFinset G N U a := by
    intro x hx
    obtain ⟨x', hx'K, rfl⟩ := Finset.mem_map.mp hx
    exact (mem_crossNeighborFinset_iff G N U a (x' : (U : Set V))).2
      ((mem_residualCrossNeighborFinset_iff G N U Q a x').1
        (by simpa [K] using hx'K))
  calc
    #K = #(K.map fQ) := by simp
    _ ≤ #(crossNeighborFinset G N U a) := Finset.card_le_card hmapSub
    _ = (G.between (N : Set V) (U : Set V)).degree (a : V) :=
      card_crossNeighborFinset_eq_between_degree G N U hNUdis a

/-- An isolated residual witness upgrades the usual uncovered-edge argument
from an independent four-set to an independent five-set. -/
theorem residualCrossNeighbor_union_isVertexCover_with_avoider
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : G.IndepSetFree 5)
    (N U : Finset V) (Q : Finset (U : Set V))
    (hNUdis : Disjoint N U)
    (a b : (N : Set V)) (hab : (a : V) ≠ (b : V))
    (habG : ¬G.Adj (a : V) (b : V))
    (c : (U : Set V)) (hcNotQ : c ∉ Q)
    (hacG : ¬G.Adj (a : V) (c : V))
    (hbcG : ¬G.Adj (b : V) (c : V))
    (L : SimpleGraph (Q : Set (U : Set V)))
    (hLnonadj : ∀ ⦃x y : (Q : Set (U : Set V))⦄, L.Adj x y →
      ¬G.Adj (x : V) (y : V))
    (hcNonadj : ∀ x : (Q : Set (U : Set V)),
      ¬G.Adj (c : V) (x : V)) :
    L.IsVertexCover
      ((residualCrossNeighborFinset G N U Q a ∪
        residualCrossNeighborFinset G N U Q b :
          Finset (Q : Set (U : Set V))) :
        Set (Q : Set (U : Set V))) := by
  classical
  intro x y hxyL
  by_contra hnot
  have hxNot : x ∉ residualCrossNeighborFinset G N U Q a ∧
      x ∉ residualCrossNeighborFinset G N U Q b := by
    simpa using (show x ∉ residualCrossNeighborFinset G N U Q a ∪
      residualCrossNeighborFinset G N U Q b from fun hx => hnot (Or.inl hx))
  have hyNot : y ∉ residualCrossNeighborFinset G N U Q a ∧
      y ∉ residualCrossNeighborFinset G N U Q b := by
    simpa using (show y ∉ residualCrossNeighborFinset G N U Q a ∪
      residualCrossNeighborFinset G N U Q b from fun hy => hnot (Or.inr hy))
  have hxAvoid : ¬G.Adj (a : V) (x : V) ∧
      ¬G.Adj (b : V) (x : V) := by
    exact ⟨fun h => hxNot.1
      ((mem_residualCrossNeighborFinset_iff G N U Q a x).2 h),
      fun h => hxNot.2
      ((mem_residualCrossNeighborFinset_iff G N U Q b x).2 h)⟩
  have hyAvoid : ¬G.Adj (a : V) (y : V) ∧
      ¬G.Adj (b : V) (y : V) := by
    exact ⟨fun h => hyNot.1
      ((mem_residualCrossNeighborFinset_iff G N U Q a y).2 h),
      fun h => hyNot.2
      ((mem_residualCrossNeighborFinset_iff G N U Q b y).2 h)⟩
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
    hcNotQ (Subtype.ext h ▸ x.property)
  have hcy : (c : V) ≠ (y : V) := fun h =>
    hcNotQ (Subtype.ext h ▸ y.property)
  have hxy : (x : V) ≠ (y : V) := fun h =>
    hxyL.ne (Subtype.ext (Subtype.ext h))
  exact false_of_indepSetFree_five_of_pairwise_nonadj G hfree
    hab hac hax hay hbc hbx hby hcx hcy hxy habG hacG hxAvoid.1
    hyAvoid.1 hbcG hxAvoid.2 hyAvoid.2 (hcNonadj x) (hcNonadj y)
    (hLnonadj hxyL)

/-- Two vertices outside an admissible five-clique have a common avoider in
the clique. -/
theorem exists_mem_clique_five_avoiding_pair
    {V : Type u} [Finite V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (C : Finset V)
    (hCcard : #C = 5) (hCclique : G.IsClique (C : Set V))
    (a b : V) (haNotC : a ∉ C) (hbNotC : b ∉ C) :
    ∃ c ∈ C, ¬G.Adj a c ∧ ¬G.Adj b c := by
  classical
  let bad := C.filter (G.Adj a) ∪ C.filter (G.Adj b)
  let good := C \ bad
  have hbadSub : bad ⊆ C :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hbadCard : #bad ≤ 2 := by
    have hu := Finset.card_union_le (C.filter (G.Adj a)) (C.filter (G.Adj b))
    have haLe := card_filter_adj_le_one_of_admissible_clique_five
      G hG C hCcard hCclique a haNotC
    have hbLe := card_filter_adj_le_one_of_admissible_clique_five
      G hG C hCcard hCclique b hbNotC
    change #(C.filter (G.Adj a) ∪ C.filter (G.Adj b)) ≤ 2
    omega
  have hgoodCard : 3 ≤ #good := by
    have hs := Finset.card_sdiff_of_subset hbadSub
    rw [hCcard] at hs
    have hs' : #good = 5 - #bad := by simpa [good] using hs
    omega
  obtain ⟨c, hcgood⟩ := Finset.card_pos.mp (by omega : 0 < #good)
  have hcC : c ∈ C := (Finset.mem_sdiff.mp hcgood).1
  have hcAvoid : ¬G.Adj a c ∧ ¬G.Adj b c := by
    have hcnot := (Finset.mem_sdiff.mp hcgood).2
    simpa [bad, hcC] using hcnot
  exact ⟨c, hcC, hcAvoid⟩

/-- The common-avoider can also be chosen away from one distinguished clique
vertex. -/
theorem exists_mem_clique_five_avoiding_pair_and_ne
    {V : Type u} [Finite V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (C : Finset V)
    (hCcard : #C = 5) (hCclique : G.IsClique (C : Set V))
    (a b c0 : V) (haNotC : a ∉ C) (hbNotC : b ∉ C) (hc0C : c0 ∈ C) :
    ∃ c ∈ C, c ≠ c0 ∧ ¬G.Adj a c ∧ ¬G.Adj b c := by
  classical
  let bad := insert c0 (C.filter (G.Adj a) ∪ C.filter (G.Adj b))
  let good := C \ bad
  have hbadSub : bad ⊆ C := by
    exact Finset.insert_subset hc0C
      (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  have hpairs : #(C.filter (G.Adj a) ∪ C.filter (G.Adj b)) ≤ 2 := by
    have hu := Finset.card_union_le (C.filter (G.Adj a)) (C.filter (G.Adj b))
    have haLe := card_filter_adj_le_one_of_admissible_clique_five
      G hG C hCcard hCclique a haNotC
    have hbLe := card_filter_adj_le_one_of_admissible_clique_five
      G hG C hCcard hCclique b hbNotC
    omega
  have hbadCard : #bad ≤ 3 := by
    have hi := Finset.card_insert_le c0
      (C.filter (G.Adj a) ∪ C.filter (G.Adj b))
    change #(insert c0 (C.filter (G.Adj a) ∪ C.filter (G.Adj b))) ≤ 3
    omega
  have hgoodCard : 2 ≤ #good := by
    have hs := Finset.card_sdiff_of_subset hbadSub
    rw [hCcard] at hs
    have hs' : #good = 5 - #bad := by simpa [good] using hs
    omega
  obtain ⟨c, hcgood⟩ := Finset.card_pos.mp (by omega : 0 < #good)
  have hcC : c ∈ C := (Finset.mem_sdiff.mp hcgood).1
  have hcNotBad := (Finset.mem_sdiff.mp hcgood).2
  have hc0 : c ≠ c0 := by
    intro h
    subst c
    exact hcNotBad (by simp [bad])
  have hcAvoid : ¬G.Adj a c ∧ ¬G.Adj b c := by
    have hcPair : c ∉ C.filter (G.Adj a) ∪ C.filter (G.Adj b) := by
      intro hc
      exact hcNotBad (by simp [bad, hc])
    simpa [hcC] using hcPair
  exact ⟨c, hcC, hc0, hcAvoid⟩

/-- A cut with one edge has a unique endpoint on either specified side. -/
theorem exists_left_endpoint_of_card_between_eq_one
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C Q : Finset V) (hCQdis : Disjoint C Q)
    (hedges : #(G.between (C : Set V) (Q : Set V)).edgeFinset = 1) :
    ∃ c0 ∈ C, ∀ c ∈ C, c ≠ c0 → ∀ q ∈ Q, ¬G.Adj c q := by
  classical
  let B := G.between (C : Set V) (Q : Set V)
  obtain ⟨e, hedgeEq⟩ := Finset.card_eq_one.mp (by simpa [B] using hedges)
  have hedgeEqB : B.edgeFinset = {e} := by simpa [B] using hedgeEq
  have he : e ∈ B.edgeFinset := by rw [hedgeEqB]; simp
  induction e using Sym2.inductionOn with
  | hf p q =>
    have hedgeEqB' : B.edgeFinset = {s(p, q)} := hedgeEqB
    have hpqB : B.Adj p q := by simpa using he
    have hpqParts := (SimpleGraph.between_adj.mp hpqB).2
    rcases hpqParts with hpq | hpq
    · refine ⟨p, hpq.1, ?_⟩
      intro c hcC hcp r hrQ hcr
      have hcrB : B.Adj c r := by
        exact ⟨hcr, Or.inl ⟨hcC, hrQ⟩⟩
      have hmem : s(c, r) ∈ B.edgeFinset := by simpa using hcrB
      rw [hedgeEqB'] at hmem
      have heq : s(c, r) = s(p, q) := by simpa only [Finset.mem_singleton] using hmem
      rcases Sym2.eq_iff.mp heq with hsame | hswap
      · exact hcp hsame.1
      · exact (Finset.disjoint_left.mp hCQdis) hcC (hswap.1 ▸ hpq.2)
    · refine ⟨q, hpq.2, ?_⟩
      intro c hcC hcq r hrQ hcr
      have hcrB : B.Adj c r := by
        exact ⟨hcr, Or.inl ⟨hcC, hrQ⟩⟩
      have hmem : s(c, r) ∈ B.edgeFinset := by simpa using hcrB
      rw [hedgeEqB'] at hmem
      have heq : s(c, r) = s(p, q) := by simpa only [Finset.mem_singleton] using hmem
      rcases Sym2.eq_iff.mp heq with hsame | hswap
      · exact (Finset.disjoint_left.mp hCQdis) hcC (hsame.1 ▸ hpq.1)
      · exact hcq hswap.1

/-- Every finite vertex cover of a graph isomorphic to the canonical
balanced `C5` blow-up has at least six vertices. -/
theorem six_le_card_of_vertexCover_of_iso_balancedC5Blowup
    {W : Type u}
    (L : SimpleGraph W) (iso : L ≃g balancedC5Blowup)
    (K : Finset W) (hcover : L.IsVertexCover (K : Set W)) :
    6 ≤ #K := by
  classical
  let f : W ↪ Fin 5 × Fin 2 := iso.toEquiv.toEmbedding
  let K' : Finset (Fin 5 × Fin 2) := K.map f
  have hK'cover : balancedC5Blowup.IsVertexCover (K' : Set _) := by
    have h :=
      (SimpleGraph.isVertexCover_image_iso iso (c := (K : Set W))).2 hcover
    simpa [K', f, Finset.coe_map] using h
  have hlower := six_le_card_of_balancedC5Blowup_vertexCover K' hK'cover
  simpa [K'] using hlower

/-- If every complementary-neighborhood edge supplies a minimum cover of a
canonical ten-vertex residual, one unit of cross-degree excess forces the
same star and fourteen-edge six-set as in the order-sixteen recursion.  The
cover premise is deliberately abstract: in the order-twenty-one application
it is proved separately for each edge by choosing an avoider in an isolated
five-clique. -/
theorem false_of_canonical_residual_excess_one_of_edge_covers
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (v : V) (N U : Finset V)
    (Q : Finset (U : Set V))
    (hN : N = G.neighborFinset v)
    (hU : U = exteriorFinset G v)
    (hNcard : #N = 5) (hNUdis : Disjoint N U)
    (L : SimpleGraph (Q : Set (U : Set V)))
    (iso : L ≃g balancedC5Blowup)
    (hMedges : #((G.induce (N : Set V))ᶜ).edgeFinset = 4)
    (hCedges : #(G.between (N : Set V) (U : Set V)).edgeFinset = 9)
    (hPointLe : ∀ a : (N : Set V),
      (G.induce (N : Set V))ᶜ.degree a ≤
        (G.between (N : Set V) (U : Set V)).degree (a : V))
    (hEdgeCover : ∀ ⦃a b : (N : Set V)⦄,
      (G.induce (N : Set V))ᶜ.Adj a b →
        L.IsVertexCover
          ((residualCrossNeighborFinset G N U Q a ∪
            residualCrossNeighborFinset G N U Q b :
              Finset (Q : Set (U : Set V))) :
            Set (Q : Set (U : Set V)))) :
    False := by
  classical
  let M := (G.induce (N : Set V))ᶜ
  let C := G.between (N : Set V) (U : Set V)
  have hNtype : Fintype.card (N : Set V) = 5 := by simpa using hNcard
  have hNUdisSet : Disjoint (N : Set V) (U : Set V) :=
    Finset.disjoint_coe.mpr hNUdis
  have hCbip : C.IsBipartiteWith (N : Set V) (U : Set V) := by
    simpa [C] using
      SimpleGraph.between_isBipartiteWith (G := G) hNUdisSet
  have hSumM : (∑ a : (N : Set V), M.degree a) = 8 := by
    have hs := M.sum_degrees_eq_twice_card_edges
    rw [show #M.edgeFinset = 4 by simpa [M] using hMedges] at hs
    norm_num at hs ⊢
    exact hs
  have hSumCbase : (∑ a ∈ N, C.degree a) = 9 := by
    have hs := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hCbip
    rw [show #C.edgeFinset = 9 by simpa [C] using hCedges] at hs
    exact hs
  have hSumC : (∑ a : (N : Set V), C.degree (a : V)) = 9 := by
    have hs := Finset.sum_attach N (fun a => C.degree a)
    rw [Finset.attach_eq_univ] at hs
    calc
      (∑ a : (N : Set V), C.degree (a : V)) =
          ∑ a ∈ N, C.degree a := hs
      _ = 9 := hSumCbase
  let excess (a : (N : Set V)) : ℕ := C.degree (a : V) - M.degree a
  have hExcessSum : (∑ a : (N : Set V), excess a) = 1 := by
    have hdecomp : (∑ a : (N : Set V), M.degree a) +
        (∑ a : (N : Set V), excess a) =
          ∑ a : (N : Set V), C.degree (a : V) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      dsimp [excess]
      have hle : M.degree a ≤ C.degree (a : V) := by
        simpa [M, C] using hPointLe a
      omega
    rw [hSumM, hSumC] at hdecomp
    omega
  have hExcessNe : (∑ a : (N : Set V), excess a) ≠ 0 := by
    rw [hExcessSum]
    norm_num
  obtain ⟨z, _hzMem, hzNe⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hExcessNe
  have hzExcess : excess z = 1 := by
    have hzLe : excess z ≤ ∑ a : (N : Set V), excess a :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ z)
    rw [hExcessSum] at hzLe
    omega
  have hExcessOther (a : (N : Set V)) (haz : a ≠ z) : excess a = 0 := by
    have hsplit :
        (∑ x ∈ (Finset.univ : Finset (N : Set V)).erase z, excess x) +
          excess z = ∑ x : (N : Set V), excess x :=
      Finset.sum_erase_add
        (Finset.univ : Finset (N : Set V)) excess (Finset.mem_univ z)
    have hrest : (∑ x ∈ (Finset.univ : Finset (N : Set V)).erase z,
        excess x) = 0 := by
      rw [hExcessSum, hzExcess] at hsplit
      omega
    have haMem : a ∈ (Finset.univ : Finset (N : Set V)).erase z := by
      simp [haz]
    have haLe : excess a ≤
        ∑ x ∈ (Finset.univ : Finset (N : Set V)).erase z, excess x :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) haMem
    rw [hrest] at haLe
    omega
  have hPointEqOther (a : (N : Set V)) (haz : a ≠ z) :
      M.degree a = C.degree (a : V) := by
    have hzero := hExcessOther a haz
    have hle : M.degree a ≤ C.degree (a : V) := by
      simpa [M, C] using hPointLe a
    dsimp [excess] at hzero
    omega
  have hPointZ : C.degree (z : V) = M.degree z + 1 := by
    have hle : M.degree z ≤ C.degree (z : V) := by
      simpa [M, C] using hPointLe z
    dsimp [excess] at hzExcess
    omega
  have hcoverLower : ∀ K : Finset (Q : Set (U : Set V)),
      L.IsVertexCover (K : Set (Q : Set (U : Set V))) → 6 ≤ #K := by
    intro K hK
    have hcoverEq : L.vertexCoverNum = 6 :=
      (SimpleGraph.vertexCoverNum_congr iso).trans
        balancedC5Blowup_vertexCoverNum
    have hle := hK.vertexCoverNum_le
    rw [hcoverEq] at hle
    simpa using hle
  have hEdgeMeet : ∀ ⦃a b : (N : Set V)⦄, M.Adj a b →
      a = z ∨ b = z := by
    intro a b habM
    by_contra hnot
    have haz : a ≠ z := fun h => hnot (Or.inl h)
    have hbz : b ≠ z := fun h => hnot (Or.inr h)
    let A : Finset (Q : Set (U : Set V)) :=
      residualCrossNeighborFinset G N U Q a
    let B : Finset (Q : Set (U : Set V)) :=
      residualCrossNeighborFinset G N U Q b
    have hcover : L.IsVertexCover ((A ∪ B : Finset _) : Set _) := by
      simpa [A, B, M] using hEdgeCover habM
    have hlower : 6 ≤ #(A ∪ B) := hcoverLower (A ∪ B) hcover
    have hu := Finset.card_union_le A B
    have haLe : #A ≤ C.degree (a : V) := by
      simpa [A, C] using
        card_residualCrossNeighborFinset_le_between_degree
          G N U Q hNUdis a
    have hbLe : #B ≤ C.degree (b : V) := by
      simpa [B, C] using
        card_residualCrossNeighborFinset_le_between_degree
          G N U Q hNUdis b
    have hupper := degree_add_degree_le_card_edges_add_one_of_adj M habM
    rw [show #M.edgeFinset = 4 by simpa [M] using hMedges] at hupper
    rw [hPointEqOther a haz, hPointEqOther b hbz] at hupper
    omega
  have hAllEdgesIncident : M.edgeFinset ⊆ M.incidenceFinset z := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf a b =>
      have habM : M.Adj a b := by simpa using he
      have hmeet := hEdgeMeet habM
      rw [SimpleGraph.mem_incidenceFinset,
        SimpleGraph.mk'_mem_incidenceSet_iff]
      exact ⟨habM, hmeet.imp Eq.symm Eq.symm⟩
  have hIncidenceEq : M.incidenceFinset z = M.edgeFinset :=
    Finset.Subset.antisymm (M.incidenceFinset_subset z) hAllEdgesIncident
  have hzMdegree : M.degree z = 4 := by
    rw [← SimpleGraph.card_incidenceFinset_eq_degree, hIncidenceEq]
    simpa [M] using hMedges
  have hEraseCard : #((Finset.univ : Finset (N : Set V)).erase z) = 4 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ z)]
    simpa using hNtype
  have hzNeighborEq : M.neighborFinset z =
      (Finset.univ : Finset (N : Set V)).erase z := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      have haz : a ≠ z := by
        intro h
        subst a
        exact M.notMem_neighborFinset_self z ha
      simp [haz]
    · rw [hEraseCard, SimpleGraph.card_neighborFinset_eq_degree, hzMdegree]
  have hzAdj (a : (N : Set V)) (haz : a ≠ z) : M.Adj z a := by
    rw [← SimpleGraph.mem_neighborFinset, hzNeighborEq]
    simp [haz]
  have hLeafMdegree (a : (N : Set V)) (haz : a ≠ z) : M.degree a = 1 := by
    have hneighbors : M.neighborFinset a = {z} := by
      ext b
      constructor
      · intro hb
        have habM : M.Adj a b := by
          rw [← SimpleGraph.mem_neighborFinset]
          exact hb
        have hmeet := hEdgeMeet habM
        have hbz : b = z := hmeet.resolve_left haz
        simp [hbz]
      · intro hb
        have hbz : b = z := by simpa using hb
        subst b
        rw [SimpleGraph.mem_neighborFinset]
        exact (hzAdj a haz).symm
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hneighbors]
    simp
  have hzCdegree : C.degree (z : V) = 5 := by omega
  have hLeafCdegree (a : (N : Set V)) (haz : a ≠ z) :
      C.degree (a : V) = 1 := by
    rw [← hPointEqOther a haz, hLeafMdegree a haz]
  let Z : Finset (Q : Set (U : Set V)) :=
    residualCrossNeighborFinset G N U Q z
  let A (a : (N : Set V)) : Finset (Q : Set (U : Set V)) :=
    residualCrossNeighborFinset G N U Q a
  let K (a : (N : Set V)) : Finset (Q : Set (U : Set V)) := Z ∪ A a
  have hZupper : #Z ≤ 5 := by
    calc
      #Z ≤ C.degree (z : V) := by
        simpa [Z, C] using
          card_residualCrossNeighborFinset_le_between_degree
            G N U Q hNUdis z
      _ = 5 := hzCdegree
  have hAupper (a : (N : Set V)) (haz : a ≠ z) : #(A a) ≤ 1 := by
    calc
      #(A a) ≤ C.degree (a : V) := by
        simpa [A, C] using
          card_residualCrossNeighborFinset_le_between_degree
            G N U Q hNUdis a
      _ = 1 := hLeafCdegree a haz
  have hKcover (a : (N : Set V)) (haz : a ≠ z) :
      L.IsVertexCover (K a : Set (Q : Set (U : Set V))) := by
    simpa [K, Z, A, M] using hEdgeCover (hzAdj a haz)
  have hKcard (a : (N : Set V)) (haz : a ≠ z) : #(K a) = 6 := by
    have hlower := hcoverLower (K a) (hKcover a haz)
    have hu := Finset.card_union_le Z (A a)
    have ha := hAupper a haz
    change 6 ≤ #(Z ∪ A a) at hlower
    change #(Z ∪ A a) ≤ #Z + #(A a) at hu
    change #(Z ∪ A a) = 6
    omega
  have hZcard : #Z = 5 := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega :
      0 < #((Finset.univ : Finset (N : Set V)).erase z))
    have haz : a ≠ z := by simpa using ha
    have hk := hKcard a haz
    have hu := Finset.card_union_le Z (A a)
    have haUpper := hAupper a haz
    change #(Z ∪ A a) = 6 at hk
    omega
  have hAcard (a : (N : Set V)) (haz : a ≠ z) : #(A a) = 1 := by
    have hk := hKcard a haz
    have hu := Finset.card_union_le Z (A a)
    have haUpper := hAupper a haz
    change #(Z ∪ A a) = 6 at hk
    omega
  have hZAdis (a : (N : Set V)) (haz : a ≠ z) : Disjoint Z (A a) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    apply Finset.card_eq_zero.mp
    have hidentity := Finset.card_union_add_card_inter Z (A a)
    have hk := hKcard a haz
    have ha := hAcard a haz
    change #(Z ∪ A a) = 6 at hk
    change #(Z ∪ A a) + #(Z ∩ A a) = #Z + #(A a) at hidentity
    omega
  have hKeq (a b : (N : Set V)) (haz : a ≠ z) (hbz : b ≠ z) :
      K a = K b := by
    rcases six_vertexCovers_eq_or_inter_card_le_four_of_iso_balancedC5Blowup
      L iso (K a) (K b) (hKcard a haz) (hKcover a haz)
        (hKcard b hbz) (hKcover b hbz) with heq | hinter
    · exact heq
    · exfalso
      have hZsub : Z ⊆ K a ∩ K b := by
        intro x hx
        simp [K, hx]
      have hcardLower := Finset.card_le_card hZsub
      omega
  have hAeq (a b : (N : Set V)) (haz : a ≠ z) (hbz : b ≠ z) :
      A a = A b := by
    have hk := hKeq a b haz hbz
    ext x
    constructor
    · intro hxa
      have hxNotZ : x ∉ Z := fun hxZ =>
        (Finset.disjoint_left.mp (hZAdis a haz)) hxZ hxa
      have hxK : x ∈ K a := by simp [K, hxa]
      rw [hk] at hxK
      have hxParts : x ∈ Z ∨ x ∈ A b := by simpa [K] using hxK
      exact hxParts.resolve_left hxNotZ
    · intro hxb
      have hxNotZ : x ∉ Z := fun hxZ =>
        (Finset.disjoint_left.mp (hZAdis b hbz)) hxZ hxb
      have hxK : x ∈ K b := by simp [K, hxb]
      rw [← hk] at hxK
      have hxParts : x ∈ Z ∨ x ∈ A a := by simpa [K] using hxK
      exact hxParts.resolve_left hxNotZ
  let Leaves : Finset (N : Set V) := Finset.univ.erase z
  have hLeavesCard : #Leaves = 4 := by simpa [Leaves] using hEraseCard
  obtain ⟨a0, ha0⟩ := Finset.card_pos.mp (by omega : 0 < #Leaves)
  have ha0z : a0 ≠ z := by simpa [Leaves] using ha0
  obtain ⟨u, hAu⟩ := Finset.card_eq_one.mp (hAcard a0 ha0z)
  have hAleaves (a : (N : Set V)) (haz : a ≠ z) : A a = {u} :=
    (hAeq a a0 haz ha0z).trans hAu
  have hLeafAdjU (a : (N : Set V)) (haz : a ≠ z) :
      G.Adj (a : V) (u : V) := by
    have hu : u ∈ A a := by simp [hAleaves a haz]
    exact (mem_residualCrossNeighborFinset_iff G N U Q a u).mp
      (by simpa [A] using hu)
  let fN : (N : Set V) ↪ V := Function.Embedding.subtype _
  let A0 : Finset V := Leaves.map fN
  let B0 : Finset V := {v, (u : V)}
  let S : Finset V := insert v (insert (u : V) A0)
  have hA0card : #A0 = 4 := by
    calc
      #A0 = #Leaves := by simp [A0]
      _ = 4 := by simpa [Leaves] using hEraseCard
  have hvNotN : v ∉ N := by
    rw [hN]
    exact G.notMem_neighborFinset_self v
  have hvNotA0 : v ∉ A0 := by
    intro hv
    obtain ⟨a, ha, hav⟩ := Finset.mem_map.mp hv
    exact hvNotN (hav ▸ a.property)
  have huNotN : (u : V) ∉ N := fun huN =>
    (Finset.disjoint_left.mp hNUdis) huN u.val.property
  have huNotA0 : (u : V) ∉ A0 := by
    intro hu
    obtain ⟨a, ha, hau⟩ := Finset.mem_map.mp hu
    exact huNotN (hau ▸ a.property)
  have huExterior : (u : V) ∈ exteriorFinset G v := by
    rw [← hU]
    exact u.val.property
  have huFacts : ¬G.Adj v (u : V) ∧ (u : V) ≠ v := by
    have hraw : (u : V) ≠ v ∧ ¬G.Adj v (u : V) := by
      simpa [exteriorFinset] using huExterior
    exact ⟨hraw.2, hraw.1⟩
  have hvu : v ≠ (u : V) := huFacts.2.symm
  have hScard : #S = 6 := by
    simp [S, hvNotA0, huNotA0, hvu, hA0card]
  have hA0ind : Gᶜ.IsIndepSet (A0 : Set V) := by
    intro x hx y hy hxy hxyComp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    have haz : a ≠ z := by simpa [Leaves] using ha
    have hbz : b ≠ z := by simpa [Leaves] using hb
    have habM : M.Adj a b := by
      have habSub : a ≠ b := fun h => hxy (congrArg Subtype.val h)
      have hnG : ¬G.Adj (a : V) (b : V) := hxyComp.2
      simpa [M] using (show a ≠ b ∧ ¬G.Adj (a : V) (b : V) from
        ⟨habSub, hnG⟩)
    rcases hEdgeMeet habM with h | h
    · exact haz h
    · exact hbz h
  have hA0B0dis : Disjoint A0 B0 := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hxA
    have haN := a.property
    have hparts : (a : V) = v ∨ (a : V) = (u : V) := by
      simpa [B0, fN] using hxB
    rcases hparts with hav | hau
    · exact hvNotN (hav ▸ haN)
    · exact huNotN (hau ▸ haN)
  have hLeafAdjB {x y : V} (hx : x ∈ A0) (hy : y ∈ B0) : G.Adj x y := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    have haz : a ≠ z := by simpa [Leaves] using ha
    have hparts : y = v ∨ y = (u : V) := by
      simpa [B0] using hy
    rcases hparts with hyv | hyu
    · subst y
      have hva : G.Adj v (a : V) := by simpa [hN] using a.property
      exact hva.symm
    · subst y
      exact hLeafAdjU a haz
  let D := Gᶜ.between (A0 : Set V) (B0 : Set V)
  have hDbot : D = (⊥ : SimpleGraph V) := by
    ext x y
    constructor
    · intro hxy
      have hraw := SimpleGraph.between_adj.mp hxy
      rcases hraw.2 with hparts | hparts
      · exact (hraw.1.2 (hLeafAdjB hparts.1 hparts.2)).elim
      · exact (hraw.1.2 (hLeafAdjB hparts.2 hparts.1).symm).elim
    · intro hxy
      exact hxy.elim
  have hvB0 : v ∈ B0 := by simp [B0]
  have huB0 : (u : V) ∈ B0 := by simp [B0]
  have hvuExterior : v ≠ (u : V) ∧ ¬G.Adj v (u : V) :=
    ⟨huFacts.2.symm, huFacts.1⟩
  have hvuComp : Gᶜ.Adj v (u : V) := hvuExterior
  have hexact := card_induce_pair_add_between_degrees_of_independent
    Gᶜ A0 B0 v (u : V) hvB0 huB0 hvuExterior.1 hA0B0dis hA0ind
  have hcompOne :
      #(Gᶜ.induce
        ((insert v (insert (u : V) A0) : Finset V) : Set V)).edgeFinset = 1 := by
    have hDdegV : D.degree v = 0 := by simp [hDbot]
    have hDdegU : D.degree (u : V) = 0 := by simp [hDbot]
    simpa [D, hDdegV, hDdegU, hvuComp] using hexact
  have hfour := four_le_card_induced_compl_of_admissible_six G hG S hScard
  have hcompOneS : #(Gᶜ.induce (S : Set V)).edgeFinset = 1 := by
    simpa [S] using hcompOne
  omega

/-- A degree-five minimum vertex cannot occur in the exact order-21,
55-edge residual. -/
theorem false_of_admissible_indepSetFree_five_card_twentyOne_edges_fiftyFive_minDegree_five_at
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 5)
    (hcard : Fintype.card V = 21) (hedges : #G.edgeFinset = 55)
    (v : V) (hdegree : G.degree v = 5)
    (hmin : ∀ w, G.degree v ≤ G.degree w) :
    False := by
  classical
  let N := G.neighborFinset v
  let U := exteriorFinset G v
  let R := G.induce (U : Set V)
  let C := G.between (N : Set V) (U : Set V)
  let H := G.induce (N : Set V)
  let M := Hᶜ
  have hNcard : #N = 5 := by simp [N, hdegree]
  have hNtype : Fintype.card (N : Set V) = 5 := by simpa using hNcard
  have hUcardRaw := card_exterior_type_add_degree_add_one G v
  have hUcard : Fintype.card (U : Set V) = 15 := by
    rw [hcard, hdegree] at hUcardRaw
    simpa [U] using (show Fintype.card (exteriorFinset G v : Set V) = 15 by
      omega)
  have hRadmissible : Admissible R := by
    simpa [R, U] using admissible_induce G hG U
  have hRfree : R.IndepSetFree 4 := by
    simpa [R, U] using
      (indepSetFree_exterior_induce G (k := 4) (by simpa using hfree) v)
  by_cases hcolor : Rᶜ.Colorable 3
  · exact false_of_colorable_compl_exterior_degree_five_card_twentyOne
      G hG hfree hcard v hdegree (by simpa [R, U] using hcolor)
  have hRlower :=
    card_edges_ge_thirtyFive_of_admissible_indepSetFree_four_card_fifteen_not_colorable
      R hRadmissible hRfree hUcard hcolor
  have hstrong :=
    exterior_edges_add_nineteen_le_edges_of_admissible_degree_five
      G hG v hdegree hmin
  have hRupper : #R.edgeFinset ≤ 36 := by
    have hstrong' : #R.edgeFinset + 19 ≤ 55 := by
      simpa [R, U, hedges] using hstrong
    omega
  have hRrange : #R.edgeFinset = 35 ∨ #R.edgeFinset = 36 := by omega
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
    simpa [C] using
      SimpleGraph.between_isBipartiteWith (G := G) hNUdisSet
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
  have hexact := card_edges_eq_exterior_add_degree_add_accounting G v
  have hexact' : #R.edgeFinset + 5 +
      (neighborhoodCrossEdgeCount G v +
        neighborhoodInternalEdgeCount G v) = 55 := by
    simpa [R, U, hdegree, hedges] using hexact
  have hYupper := neighborhoodInternalEdgeCount_le_six_of_admissible_degree_five
    G hG v hdegree
  have htwice := neighborhood_cross_add_twice_internal_ge G v hmin
  rw [hdegree] at htwice
  norm_num at htwice
  rcases hRrange with hR35 | hR36
  · have haccount : neighborhoodCrossEdgeCount G v +
        neighborhoodInternalEdgeCount G v = 15 := by omega
    have hYlower : 5 ≤ neighborhoodInternalEdgeCount G v := by omega
    have hYrange : neighborhoodInternalEdgeCount G v = 5 ∨
        neighborhoodInternalEdgeCount G v = 6 := by omega
    have hstructure := orderFifteenThirtyFiveStructure_of_admissible
      R hRadmissible hRfree hUcard hR35 hcolor
    rcases hstructure with ⟨P, hPcard, hPisolated, hiso⟩
    let Q : Finset (U : Set V) := Pᶜ
    let T := (R.induce (Q : Set (U : Set V)))ᶜ
    obtain ⟨isoT⟩ : Nonempty (T ≃g balancedC5Blowup) := by
      simpa [T, Q] using hiso
    let fU : (U : Set V) ↪ V := Function.Embedding.subtype _
    let P0 : Finset V := P.map fU
    have hP0card : #P0 = 5 := by simp [P0, hPcard]
    have hP0clique : G.IsClique (P0 : Set V) := by
      intro x hx y hy hxy
      obtain ⟨x', hx'P, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨y', hy'P, rfl⟩ := Finset.mem_map.mp hy
      have hxy' : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
      change G.Adj (x' : V) (y' : V)
      simpa [R] using hPisolated.1 hx'P hy'P hxy'
    have hNP0dis : Disjoint N P0 := by
      rw [Finset.disjoint_left]
      intro x hxN hxP0
      obtain ⟨x', hx'P, rfl⟩ := Finset.mem_map.mp hxP0
      exact (Finset.disjoint_left.mp hNUdis) hxN x'.property
    have hTnonadj : ∀ ⦃x y : (Q : Set (U : Set V))⦄, T.Adj x y →
        ¬G.Adj (x : V) (y : V) := by
      intro x y hxy
      have hnotInduce : ¬(R.induce (Q : Set (U : Set V))).Adj x y := hxy.2
      simpa [R] using hnotInduce
    have hCoverOfMEdge : ∀ ⦃a b : (N : Set V)⦄, M.Adj a b →
        T.IsVertexCover
          ((residualCrossNeighborFinset G N U Q a ∪
            residualCrossNeighborFinset G N U Q b : Finset _) : Set _) := by
      intro a b habM
      have haNotP0 : (a : V) ∉ P0 := fun ha =>
        (Finset.disjoint_left.mp hNP0dis) a.property ha
      have hbNotP0 : (b : V) ∉ P0 := fun hb =>
        (Finset.disjoint_left.mp hNP0dis) b.property hb
      obtain ⟨c0, hc0P0, hac, hbc⟩ :=
        exists_mem_clique_five_avoiding_pair
          G hG P0 hP0card hP0clique (a : V) (b : V) haNotP0 hbNotP0
      obtain ⟨c, hcP, hcval⟩ := Finset.mem_map.mp hc0P0
      subst c0
      have habG : ¬G.Adj (a : V) (b : V) := by
        have hcomp : Hᶜ.Adj a b := by simpa [M] using habM
        simpa [H] using hcomp.2
      have hab : (a : V) ≠ (b : V) := fun h => habM.ne (Subtype.ext h)
      have hcNotQ : c ∉ Q := by simpa [Q] using hcP
      have hcNonadj : ∀ x : (Q : Set (U : Set V)),
          ¬G.Adj (c : V) (x : V) := by
        intro x
        have hxNotP : (x : (U : Set V)) ∉ P := by
          simpa [Q] using x.property
        have hnotR := hPisolated.2 hcP hxNotP
        simpa [R] using hnotR
      exact residualCrossNeighbor_union_isVertexCover_with_avoider
        G hfree N U Q hNUdis a b hab habG c hcNotQ
          (by simpa [fU] using hac) (by simpa [fU] using hbc)
          T hTnonadj hcNonadj
    rcases hYrange with hY5 | hY6
    · have hX : neighborhoodCrossEdgeCount G v = 10 := by omega
      have hHedges : #H.edgeFinset = 5 := by
        have hi := neighborhoodInternalEdgeCount_eq_induce G v
        rw [hY5] at hi
        simpa [H, N] using hi.symm
      have hMpartition := card_edgeFinset_add_card_compl H
      rw [hNtype, hHedges] at hMpartition
      norm_num [Nat.choose] at hMpartition
      have hMedges : #M.edgeFinset = 5 := by
        simpa [M] using (show #Hᶜ.edgeFinset = 5 by omega)
      have hCedges : #C.edgeFinset = 10 := by
        simpa [C, N, U, neighborhoodCrossEdgeCount] using hX
      have hSumM : (∑ a : (N : Set V), M.degree a) = 10 := by
        have hs := M.sum_degrees_eq_twice_card_edges
        rw [hMedges] at hs
        norm_num at hs ⊢
        exact hs
      have hSumCbase : (∑ a ∈ N, C.degree a) = 10 := by
        have hs := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hCbip
        rw [hCedges] at hs
        exact hs
      have hSumC : (∑ a : (N : Set V), C.degree (a : V)) = 10 := by
        have hs := Finset.sum_attach N (fun a => C.degree a)
        rw [Finset.attach_eq_univ] at hs
        calc
          (∑ a : (N : Set V), C.degree (a : V)) =
              ∑ a ∈ N, C.degree a := hs
          _ = 10 := hSumCbase
      have hPointEq (a : (N : Set V)) : M.degree a = C.degree (a : V) := by
        have hsumEq : (∑ x : (N : Set V), M.degree x) =
            ∑ x : (N : Set V), C.degree (x : V) := by omega
        have hp := (Finset.sum_eq_sum_iff_of_le
          (s := (Finset.univ : Finset (N : Set V)))
          (fun x _ => hPointLe x)).mp hsumEq
        exact hp a (Finset.mem_univ a)
      obtain ⟨a, b, habM, hpair⟩ :=
        exists_adj_degree_add_le_five_of_card_five_edges_five
          M hNtype hMedges
      have hcover := hCoverOfMEdge habM
      let A := residualCrossNeighborFinset G N U Q a
      let B := residualCrossNeighborFinset G N U Q b
      have hcoverAB : T.IsVertexCover ((A ∪ B : Finset _) : Set _) := by
        simpa [A, B] using hcover
      have hu := Finset.card_union_le A B
      have haLe : #A ≤ C.degree (a : V) := by
        simpa [A, C] using
          card_residualCrossNeighborFinset_le_between_degree
            G N U Q hNUdis a
      have hbLe : #B ≤ C.degree (b : V) := by
        simpa [B, C] using
          card_residualCrossNeighborFinset_le_between_degree
            G N U Q hNUdis b
      have hlowerCard : 6 ≤ #(A ∪ B) := by
        exact six_le_card_of_vertexCover_of_iso_balancedC5Blowup
          T isoT (A ∪ B) hcoverAB
      rw [← hPointEq a] at haLe
      rw [← hPointEq b] at hbLe
      omega
    · have hX : neighborhoodCrossEdgeCount G v = 9 := by omega
      have hHedges : #H.edgeFinset = 6 := by
        have hi := neighborhoodInternalEdgeCount_eq_induce G v
        rw [hY6] at hi
        simpa [H, N] using hi.symm
      have hMpartition := card_edgeFinset_add_card_compl H
      rw [hNtype, hHedges] at hMpartition
      norm_num [Nat.choose] at hMpartition
      have hMedges : #M.edgeFinset = 4 := by
        simpa [M] using (show #Hᶜ.edgeFinset = 4 by omega)
      have hCedges : #C.edgeFinset = 9 := by
        simpa [C, N, U, neighborhoodCrossEdgeCount] using hX
      exact false_of_canonical_residual_excess_one_of_edge_covers
        G hG v N U Q rfl rfl hNcard hNUdis T isoT
          (by simpa [M, H] using hMedges)
          (by simpa [C] using hCedges)
          (fun a => by simpa [M, H, C] using hPointLe a)
          (by
            intro a b hab
            apply hCoverOfMEdge
            simpa [M, H] using hab)
  · have haccount : neighborhoodCrossEdgeCount G v +
        neighborhoodInternalEdgeCount G v = 14 := by omega
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
    have hCedges : #C.edgeFinset = 8 := by
      simpa [C, N, U, neighborhoodCrossEdgeCount] using hX
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
        (∑ a : (N : Set V), C.degree (a : V)) =
            ∑ a ∈ N, C.degree a := hs
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
      have hpair := degree_add_degree_le_card_edges_add_one_of_adj M habM
      rw [hMedges] at hpair
      have habG : ¬G.Adj (a : V) (b : V) := by
        have hcomp : Hᶜ.Adj a b := by simpa [M] using habM
        simpa [H] using hcomp.2
      have hab : (a : V) ≠ (b : V) := fun h => habM.ne (Subtype.ext h)
      have hstructure := orderFifteenThirtySixStructure_or_of_admissible
        R hRadmissible hRfree hUcard hR36 hcolor
      rcases hstructure with hone | hisolated
      · rcases hone with ⟨P, hPcard, hPclique, hcross, hiso⟩
        let Q : Finset (U : Set V) := Pᶜ
        let T := (R.induce (Q : Set (U : Set V)))ᶜ
        obtain ⟨isoT⟩ : Nonempty (T ≃g balancedC5Blowup) := by
          simpa [T, Q] using hiso
        have hPQdis : Disjoint P Q := by
          rw [Finset.disjoint_left]
          intro x hxP hxQ
          have hxNotP : x ∉ P := by simpa [Q] using hxQ
          exact hxNotP hxP
        obtain ⟨c0, hc0P, hc0NoCross⟩ :=
          exists_left_endpoint_of_card_between_eq_one
            R P Q hPQdis (by simpa [Q] using hcross)
        let fU : (U : Set V) ↪ V := Function.Embedding.subtype _
        let P0 : Finset V := P.map fU
        have hP0card : #P0 = 5 := by simp [P0, hPcard]
        have hP0clique : G.IsClique (P0 : Set V) := by
          intro x hx y hy hxy
          obtain ⟨x', hx'P, rfl⟩ := Finset.mem_map.mp hx
          obtain ⟨y', hy'P, rfl⟩ := Finset.mem_map.mp hy
          have hxy' : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
          change G.Adj (x' : V) (y' : V)
          simpa [R] using hPclique hx'P hy'P hxy'
        have hNP0dis : Disjoint N P0 := by
          rw [Finset.disjoint_left]
          intro x hxN hxP0
          obtain ⟨x', hx'P, rfl⟩ := Finset.mem_map.mp hxP0
          exact (Finset.disjoint_left.mp hNUdis) hxN x'.property
        have haNotP0 : (a : V) ∉ P0 := fun ha =>
          (Finset.disjoint_left.mp hNP0dis) a.property ha
        have hbNotP0 : (b : V) ∉ P0 := fun hb =>
          (Finset.disjoint_left.mp hNP0dis) b.property hb
        have hc0P0 : (c0 : V) ∈ P0 := by
          exact Finset.mem_map.mpr ⟨c0, hc0P, rfl⟩
        obtain ⟨d0, hd0P0, hd0c0, had, hbd⟩ :=
          exists_mem_clique_five_avoiding_pair_and_ne
            G hG P0 hP0card hP0clique (a : V) (b : V) (c0 : V)
              haNotP0 hbNotP0 hc0P0
        obtain ⟨d, hdP, hdval⟩ := Finset.mem_map.mp hd0P0
        subst d0
        have hdc0 : d ≠ c0 := by
          intro h
          exact hd0c0 (congrArg Subtype.val h)
        have hdNotQ : d ∉ Q := by simpa [Q] using hdP
        have hTnonadj : ∀ ⦃x y : (Q : Set (U : Set V))⦄,
            T.Adj x y → ¬G.Adj (x : V) (y : V) := by
          intro x y hxy
          have hnotInduce : ¬(R.induce (Q : Set (U : Set V))).Adj x y :=
            hxy.2
          simpa [R] using hnotInduce
        have hdNonadj : ∀ x : (Q : Set (U : Set V)),
            ¬G.Adj (d : V) (x : V) := by
          intro x
          have hnotR := hc0NoCross d hdP hdc0 (x : (U : Set V)) x.property
          simpa [R] using hnotR
        have hcover :=
          residualCrossNeighbor_union_isVertexCover_with_avoider
            G hfree N U Q hNUdis a b hab habG d hdNotQ
              (by simpa [fU] using had) (by simpa [fU] using hbd)
              T hTnonadj hdNonadj
        let A := residualCrossNeighborFinset G N U Q a
        let B := residualCrossNeighborFinset G N U Q b
        have hcoverAB : T.IsVertexCover ((A ∪ B : Finset _) : Set _) := by
          simpa [A, B] using hcover
        have hlower : 6 ≤ #(A ∪ B) :=
          six_le_card_of_vertexCover_of_iso_balancedC5Blowup
            T isoT (A ∪ B) hcoverAB
        have hu := Finset.card_union_le A B
        have haLe : #A ≤ C.degree (a : V) := by
          simpa [A, C] using
            card_residualCrossNeighborFinset_le_between_degree
              G N U Q hNUdis a
        have hbLe : #B ≤ C.degree (b : V) := by
          simpa [B, C] using
            card_residualCrossNeighborFinset_le_between_degree
              G N U Q hNUdis b
        rw [← hPointEq a] at haLe
        rw [← hPointEq b] at hbLe
        omega
      · rcases hisolated with ⟨P, hPcard, hPisolated, hprops⟩
        let Q : Finset (U : Set V) := Pᶜ
        let T := (R.induce (Q : Set (U : Set V)))ᶜ
        have hQcardFin : #Q = 10 := by
          rw [Finset.card_compl, hPcard, hUcard]
        have hQcard : Fintype.card (Q : Set (U : Set V)) = 10 := by
          simpa using hQcardFin
        have hTfree : T.IndepSetFree 5 := by
          simpa [T, Q] using hprops.2.2
        let fU : (U : Set V) ↪ V := Function.Embedding.subtype _
        let P0 : Finset V := P.map fU
        have hP0card : #P0 = 5 := by simp [P0, hPcard]
        have hP0clique : G.IsClique (P0 : Set V) := by
          intro x hx y hy hxy
          obtain ⟨x', hx'P, rfl⟩ := Finset.mem_map.mp hx
          obtain ⟨y', hy'P, rfl⟩ := Finset.mem_map.mp hy
          have hxy' : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
          change G.Adj (x' : V) (y' : V)
          simpa [R] using hPisolated.1 hx'P hy'P hxy'
        have hNP0dis : Disjoint N P0 := by
          rw [Finset.disjoint_left]
          intro x hxN hxP0
          obtain ⟨x', hx'P, rfl⟩ := Finset.mem_map.mp hxP0
          exact (Finset.disjoint_left.mp hNUdis) hxN x'.property
        have haNotP0 : (a : V) ∉ P0 := fun ha =>
          (Finset.disjoint_left.mp hNP0dis) a.property ha
        have hbNotP0 : (b : V) ∉ P0 := fun hb =>
          (Finset.disjoint_left.mp hNP0dis) b.property hb
        obtain ⟨d0, hd0P0, had, hbd⟩ :=
          exists_mem_clique_five_avoiding_pair
            G hG P0 hP0card hP0clique (a : V) (b : V) haNotP0 hbNotP0
        obtain ⟨d, hdP, hdval⟩ := Finset.mem_map.mp hd0P0
        subst d0
        have hdNotQ : d ∉ Q := by simpa [Q] using hdP
        have hTnonadj : ∀ ⦃x y : (Q : Set (U : Set V))⦄,
            T.Adj x y → ¬G.Adj (x : V) (y : V) := by
          intro x y hxy
          have hnotInduce : ¬(R.induce (Q : Set (U : Set V))).Adj x y :=
            hxy.2
          simpa [R] using hnotInduce
        have hdNonadj : ∀ x : (Q : Set (U : Set V)),
            ¬G.Adj (d : V) (x : V) := by
          intro x
          have hxNotP : (x : (U : Set V)) ∉ P := by
            simpa [Q] using x.property
          have hnotR := hPisolated.2 hdP hxNotP
          simpa [R] using hnotR
        have hcover :=
          residualCrossNeighbor_union_isVertexCover_with_avoider
            G hfree N U Q hNUdis a b hab habG d hdNotQ
              (by simpa [fU] using had) (by simpa [fU] using hbd)
              T hTnonadj hdNonadj
        let A := residualCrossNeighborFinset G N U Q a
        let B := residualCrossNeighborFinset G N U Q b
        have hcoverAB : T.IsVertexCover ((A ∪ B : Finset _) : Set _) := by
          simpa [A, B] using hcover
        have hlower : 6 ≤ #(A ∪ B) :=
          six_le_card_of_vertexCover_of_indepSetFree_five_card_ten
            T hTfree hQcard (A ∪ B) hcoverAB
        have hu := Finset.card_union_le A B
        have haLe : #A ≤ C.degree (a : V) := by
          simpa [A, C] using
            card_residualCrossNeighborFinset_le_between_degree
              G N U Q hNUdis a
        have hbLe : #B ≤ C.degree (b : V) := by
          simpa [B, C] using
            card_residualCrossNeighborFinset_le_between_degree
              G N U Q hNUdis b
        rw [← hPointEq a] at haLe
        rw [← hPointEq b] at hbLe
        omega

/-- No exact order-21, 55-edge admissible graph with no independent five-set
can have minimum degree at least five. -/
theorem false_of_admissible_indepSetFree_five_card_twentyOne_edges_fiftyFive_minDegree_five
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 5)
    (hcard : Fintype.card V = 21) (hedges : #G.edgeFinset = 55)
    (hdegreeLower : ∀ w, 5 ≤ G.degree w) :
    False := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by
    rw [hcard]
    norm_num)
  obtain ⟨v, hmin, havg⟩ :=
    exists_minimal_vertex_card_mul_degree_le_twice_edges G
  have hdegreeUpper : G.degree v ≤ 5 := by
    rw [hcard, hedges] at havg
    omega
  have hdegree : G.degree v = 5 := by
    have := hdegreeLower v
    omega
  exact
    false_of_admissible_indepSetFree_five_card_twentyOne_edges_fiftyFive_minDegree_five_at
      G hG hfree hcard hedges v hdegree hmin

/-- The exact order-21 residual with inherited minimum degree four is
impossible: E056 advances it to minimum degree five, and the preceding
theorem closes that final branch. -/
theorem false_of_admissible_indepSetFree_five_card_twentyOne_edges_fiftyFive_minDegree_four
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 5)
    (hcard : Fintype.card V = 21) (hedges : #G.edgeFinset = 55)
    (hdegreeLower : ∀ w, 4 ≤ G.degree w) :
    False := by
  have hfive :=
    five_le_degree_of_admissible_indepSetFree_five_card_twentyOne_edges_fiftyFive
      G hG hfree hcard hedges hdegreeLower
  exact
    false_of_admissible_indepSetFree_five_card_twentyOne_edges_fiftyFive_minDegree_five
      G hG hfree hcard hedges hfive

/-- The residual structure exported by E055 cannot occur.  This theorem is
purely graph-theoretic and has no special-Brooks premise. -/
theorem false_of_r5ColorGraphResidualStructure
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hstructure : R5ColorGraphResidualStructure G) :
    False := by
  classical
  rcases hstructure with
    ⟨v, hmin, hdegree, hisolated, hcard, hedges, hG, hfree, hdegreeLower⟩
  let U := exteriorFinset G v
  let H := G.induce (U : Set (Fin 26))
  exact
    false_of_admissible_indepSetFree_five_card_twentyOne_edges_fiftyFive_minDegree_four
      H (by simpa [H, U] using hG) (by simpa [H, U] using hfree)
        (by simpa [H, U] using hcard) (by simpa [H, U] using hedges)
        (by simpa [H, U] using hdegreeLower)

/-- Conditional on the exact finite special-Brooks proposition isolated in
E055, no 26-vertex five-color counterexample exists. -/
theorem no_r5_counterexample_of_special_brooks
    (hbrooks : R5SpecialBrooksObstruction) :
    ¬∃ χ : EdgeColoring (Fin 26) (Fin 5), IsCounterexample 6 χ := by
  rintro ⟨χ, hχ⟩
  have hstructure := colorGraph_residualStructure_of_special_brooks
    hbrooks χ hχ (0 : Fin 5)
  exact false_of_r5ColorGraphResidualStructure (colorGraph χ 0) hstructure

/-- The complete fixed-`r=5` upper statement, conditional only on the
explicit finite special-Brooks obstruction. -/
theorem r5Upper_of_special_brooks
    (hbrooks : R5SpecialBrooksObstruction) :
    R5Upper := by
  exact r5Upper_iff_no_counterexample.mpr
    (no_r5_counterexample_of_special_brooks hbrooks)

/-- The original fixed-case formulation at `r=5`, with the same sole
conditional premise. -/
theorem problem617At_five_of_special_brooks
    (hbrooks : R5SpecialBrooksObstruction) :
    Problem617At 5 := by
  exact problem617At_five_iff_r5Upper.mpr
    (r5Upper_of_special_brooks hbrooks)

end Erdos617
