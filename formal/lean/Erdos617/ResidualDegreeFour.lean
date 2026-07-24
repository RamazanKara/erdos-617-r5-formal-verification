/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.EdgeEqualization
public import Mathlib.Tactic.IntervalCases

/-!
# The minimum-degree-four branch of the final order-21 residual

This module eliminates the degree-four branch of the exact residual produced
by `colorGraph_residualStructure_of_special_brooks`.  The terminal cases use
the complete order-ten structure theorem and its minimum-cover intersection
certificate.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

universe u

/-- In a ten-vertex graph with no independent five-set, every finite vertex
cover has at least six vertices. -/
theorem six_le_card_of_vertexCover_of_indepSetFree_five_card_ten
    {V : Type u} [Fintype V]
    (L : SimpleGraph V)
    (hfree : L.IndepSetFree 5) (hcard : Fintype.card V = 10)
    (K : Finset V) (hcover : L.IsVertexCover (K : Set V)) :
    6 ≤ #K := by
  classical
  by_contra hnot
  have hKupper : #K ≤ 5 := by omega
  have hcompIndSet : L.IsIndepSet ((Kᶜ : Finset V) : Set V) := by
    have hraw :=
      (SimpleGraph.isIndepSet_compl_iff_isVertexCover (G := L)).2 hcover
    simpa using hraw
  have hcompCard : 5 ≤ #(Kᶜ : Finset V) := by
    rw [Finset.card_compl, hcard]
    omega
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hcompCard
  have hSind : L.IsIndepSet (S : Set V) := by
    intro x hx y hy hxy
    exact hcompIndSet (hSsub hx) (hSsub hy) hxy
  exact hfree S ⟨hSind, hScard⟩

/-- If two nonadjacent vertices on one side of a cut must cover an exterior
graph with their cross-neighborhoods, and every such cover has size at least
six, then their two cross-degrees sum to at least six. -/
theorem six_le_cross_degree_add_of_nonadjacent_pair
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : G.IndepSetFree 4)
    (N U : Finset V) (hNUdis : Disjoint N U)
    (a b : (N : Set V)) (hab : (a : V) ≠ (b : V))
    (habG : ¬G.Adj (a : V) (b : V))
    (L : SimpleGraph (U : Set V))
    (hLnonadj : ∀ ⦃x y : (U : Set V)⦄, L.Adj x y →
      ¬G.Adj (x : V) (y : V))
    (hcoverLower : ∀ K : Finset (U : Set V),
      L.IsVertexCover (K : Set (U : Set V)) → 6 ≤ #K) :
    6 ≤ (G.between (N : Set V) (U : Set V)).degree (a : V) +
      (G.between (N : Set V) (U : Set V)).degree (b : V) := by
  classical
  let C := G.between (N : Set V) (U : Set V)
  let K0 : Finset V := C.neighborFinset (a : V) ∪
    C.neighborFinset (b : V)
  have hNUdisSet : Disjoint (N : Set V) (U : Set V) :=
    Finset.disjoint_coe.mpr hNUdis
  have hCbip : C.IsBipartiteWith (N : Set V) (U : Set V) := by
    simpa [C] using
      SimpleGraph.between_isBipartiteWith (G := G) hNUdisSet
  have hCaSub : C.neighborFinset (a : V) ⊆ U :=
    SimpleGraph.isBipartiteWith_neighborFinset_subset hCbip a.property
  have hCbSub : C.neighborFinset (b : V) ⊆ U :=
    SimpleGraph.isBipartiteWith_neighborFinset_subset hCbip b.property
  have hK0sub : K0 ⊆ U := Finset.union_subset hCaSub hCbSub
  let fU : (U : Set V) ↪ V := Function.Embedding.subtype _
  let K : Finset (U : Set V) :=
    Finset.univ.filter fun x => (x : V) ∈ K0
  have hKmap : K.map fU = K0 := by
    ext x
    constructor
    · intro hx
      obtain ⟨x', hx'K, rfl⟩ := Finset.mem_map.mp hx
      change (x' : V) ∈ K0
      simpa [K] using hx'K
    · intro hx
      have hxU := hK0sub hx
      refine Finset.mem_map.mpr ⟨⟨x, hxU⟩, ?_, rfl⟩
      simp [K, hx]
  have hKcardBase : #K = #K0 := by
    calc
      #K = #(K.map fU) := by simp
      _ = #K0 := congrArg Finset.card hKmap
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
    have hyAvoid : ¬G.Adj (a : V) (y : V) ∧
        ¬G.Adj (b : V) (y : V) := by
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
    have hxyG : ¬G.Adj (x : V) (y : V) := hLnonadj hxyL
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
  have hKlower : 6 ≤ #K := hcoverLower K hKcover
  have hKupper : #K ≤ C.degree (a : V) + C.degree (b : V) := by
    have hu := Finset.card_union_le
      (C.neighborFinset (a : V)) (C.neighborFinset (b : V))
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at hu
    calc
      #K = #K0 := hKcardBase
      _ = #(C.neighborFinset (a : V) ∪
          C.neighborFinset (b : V)) := by rfl
      _ ≤ C.degree (a : V) + C.degree (b : V) := hu
  simpa [C] using (show 6 ≤ C.degree (a : V) + C.degree (b : V) by
    omega)

/-- The cross-neighborhood of a vertex of `N`, represented directly on the
subtype carried by `U`. -/
def crossNeighborFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (N U : Finset V) (a : (N : Set V)) : Finset (U : Set V) :=
  Finset.univ.filter fun x => G.Adj (a : V) (x : V)

@[simp]
theorem mem_crossNeighborFinset_iff
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (N U : Finset V) (a : (N : Set V)) (x : (U : Set V)) :
    x ∈ crossNeighborFinset G N U a ↔ G.Adj (a : V) (x : V) := by
  simp [crossNeighborFinset]

/-- The subtype cross-neighborhood has the expected between-graph degree. -/
theorem card_crossNeighborFinset_eq_between_degree
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (N U : Finset V) (hNUdis : Disjoint N U)
    (a : (N : Set V)) :
    #(crossNeighborFinset G N U a) =
      (G.between (N : Set V) (U : Set V)).degree (a : V) := by
  classical
  let C := G.between (N : Set V) (U : Set V)
  let fU : (U : Set V) ↪ V := Function.Embedding.subtype _
  have hNUdisSet : Disjoint (N : Set V) (U : Set V) :=
    Finset.disjoint_coe.mpr hNUdis
  have hCbip : C.IsBipartiteWith (N : Set V) (U : Set V) := by
    simpa [C] using
      SimpleGraph.between_isBipartiteWith (G := G) hNUdisSet
  have hsub : C.neighborFinset (a : V) ⊆ U :=
    SimpleGraph.isBipartiteWith_neighborFinset_subset hCbip a.property
  have hmap : (crossNeighborFinset G N U a).map fU =
      C.neighborFinset (a : V) := by
    ext x
    constructor
    · intro hx
      obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
      rw [SimpleGraph.mem_neighborFinset]
      exact ⟨by simpa [fU] using
        (mem_crossNeighborFinset_iff G N U a x').mp hx',
        Or.inl ⟨a.property, x'.property⟩⟩
    · intro hx
      have hxU := hsub hx
      refine Finset.mem_map.mpr ⟨⟨x, hxU⟩, ?_, rfl⟩
      have hxC : C.Adj (a : V) x := by
        rw [← SimpleGraph.mem_neighborFinset]
        exact hx
      exact (by
        rw [mem_crossNeighborFinset_iff]
        exact (SimpleGraph.between_adj.mp hxC).1)
  calc
    #(crossNeighborFinset G N U a) =
        #((crossNeighborFinset G N U a).map fU) := by simp
    _ = #(C.neighborFinset (a : V)) := congrArg Finset.card hmap
    _ = C.degree (a : V) := SimpleGraph.card_neighborFinset_eq_degree _ _

/-- Nonadjacent vertices of `N` have cross-neighborhoods whose union covers
every exterior nonedge, on pain of an independent four-set. -/
theorem crossNeighbor_union_isVertexCover_of_nonadjacent_pair
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : G.IndepSetFree 4)
    (N U : Finset V) (hNUdis : Disjoint N U)
    (a b : (N : Set V)) (hab : (a : V) ≠ (b : V))
    (habG : ¬G.Adj (a : V) (b : V))
    (L : SimpleGraph (U : Set V))
    (hLnonadj : ∀ ⦃x y : (U : Set V)⦄, L.Adj x y →
      ¬G.Adj (x : V) (y : V)) :
    L.IsVertexCover
      ((crossNeighborFinset G N U a ∪
        crossNeighborFinset G N U b : Finset (U : Set V)) :
          Set (U : Set V)) := by
  classical
  intro x y hxyL
  by_contra hnot
  have hxNot : x ∉ crossNeighborFinset G N U a ∧
      x ∉ crossNeighborFinset G N U b := by
    simpa using (show x ∉ crossNeighborFinset G N U a ∪
      crossNeighborFinset G N U b from fun hx => hnot (Or.inl hx))
  have hyNot : y ∉ crossNeighborFinset G N U a ∧
      y ∉ crossNeighborFinset G N U b := by
    simpa using (show y ∉ crossNeighborFinset G N U a ∪
      crossNeighborFinset G N U b from fun hy => hnot (Or.inr hy))
  have hxAvoid : ¬G.Adj (a : V) (x : V) ∧
      ¬G.Adj (b : V) (x : V) := by
    exact ⟨fun h => hxNot.1 ((mem_crossNeighborFinset_iff G N U a x).2 h),
      fun h => hxNot.2 ((mem_crossNeighborFinset_iff G N U b x).2 h)⟩
  have hyAvoid : ¬G.Adj (a : V) (y : V) ∧
      ¬G.Adj (b : V) (y : V) := by
    exact ⟨fun h => hyNot.1 ((mem_crossNeighborFinset_iff G N U a y).2 h),
      fun h => hyNot.2 ((mem_crossNeighborFinset_iff G N U b y).2 h)⟩
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
    hxAvoid.2 hyAvoid.2 (hLnonadj hxyL)

/-- The minimum-cover intersection property of the balanced two-fold `C5`
blow-up, transported through an arbitrary graph isomorphism. -/
theorem six_vertexCovers_eq_or_inter_card_le_four_of_iso_balancedC5Blowup
    {V : Type u} [DecidableEq V]
    (L : SimpleGraph V)
    (iso : L ≃g balancedC5Blowup)
    (S T : Finset V) (hScard : #S = 6)
    (hScover : L.IsVertexCover (S : Set V))
    (hTcard : #T = 6)
    (hTcover : L.IsVertexCover (T : Set V)) :
    S = T ∨ #(S ∩ T) ≤ 4 := by
  classical
  let f : V ↪ Fin 5 × Fin 2 := iso.toEquiv.toEmbedding
  let S' : Finset (Fin 5 × Fin 2) := S.map f
  let T' : Finset (Fin 5 × Fin 2) := T.map f
  have hS'card : #S' = 6 := by simpa [S'] using hScard
  have hT'card : #T' = 6 := by simpa [T'] using hTcard
  have hS'cover : balancedC5Blowup.IsVertexCover (S' : Set _) := by
    have h :=
      (SimpleGraph.isVertexCover_image_iso iso (c := (S : Set V))).2 hScover
    simpa [S', f, Finset.coe_map] using h
  have hT'cover : balancedC5Blowup.IsVertexCover (T' : Set _) := by
    have h :=
      (SimpleGraph.isVertexCover_image_iso iso (c := (T : Set V))).2 hTcover
    simpa [T', f, Finset.coe_map] using h
  by_cases hST : S = T
  · exact Or.inl hST
  · right
    have hS'T' : S' ≠ T' := by
      intro h
      apply hST
      exact Finset.map_injective f h
    have hinter :=
      balancedC5Blowup_distinct_min_covers_inter_card_le_four
        S' T' hS'card hS'cover hT'card hT'cover hS'T'
    have hmapInter : (S ∩ T).map f = S' ∩ T' := by
      simpa [S', T'] using Finset.map_inter (f := f) S T
    calc
      #(S ∩ T) = #((S ∩ T).map f) := by simp
      _ = #(S' ∩ T') := congrArg Finset.card hmapInter
      _ ≤ 4 := hinter

/-- The excess-one attachment to a canonical order-ten exterior forces four
equal minimum covers and hence a six-set with only one complementary edge. -/
theorem false_of_canonical_order_ten_excess_one
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (v : V) (N U : Finset V)
    (hN : N = G.neighborFinset v)
    (hU : U = exteriorFinset G v)
    (hNcard : #N = 5) (hNUdis : Disjoint N U)
    (L : SimpleGraph (U : Set V))
    (hLnonadj : ∀ ⦃x y : (U : Set V)⦄, L.Adj x y →
      ¬G.Adj (x : V) (y : V))
    (iso : L ≃g balancedC5Blowup)
    (hMedges : #((G.induce (N : Set V))ᶜ).edgeFinset = 4)
    (hCedges : #(G.between (N : Set V) (U : Set V)).edgeFinset = 9)
    (hPointLe : ∀ a : (N : Set V),
      (G.induce (N : Set V))ᶜ.degree a ≤
        (G.between (N : Set V) (U : Set V)).degree (a : V)) :
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
  have hcoverLower : ∀ K : Finset (U : Set V),
      L.IsVertexCover (K : Set (U : Set V)) → 6 ≤ #K := by
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
    have haz : a ≠ z := by
      intro h
      exact hnot (Or.inl h)
    have hbz : b ≠ z := by
      intro h
      exact hnot (Or.inr h)
    have habG : ¬G.Adj (a : V) (b : V) := by
      have hcomp : (G.induce (N : Set V))ᶜ.Adj a b := by
        simpa [M] using habM
      simpa using hcomp.2
    have hab : (a : V) ≠ (b : V) := fun h => habM.ne (Subtype.ext h)
    have hlower := six_le_cross_degree_add_of_nonadjacent_pair
      G hfree N U hNUdis a b hab habG L hLnonadj hcoverLower
    have hupper := degree_add_degree_le_card_edges_add_one_of_adj M habM
    rw [show #M.edgeFinset = 4 by simpa [M] using hMedges] at hupper
    rw [← hPointEqOther a haz, ← hPointEqOther b hbz] at hlower
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
  let Z : Finset (U : Set V) := crossNeighborFinset G N U z
  let A (a : (N : Set V)) : Finset (U : Set V) :=
    crossNeighborFinset G N U a
  let K (a : (N : Set V)) : Finset (U : Set V) := Z ∪ A a
  have hZcard : #Z = 5 := by
    rw [show #Z = C.degree (z : V) by
      simpa [Z, C] using
        card_crossNeighborFinset_eq_between_degree G N U hNUdis z]
    exact hzCdegree
  have hAcard (a : (N : Set V)) (haz : a ≠ z) : #(A a) = 1 := by
    rw [show #(A a) = C.degree (a : V) by
      simpa [A, C] using
        card_crossNeighborFinset_eq_between_degree G N U hNUdis a]
    exact hLeafCdegree a haz
  have hzaG (a : (N : Set V)) (haz : a ≠ z) :
      ¬G.Adj (z : V) (a : V) := by
    have hcomp : (G.induce (N : Set V))ᶜ.Adj z a := by
      simpa [M] using hzAdj a haz
    simpa using hcomp.2
  have hKcover (a : (N : Set V)) (haz : a ≠ z) :
      L.IsVertexCover (K a : Set (U : Set V)) := by
    simpa [K, Z, A] using
      crossNeighbor_union_isVertexCover_of_nonadjacent_pair
        G hfree N U hNUdis z a
          (fun h => haz (Subtype.ext h.symm)) (hzaG a haz) L hLnonadj
  have hKcard (a : (N : Set V)) (haz : a ≠ z) : #(K a) = 6 := by
    have hlower := hcoverLower (K a) (hKcover a haz)
    have hu := Finset.card_union_le Z (A a)
    have hA := hAcard a haz
    have hZ := hZcard
    change 6 ≤ #(Z ∪ A a) at hlower
    change #(Z ∪ A a) ≤ #Z + #(A a) at hu
    change #(Z ∪ A a) = 6
    omega
  have hZAdis (a : (N : Set V)) (haz : a ≠ z) : Disjoint Z (A a) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    apply Finset.card_eq_zero.mp
    have hidentity := Finset.card_union_add_card_inter Z (A a)
    have hK := hKcard a haz
    have hA := hAcard a haz
    have hZ := hZcard
    change #(Z ∪ A a) = 6 at hK
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
  have hLeavesCard : #((Finset.univ : Finset (N : Set V)).erase z) = 4 :=
    hEraseCard
  obtain ⟨a0, ha0⟩ := Finset.card_pos.mp (by omega :
    0 < #((Finset.univ : Finset (N : Set V)).erase z))
  have ha0z : a0 ≠ z := by simpa using ha0
  obtain ⟨u, hAu⟩ := Finset.card_eq_one.mp (hAcard a0 ha0z)
  have hAleaves (a : (N : Set V)) (haz : a ≠ z) : A a = {u} :=
    (hAeq a a0 haz ha0z).trans hAu
  have hLeafAdjU (a : (N : Set V)) (haz : a ≠ z) :
      G.Adj (a : V) (u : V) := by
    have hu : u ∈ A a := by simp [hAleaves a haz]
    exact (mem_crossNeighborFinset_iff G N U a u).mp (by
      simpa [A] using hu)
  let Leaves : Finset (N : Set V) := Finset.univ.erase z
  let fN : (N : Set V) ↪ V := Function.Embedding.subtype _
  let A0 : Finset V := Leaves.map fN
  let B0 : Finset V := {v, (u : V)}
  let S : Finset V := insert v (insert (u : V) A0)
  have hA0card : #A0 = 4 := by
    calc
      #A0 = #Leaves := by simp [A0]
      _ = 4 := hLeavesCard
  have hvNotN : v ∉ N := by
    rw [hN]
    exact G.notMem_neighborFinset_self v
  have hvNotA0 : v ∉ A0 := by
    intro hv
    obtain ⟨a, ha, hav⟩ := Finset.mem_map.mp hv
    exact hvNotN (hav ▸ a.property)
  have huNotN : (u : V) ∉ N := fun huN =>
    (Finset.disjoint_left.mp hNUdis) huN u.property
  have huNotA0 : (u : V) ∉ A0 := by
    intro hu
    obtain ⟨a, ha, hau⟩ := Finset.mem_map.mp hu
    exact huNotN (hau ▸ a.property)
  have huFacts : ¬G.Adj v (u : V) ∧ (u : V) ≠ v := by
    simpa [hU, exteriorFinset] using u.property
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
  have hvuExterior : v ≠ (u : V) ∧ ¬G.Adj v (u : V) := by
    exact ⟨huFacts.2.symm, huFacts.1⟩
  have hvuComp : Gᶜ.Adj v (u : V) := hvuExterior
  have hexact := card_induce_pair_add_between_degrees_of_independent
    Gᶜ A0 B0 v (u : V) hvB0 huB0 hvuExterior.1 hA0B0dis hA0ind
  have hcompOne :
      #(Gᶜ.induce ((insert v (insert (u : V) A0) : Finset V) : Set V)).edgeFinset = 1 := by
    have hDdegV : D.degree v = 0 := by simp [hDbot]
    have hDdegU : D.degree (u : V) = 0 := by simp [hDbot]
    simpa [D, hDdegV, hDdegU, hvuComp] using hexact
  have hfour := four_le_card_induced_compl_of_admissible_six G hG S hScard
  have hcompOneS : #(Gᶜ.induce (S : Set V)).edgeFinset = 1 := by
    simpa [S] using hcompOne
  omega

/-- Boolean form of the five-edge small endpoint-degree-sum certificate. -/
def fiveEdgeSmallDegreeSumProperty (e : Fin 10 → Bool) : Prop :=
  edgeBitsDegree e 0 + edgeBitsDegree e 1 + edgeBitsDegree e 2 +
      edgeBitsDegree e 3 + edgeBitsDegree e 4 = 10 →
    (e 0 = true ∧ edgeBitsDegree e 0 + edgeBitsDegree e 1 ≤ 5) ∨
    (e 1 = true ∧ edgeBitsDegree e 0 + edgeBitsDegree e 2 ≤ 5) ∨
    (e 2 = true ∧ edgeBitsDegree e 0 + edgeBitsDegree e 3 ≤ 5) ∨
    (e 3 = true ∧ edgeBitsDegree e 0 + edgeBitsDegree e 4 ≤ 5) ∨
    (e 4 = true ∧ edgeBitsDegree e 1 + edgeBitsDegree e 2 ≤ 5) ∨
    (e 5 = true ∧ edgeBitsDegree e 1 + edgeBitsDegree e 3 ≤ 5) ∨
    (e 6 = true ∧ edgeBitsDegree e 1 + edgeBitsDegree e 4 ≤ 5) ∨
    (e 7 = true ∧ edgeBitsDegree e 2 + edgeBitsDegree e 3 ≤ 5) ∨
    (e 8 = true ∧ edgeBitsDegree e 2 + edgeBitsDegree e 4 ≤ 5) ∨
    (e 9 = true ∧ edgeBitsDegree e 3 + edgeBitsDegree e 4 ≤ 5)

set_option maxRecDepth 10000 in
/-- Transparent compact-code check of all 1024 labelled five-vertex graphs. -/
theorem five_edge_small_degree_sum_code_check :
    ∀ n : Fin (2 ^ 10),
      fiveEdgeSmallDegreeSumProperty (edgeVectorOfCode n) := by
  dsimp only [fiveEdgeSmallDegreeSumProperty]
  decide

/-- Every ten-bit edge vector is covered by the compact certificate. -/
theorem five_edge_small_degree_sum_check (e : Fin 10 → Bool) :
    fiveEdgeSmallDegreeSumProperty e := by
  let f : Fin 10 → Fin 2 := fun i => boolToFinTwo (e i)
  let n : Fin (2 ^ 10) := finFunctionFinEquiv f
  have hcheck := five_edge_small_degree_sum_code_check n
  have hdecode : edgeVectorOfCode n = e := by
    funext i
    simp [edgeVectorOfCode, n, f]
  rw [hdecode] at hcheck
  exact hcheck

/-- Every simple graph on five vertices with five edges has an edge whose
endpoint degrees sum to at most five. -/
theorem exists_adj_degree_add_le_five_of_card_five_edges_five
    {W : Type u} [Fintype W]
    (M : SimpleGraph W) [DecidableRel M.Adj]
    (hcard : Fintype.card W = 5) (hedges : #M.edgeFinset = 5) :
    ∃ a b : W, M.Adj a b ∧ M.degree a + M.degree b ≤ 5 := by
  classical
  letI : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  let e : W ≃ Fin 5 := Fintype.equivFinOfCardEq hcard
  let M5 : SimpleGraph (Fin 5) := M.comap e.symm
  let hiso : M5 ≃g M := SimpleGraph.Iso.comap e.symm M
  have hedges5 : #M5.edgeFinset = 5 := hiso.card_edgeFinset_eq.trans hedges
  let bits : Fin 10 → Bool :=
    ![decide (M5.Adj 0 1), decide (M5.Adj 0 2),
      decide (M5.Adj 0 3), decide (M5.Adj 0 4),
      decide (M5.Adj 1 2), decide (M5.Adj 1 3),
      decide (M5.Adj 1 4), decide (M5.Adj 2 3),
      decide (M5.Adj 2 4), decide (M5.Adj 3 4)]
  have hd0 : edgeBitsDegree bits 0 = M5.degree 0 := by
    simpa [edgeBitsDegree, bits, edgeBit] using
      (fin_five_degree_zero_formula M5).symm
  have hd1 : edgeBitsDegree bits 1 = M5.degree 1 := by
    simpa [edgeBitsDegree, bits, edgeBit] using
      (fin_five_degree_one_formula M5).symm
  have hd2 : edgeBitsDegree bits 2 = M5.degree 2 := by
    simpa [edgeBitsDegree, bits, edgeBit] using
      (fin_five_degree_two_formula M5).symm
  have hd3 : edgeBitsDegree bits 3 = M5.degree 3 := by
    simpa [edgeBitsDegree, bits, edgeBit] using
      (fin_five_degree_three_formula M5).symm
  have hd4 : edgeBitsDegree bits 4 = M5.degree 4 := by
    simpa [edgeBitsDegree, bits, edgeBit] using
      (fin_five_degree_four_formula M5).symm
  have hsum : edgeBitsDegree bits 0 + edgeBitsDegree bits 1 +
      edgeBitsDegree bits 2 + edgeBitsDegree bits 3 +
      edgeBitsDegree bits 4 = 10 := by
    have hdAll : edgeBitsDegree bits = fun x => M5.degree x := by
      funext x
      fin_cases x
      · exact hd0
      · exact hd1
      · exact hd2
      · exact hd3
      · exact hd4
    have hs := M5.sum_degrees_eq_twice_card_edges
    rw [hedges5] at hs
    norm_num at hs
    have hsumFn : (∑ x : Fin 5, edgeBitsDegree bits x) = 10 := by
      calc
        (∑ x : Fin 5, edgeBitsDegree bits x) =
            ∑ x : Fin 5, M5.degree x := by
          apply Finset.sum_congr rfl
          intro x _
          exact congrFun hdAll x
        _ = 10 := hs
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hsumFn
  have hcases := five_edge_small_degree_sum_check bits hsum
  have hlift (i j : Fin 5) (hij : M5.Adj i j)
      (hijDegree : M5.degree i + M5.degree j ≤ 5) :
      ∃ a b : W, M.Adj a b ∧ M.degree a + M.degree b ≤ 5 := by
    refine ⟨e.symm i, e.symm j, hij, ?_⟩
    have hi := hiso.degree_eq i
    have hj := hiso.degree_eq j
    change M.degree (e.symm i) = M5.degree i at hi
    change M.degree (e.symm j) = M5.degree j at hj
    omega
  rcases hcases with h01 | h02 | h03 | h04 | h12 | h13 | h14 | h23 | h24 | h34
  · exact hlift 0 1 (by simpa [bits] using h01.1)
      (by simpa [hd0, hd1] using h01.2)
  · exact hlift 0 2 (by simpa [bits] using h02.1)
      (by simpa [hd0, hd2] using h02.2)
  · exact hlift 0 3 (by simpa [bits] using h03.1)
      (by simpa [hd0, hd3] using h03.2)
  · exact hlift 0 4 (by simpa [bits] using h04.1)
      (by simpa [hd0, hd4] using h04.2)
  · exact hlift 1 2 (by simpa [bits] using h12.1)
      (by simpa [hd1, hd2] using h12.2)
  · exact hlift 1 3 (by simpa [bits] using h13.1)
      (by simpa [hd1, hd3] using h13.2)
  · exact hlift 1 4 (by simpa [bits] using h14.1)
      (by simpa [hd1, hd4] using h14.2)
  · exact hlift 2 3 (by simpa [bits] using h23.1)
      (by simpa [hd2, hd3] using h23.2)
  · exact hlift 2 4 (by simpa [bits] using h24.1)
      (by simpa [hd2, hd4] using h24.2)
  · exact hlift 3 4 (by simpa [bits] using h34.1)
      (by simpa [hd3, hd4] using h34.2)

/-- The exact order-16, 45-edge residual cannot have minimum degree five.
The proof exhausts the bipartite, nineteen-edge, and both twenty-edge
complementary order-ten exterior cases. -/
theorem false_of_admissible_indepSetFree_four_card_sixteen_edges_fortyFive_minDegree_five
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 4)
    (hcard : Fintype.card V = 16) (hedges : #G.edgeFinset = 45)
    (v : V) (hdegree : G.degree v = 5)
    (hmin : ∀ w, G.degree v ≤ G.degree w) :
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
  have hstrong :=
    exterior_edges_add_nineteen_le_edges_of_admissible_degree_five
      G hG v hdegree hmin
  have hRupper : #R.edgeFinset ≤ 26 := by
    have hstrong' : #R.edgeFinset + 19 ≤ 45 := by
      simpa [R, U, hedges] using hstrong
    omega
  have hnotbip : ¬L.IsBipartite := by
    intro hbip
    exact false_of_bipartite_compl_exterior_degree_five_card_sixteen
      G hG hfree hcard v hdegree (by simpa [L, R, U] using hbip)
  have hLupper :=
    card_compl_edges_le_twenty_of_admissible_order_ten_nonbipartite
      R hRadmissible hRfree hUcard (by simpa [L] using hnotbip)
  have hpartitionR := card_edgeFinset_add_card_compl R
  rw [hUcard] at hpartitionR
  norm_num [Nat.choose] at hpartitionR
  have hLrange : #L.edgeFinset = 19 ∨ #L.edgeFinset = 20 := by
    have hLupper' : #L.edgeFinset ≤ 20 := by simpa [L] using hLupper
    have hpartition' : #R.edgeFinset + #L.edgeFinset = 45 := by
      simpa [L] using hpartitionR
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
    simpa [C] using
      SimpleGraph.between_isBipartiteWith (G := G) hNUdisSet
  have hLnonadj : ∀ ⦃x y : (U : Set V)⦄, L.Adj x y →
      ¬G.Adj (x : V) (y : V) := by
    intro x y hxy
    have hcomp : Rᶜ.Adj x y := by simpa [L] using hxy
    have hnotR : ¬R.Adj x y := hcomp.2
    simpa [R] using hnotR
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
        neighborhoodInternalEdgeCount G v) = 45 := by
    simpa [R, U, hdegree, hedges] using hexact
  have hYupper := neighborhoodInternalEdgeCount_le_six_of_admissible_degree_five
    G hG v hdegree
  have htwice := neighborhood_cross_add_twice_internal_ge G v hmin
  rw [hdegree] at htwice
  norm_num at htwice
  rcases hLrange with hL19 | hL20
  · have hRedges : #R.edgeFinset = 26 := by
      have hp : #R.edgeFinset + #L.edgeFinset = 45 := by
        simpa [L] using hpartitionR
      omega
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
    have hLfree : L.IndepSetFree 5 := by
      simpa [L] using
        compl_indepSetFree_five_of_admissible_order_ten_nineteen_edges
          R hRadmissible hUcard (by simpa [L] using hL19)
    have hcoverLower : ∀ K : Finset (U : Set V),
        L.IsVertexCover (K : Set (U : Set V)) → 6 ≤ #K := by
      intro K hK
      exact six_le_card_of_vertexCover_of_indepSetFree_five_card_ten
        L hLfree hUcard K hK
    have hMnonempty : M.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨e, he⟩ := hMnonempty
    induction e using Sym2.inductionOn with
    | hf a b =>
      have habM : M.Adj a b := by simpa using he
      have habG : ¬G.Adj (a : V) (b : V) := by
        have hcomp : Hᶜ.Adj a b := by simpa [M] using habM
        simpa [H] using hcomp.2
      have hab : (a : V) ≠ (b : V) := fun h => habM.ne (Subtype.ext h)
      have hlower := six_le_cross_degree_add_of_nonadjacent_pair
        G hfree N U hNUdis a b hab habG L hLnonadj hcoverLower
      have hupper := degree_add_degree_le_card_edges_add_one_of_adj M habM
      rw [hMedges] at hupper
      rw [← hPointEq a, ← hPointEq b] at hlower
      omega
  · have hRedges : #R.edgeFinset = 25 := by
      have hp : #R.edgeFinset + #L.edgeFinset = 45 := by
        simpa [L] using hpartitionR
      omega
    obtain ⟨iso⟩ :=
      compl_iso_balancedC5Blowup_of_admissible_order_ten_equality
        R hRadmissible hRfree hUcard (by simpa [L] using hnotbip)
          (by simpa [L] using hL20)
    have haccount : neighborhoodCrossEdgeCount G v +
        neighborhoodInternalEdgeCount G v = 15 := by omega
    have hYlower : 5 ≤ neighborhoodInternalEdgeCount G v := by omega
    have hYrange : neighborhoodInternalEdgeCount G v = 5 ∨
        neighborhoodInternalEdgeCount G v = 6 := by omega
    rcases hYrange with hY | hY
    · have hX : neighborhoodCrossEdgeCount G v = 10 := by omega
      have hHedges : #H.edgeFinset = 5 := by
        have hi := neighborhoodInternalEdgeCount_eq_induce G v
        rw [hY] at hi
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
      have hcoverLower : ∀ K : Finset (U : Set V),
          L.IsVertexCover (K : Set (U : Set V)) → 6 ≤ #K := by
        intro K hK
        have hcoverEq : L.vertexCoverNum = 6 :=
          (SimpleGraph.vertexCoverNum_congr iso).trans
            balancedC5Blowup_vertexCoverNum
        have hle := hK.vertexCoverNum_le
        rw [hcoverEq] at hle
        simpa using hle
      obtain ⟨a, b, habM, hpair⟩ :=
        exists_adj_degree_add_le_five_of_card_five_edges_five
          M hNtype hMedges
      have habG : ¬G.Adj (a : V) (b : V) := by
        have hcomp : Hᶜ.Adj a b := by simpa [M] using habM
        simpa [H] using hcomp.2
      have hab : (a : V) ≠ (b : V) := fun h => habM.ne (Subtype.ext h)
      have hlower := six_le_cross_degree_add_of_nonadjacent_pair
        G hfree N U hNUdis a b hab habG L hLnonadj hcoverLower
      rw [← hPointEq a, ← hPointEq b] at hlower
      omega
    · have hX : neighborhoodCrossEdgeCount G v = 9 := by omega
      have hHedges : #H.edgeFinset = 6 := by
        have hi := neighborhoodInternalEdgeCount_eq_induce G v
        rw [hY] at hi
        simpa [H, N] using hi.symm
      have hMpartition := card_edgeFinset_add_card_compl H
      rw [hNtype, hHedges] at hMpartition
      norm_num [Nat.choose] at hMpartition
      have hMedges : #M.edgeFinset = 4 := by
        simpa [M] using (show #Hᶜ.edgeFinset = 4 by omega)
      have hCedges : #C.edgeFinset = 9 := by
        simpa [C, N, U, neighborhoodCrossEdgeCount] using hX
      exact false_of_canonical_order_ten_excess_one
        G hG hfree v N U rfl rfl hNcard hNUdis L hLnonadj iso
          (by simpa [M, H] using hMedges)
          (by simpa [C] using hCedges)
          (fun a => by simpa [M, H, C] using hPointLe a)

/-- The exact order-21 residual produced by edge equalization cannot contain
a degree-four vertex when all of its degrees are at least four. -/
theorem false_of_admissible_indepSetFree_five_card_twentyOne_edges_fiftyFive_degree_four
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 5)
    (hcard : Fintype.card V = 21) (hedges : #G.edgeFinset = 55)
    (hdegreeLower : ∀ w, 4 ≤ G.degree w)
    (v : V) (hdegree : G.degree v = 4) :
    False := by
  classical
  let U := exteriorFinset G v
  let Q := G.induce (U : Set V)
  have hmin : ∀ w, G.degree v ≤ G.degree w := by
    intro w
    rw [hdegree]
    exact hdegreeLower w
  have hUcardRaw := card_exterior_type_add_degree_add_one G v
  have hUcard : Fintype.card (U : Set V) = 16 := by
    rw [hcard, hdegree] at hUcardRaw
    simpa [U] using (show Fintype.card (exteriorFinset G v : Set V) = 16 by
      omega)
  have hQadmissible : Admissible Q := by
    simpa [Q, U] using admissible_induce G hG U
  have hQfree : Q.IndepSetFree 4 := by
    simpa [Q, U] using
      (indepSetFree_exterior_induce G (k := 4) (by simpa using hfree) v)
  have hQlower :=
    card_edges_ge_fortyFive_of_admissible_indepSetFree_four_card_sixteen
      Q hQadmissible hQfree hUcard
  have hexact := card_edges_eq_exterior_add_degree_add_accounting G v
  have hexact' : #Q.edgeFinset + 4 +
      (neighborhoodCrossEdgeCount G v +
        neighborhoodInternalEdgeCount G v) = 55 := by
    simpa [Q, U, hdegree, hedges] using hexact
  have haccountLower :=
    neighborhood_cross_add_internal_ge_choose_degree G v hmin
  have hQedges : #Q.edgeFinset = 45 := by
    rw [hdegree] at haccountLower
    norm_num [Nat.choose] at haccountLower
    omega
  have haccountEq : neighborhoodCrossEdgeCount G v +
      neighborhoodInternalEdgeCount G v = (G.degree v).choose 2 := by
    rw [hdegree]
    norm_num [Nat.choose]
    omega
  have hisolated :=
    neighborhood_accounting_equality_isolatedClique G v hmin haccountEq
  have hQdegreeLower : ∀ w : (U : Set V), 4 ≤ Q.degree w := by
    intro w
    have heq : Q.degree w = G.degree w := by
      simpa [Q, U] using
        degree_induce_exterior_eq_of_isolatedClosedNeighborhood G v
          hisolated w
    rw [heq]
    exact hdegreeLower w
  letI : Nonempty (U : Set V) := Fintype.card_pos_iff.mp (by
    rw [hUcard]
    norm_num)
  obtain ⟨w, hQmin, hQavg⟩ :=
    exists_minimal_vertex_card_mul_degree_le_twice_edges Q
  have hwLower : 4 ≤ Q.degree w := hQdegreeLower w
  have hwUpper : Q.degree w ≤ 5 := by
    rw [hUcard, hQedges] at hQavg
    omega
  interval_cases hwdegree : Q.degree w
  · let U2 := exteriorFinset Q w
    let R := Q.induce (U2 : Set (U : Set V))
    have hQminCase : ∀ x, Q.degree w ≤ Q.degree x := by
      intro x
      rw [hwdegree]
      exact hQdegreeLower x
    have hU2cardRaw := card_exterior_type_add_degree_add_one Q w
    have hU2card : Fintype.card (U2 : Set (U : Set V)) = 11 := by
      rw [hUcard, hwdegree] at hU2cardRaw
      simpa [U2] using (show
        Fintype.card (exteriorFinset Q w : Set (U : Set V)) = 11 by omega)
    have hRadmissible : Admissible R := by
      simpa [R, U2] using admissible_induce Q hQadmissible U2
    have hRfree : R.IndepSetFree 3 := by
      simpa [R, U2] using
        (indepSetFree_exterior_induce Q (k := 3)
          (by simpa using hQfree) w)
    have hsplit := exterior_edges_add_degree_add_choose_le_edges Q w hQminCase
    have hRupper : #R.edgeFinset ≤ 35 := by
      have hsplit' : #R.edgeFinset + Q.degree w +
          (Q.degree w).choose 2 ≤ #Q.edgeFinset := by
        simpa [R, U2] using hsplit
      rw [hwdegree, hQedges] at hsplit'
      norm_num [Nat.choose] at hsplit'
      omega
    have hRlower :=
      card_edges_ge_thirtySix_of_admissible_indepSetFree_three_card_eleven
        R hRadmissible hRfree hU2card
    omega
  · have hQminCase : ∀ x, Q.degree w ≤ Q.degree x := by
      intro x
      rw [hwdegree]
      exact hQmin x
    exact false_of_admissible_indepSetFree_four_card_sixteen_edges_fortyFive_minDegree_five
      Q hQadmissible hQfree hUcard hQedges w hwdegree hQminCase

/-- Consequently every vertex of an exact order-21 residual with minimum
degree at least four actually has degree at least five. -/
theorem five_le_degree_of_admissible_indepSetFree_five_card_twentyOne_edges_fiftyFive
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 5)
    (hcard : Fintype.card V = 21) (hedges : #G.edgeFinset = 55)
    (hdegreeLower : ∀ w, 4 ≤ G.degree w) :
    ∀ w, 5 ≤ G.degree w := by
  intro w
  by_contra hnot
  have hw : G.degree w = 4 := by
    have := hdegreeLower w
    omega
  exact false_of_admissible_indepSetFree_five_card_twentyOne_edges_fiftyFive_degree_four
    G hG hfree hcard hedges hdegreeLower w hw

end Erdos617
