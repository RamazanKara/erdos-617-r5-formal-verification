/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.IsolatedBase
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Neighborhood accounting

This module formalizes the elementary double counting around a minimum-degree
vertex used throughout the fixed-`r = 5` manuscript.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

universe u

/-- Vertices outside a vertex and its open neighborhood. -/
def exteriorFinset {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  (insert v (G.neighborFinset v))ᶜ

/-- The number of edges joining the open neighborhood of `v` to the exterior
of the closed neighborhood. -/
def neighborhoodCrossEdgeCount {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  #(G.between (G.neighborFinset v : Set V)
    (exteriorFinset G v : Set V)).edgeFinset

/-- The spanning graph whose nonisolated part is the subgraph induced by the
open neighborhood of `v`. -/
abbrev neighborhoodInternalGraph {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : SimpleGraph V :=
  G.between (G.neighborFinset v : Set V)
    (G.neighborFinset v : Set V)

/-- The number of edges induced by the open neighborhood of `v`. -/
def neighborhoodInternalEdgeCount {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  #(neighborhoodInternalGraph G v).edgeFinset

/-- The spanning internal graph counts exactly the edges of the usual induced
subgraph on the open neighborhood. -/
theorem neighborhoodInternalEdgeCount_eq_induce
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    neighborhoodInternalEdgeCount G v =
      #(G.induce (G.neighborFinset v : Set V)).edgeFinset := by
  let N := G.neighborFinset v
  let f : (N : Set V) ↪ V := Function.Embedding.subtype _
  have hgraph :
      (G.induce (N : Set V)).map f = neighborhoodInternalGraph G v := by
    ext a b
    rw [SimpleGraph.map_adj]
    simp only [SimpleGraph.induce_adj, neighborhoodInternalGraph,
      SimpleGraph.between_adj]
    constructor
    · rintro ⟨a', b', hab, rfl, rfl⟩
      exact ⟨hab, Or.inl ⟨a'.property, b'.property⟩⟩
    · rintro ⟨hab, hparts⟩
      rcases hparts with ⟨haN, hbN⟩ | ⟨haN, hbN⟩
      · exact ⟨⟨a, haN⟩, ⟨b, hbN⟩, hab, rfl, rfl⟩
      · exact ⟨⟨a, haN⟩, ⟨b, hbN⟩, hab, rfl, rfl⟩
  have hedge :
      #((G.induce (N : Set V)).map f).edgeFinset =
        #(neighborhoodInternalGraph G v).edgeFinset :=
    congrArg Finset.card (SimpleGraph.edgeFinset_inj.mpr hgraph)
  calc
    neighborhoodInternalEdgeCount G v =
        #((G.induce (N : Set V)).map f).edgeFinset := by
      simpa [neighborhoodInternalEdgeCount] using hedge.symm
    _ = #(G.induce (N : Set V)).edgeFinset :=
      SimpleGraph.card_edgeFinset_map f _

/-- A neighbor's incident edges split into its edge to the center, its edges
inside the center's neighborhood, and its edges to the exterior. -/
theorem degree_neighbor_eq_one_add_internal_add_cross
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v a : V)
    (ha : a ∈ G.neighborFinset v) :
    G.degree a =
      1 + (neighborhoodInternalGraph G v).degree a +
        (G.between (G.neighborFinset v : Set V)
          (exteriorFinset G v : Set V)).degree a := by
  let N := G.neighborFinset v
  let U := exteriorFinset G v
  let I := G.neighborFinset a ∩ N
  let C := G.neighborFinset a ∩ U
  have hva : G.Adj v a := (SimpleGraph.mem_neighborFinset G v a).mp ha
  have hav : G.Adj a v := hva.symm
  have hsplit : G.neighborFinset a = {v} ∪ (I ∪ C) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, mem_union, mem_singleton,
      mem_inter, I, C]
    constructor
    · intro haw
      by_cases hwv : w = v
      · exact Or.inl hwv
      · by_cases hwN : w ∈ N
        · exact Or.inr (Or.inl ⟨haw, hwN⟩)
        · have hnotadj : ¬G.Adj v w := by simpa [N] using hwN
          exact Or.inr (Or.inr
            ⟨haw, by simp [U, exteriorFinset, hwv, hnotadj]⟩)
    · rintro (rfl | ⟨haw, _⟩ | ⟨haw, _⟩)
      · exact hav
      · exact haw
      · exact haw
  have hdIC : Disjoint I C := by
    rw [Finset.disjoint_left]
    intro w hwI hwC
    have hwN : w ∈ N := (mem_inter.mp hwI).2
    have hwU : w ∈ U := (mem_inter.mp hwC).2
    have hvw : G.Adj v w := by simpa [N] using hwN
    have hwU' : w ≠ v ∧ ¬G.Adj v w := by
      simpa [U, exteriorFinset] using hwU
    exact hwU'.2 hvw
  have hdv : Disjoint ({v} : Finset V) (I ∪ C) := by
    rw [Finset.disjoint_left]
    intro w hwv hw
    have hwv' : w = v := mem_singleton.mp hwv
    subst w
    rcases mem_union.mp hw with hwI | hwC
    · have hvN : v ∈ N := (mem_inter.mp hwI).2
      simp [N] at hvN
    · have hvU : v ∈ U := (mem_inter.mp hwC).2
      simp [U, exteriorFinset] at hvU
  have hinternalNeighbors :
      (neighborhoodInternalGraph G v).neighborFinset a = I := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, neighborhoodInternalGraph,
      SimpleGraph.between_adj, mem_inter, I]
    constructor
    · rintro ⟨haw, hparts⟩
      rcases hparts with ⟨_, hwN⟩ | ⟨_, hwN⟩
      · exact ⟨haw, hwN⟩
      · exact ⟨haw, hwN⟩
    · rintro ⟨haw, hwN⟩
      exact ⟨haw, Or.inl ⟨ha, hwN⟩⟩
  have hI : #I = (neighborhoodInternalGraph G v).degree a := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hinternalNeighbors]
  have haU : a ∉ U := by
    simp [U, exteriorFinset, ha]
  have hcrossNeighbors :
      (G.between (G.neighborFinset v : Set V)
        (exteriorFinset G v : Set V)).neighborFinset a = C := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.between_adj,
      mem_inter, C]
    constructor
    · rintro ⟨haw, hparts⟩
      rcases hparts with ⟨_, hwU⟩ | ⟨haU', _⟩
      · exact ⟨haw, hwU⟩
      · exact (haU haU').elim
    · rintro ⟨haw, hwU⟩
      exact ⟨haw, Or.inl ⟨ha, hwU⟩⟩
  have hC : #C =
      (G.between (G.neighborFinset v : Set V)
        (exteriorFinset G v : Set V)).degree a := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hcrossNeighbors]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hsplit,
    card_union_of_disjoint hdv, card_singleton,
    card_union_of_disjoint hdIC, hI, hC]
  omega

/-- Summing the preceding decomposition over the whole neighborhood gives the
exact accounting identity used in the manuscript. -/
theorem sum_degrees_neighborFinset_eq_accounting
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (∑ a ∈ G.neighborFinset v, G.degree a) =
      G.degree v + 2 * neighborhoodInternalEdgeCount G v +
        neighborhoodCrossEdgeCount G v := by
  let N := G.neighborFinset v
  let U := exteriorFinset G v
  let GI := neighborhoodInternalGraph G v
  let B := G.between (N : Set V) (U : Set V)
  have hpoint (a : V) (ha : a ∈ N) :
      G.degree a = 1 + GI.degree a + B.degree a := by
    exact degree_neighbor_eq_one_add_internal_add_cross G v a ha
  have hsupport : GI.support.toFinset ⊆ N := by
    intro a ha
    have ha' : a ∈ GI.support := by simpa using ha
    obtain ⟨w, haw⟩ := ha'
    have hparts := (SimpleGraph.between_adj.mp haw).2
    rcases hparts with ⟨haN, _⟩ | ⟨haN, _⟩
    · exact haN
    · exact haN
  have hzero : ∀ a ∈ N, a ∉ GI.support.toFinset → GI.degree a = 0 := by
    intro a _ ha
    rw [SimpleGraph.degree_eq_zero_iff_notMem_support]
    simpa using ha
  have hinternal : (∑ a ∈ N, GI.degree a) = 2 * #GI.edgeFinset := by
    rw [← SimpleGraph.sum_degrees_support_eq_twice_card_edges]
    exact (Finset.sum_subset hsupport hzero).symm
  have hdisFin : Disjoint N U := by
    rw [Finset.disjoint_left]
    intro a haN haU
    have hva : G.Adj v a := by simpa [N] using haN
    have haU' : a ≠ v ∧ ¬G.Adj v a := by
      simpa [U, exteriorFinset] using haU
    exact haU'.2 hva
  have hdisSet : Disjoint (N : Set V) (U : Set V) := by
    exact Finset.disjoint_coe.mpr hdisFin
  have hbip : B.IsBipartiteWith (N : Set V) (U : Set V) :=
    SimpleGraph.between_isBipartiteWith hdisSet
  have hcrossFin : (∑ a ∈ N, B.degree a) = #B.edgeFinset :=
    SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hbip
  calc
    (∑ a ∈ N, G.degree a) =
        ∑ a ∈ N, (1 + GI.degree a + B.degree a) := by
      exact Finset.sum_congr rfl hpoint
    _ = #N + (∑ a ∈ N, GI.degree a) + (∑ a ∈ N, B.degree a) := by
      simp [sum_add_distrib, Nat.add_assoc]
    _ = G.degree v + 2 * neighborhoodInternalEdgeCount G v +
        neighborhoodCrossEdgeCount G v := by
      simp [N, U, GI, B, neighborhoodInternalEdgeCount,
        neighborhoodCrossEdgeCount, SimpleGraph.card_neighborFinset_eq_degree,
        hinternal, hcrossFin]

/-- At a minimum-degree vertex, the crossing count plus twice the internal
count is at least `d(d-1)`. -/
theorem neighborhood_cross_add_twice_internal_ge
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hmin : ∀ w, G.degree v ≤ G.degree w) :
    G.degree v * (G.degree v - 1) ≤
      neighborhoodCrossEdgeCount G v +
        2 * neighborhoodInternalEdgeCount G v := by
  let d := G.degree v
  let N := G.neighborFinset v
  have hcardN : #N = d := by
    exact SimpleGraph.card_neighborFinset_eq_degree G v
  have hsumLower : d * d ≤ ∑ a ∈ N, G.degree a := by
    calc
      d * d = ∑ _a ∈ N, d := by simp [hcardN]
      _ ≤ ∑ a ∈ N, G.degree a := by
        exact Finset.sum_le_sum fun a _ => hmin a
  have hsum := sum_degrees_neighborFinset_eq_accounting G v
  have hmul : d * d = d + d * (d - 1) := by
    cases d with
    | zero => simp
    | succ k => simp [Nat.mul_succ, Nat.add_comm]
  dsimp [d, N] at hsumLower hmul ⊢
  omega

/-- The neighborhood-induced graph has at most `choose d 2` edges. -/
theorem neighborhoodInternalEdgeCount_le_choose_degree
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    neighborhoodInternalEdgeCount G v ≤ (G.degree v).choose 2 := by
  let N := G.neighborFinset v
  have h := SimpleGraph.card_edgeFinset_le_card_choose_two
    (G := G.induce (N : Set V))
  have hcardN : Fintype.card (N : Set V) = G.degree v := by
    calc
      Fintype.card (N : Set V) = #N := by simp
      _ = G.degree v := SimpleGraph.card_neighborFinset_eq_degree G v
  rw [hcardN] at h
  rw [neighborhoodInternalEdgeCount_eq_induce G v]
  exact h

/-- The total number of internal and crossing edges is at least
`choose d 2` at a minimum-degree vertex. -/
theorem neighborhood_cross_add_internal_ge_choose_degree
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hmin : ∀ w, G.degree v ≤ G.degree w) :
    (G.degree v).choose 2 ≤
      neighborhoodCrossEdgeCount G v + neighborhoodInternalEdgeCount G v := by
  have hfirst := neighborhood_cross_add_twice_internal_ge G v hmin
  have hY := neighborhoodInternalEdgeCount_le_choose_degree G v
  have htwice : 2 * (G.degree v).choose 2 =
      G.degree v * (G.degree v - 1) := by
    rw [Nat.choose_two_right, mul_comm 2,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self (G.degree v))]
  omega

/-- The spanning graph that keeps exactly the edges internal to a finite set
has the same number of edges as the usual induced graph on that set. -/
theorem card_between_self_eq_card_induce
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    #(G.between (S : Set V) (S : Set V)).edgeFinset =
      #(G.induce (S : Set V)).edgeFinset := by
  let f : (S : Set V) ↪ V := Function.Embedding.subtype _
  have hgraph :
      (G.induce (S : Set V)).map f =
        G.between (S : Set V) (S : Set V) := by
    ext a b
    rw [SimpleGraph.map_adj]
    simp only [SimpleGraph.induce_adj, SimpleGraph.between_adj]
    constructor
    · rintro ⟨a', b', hab, rfl, rfl⟩
      exact ⟨hab, Or.inl ⟨a'.property, b'.property⟩⟩
    · rintro ⟨hab, hparts⟩
      rcases hparts with ⟨haS, hbS⟩ | ⟨haS, hbS⟩
      · exact ⟨⟨a, haS⟩, ⟨b, hbS⟩, hab, rfl, rfl⟩
      · exact ⟨⟨a, haS⟩, ⟨b, hbS⟩, hab, rfl, rfl⟩
  have hedge :
      #((G.induce (S : Set V)).map f).edgeFinset =
        #(G.between (S : Set V) (S : Set V)).edgeFinset :=
    congrArg Finset.card (SimpleGraph.edgeFinset_inj.mpr hgraph)
  calc
    #(G.between (S : Set V) (S : Set V)).edgeFinset =
        #((G.induce (S : Set V)).map f).edgeFinset := hedge.symm
    _ = #(G.induce (S : Set V)).edgeFinset :=
      SimpleGraph.card_edgeFinset_map f _

/-- The edges from the center to its neighborhood, together with all edges
inside the neighborhood, inject into the graph induced by the closed
neighborhood. -/
theorem degree_add_internal_le_closedNeighborhood
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.degree v + neighborhoodInternalEdgeCount G v ≤
      #(G.induce (insert v (G.neighborFinset v) : Finset V)).edgeFinset := by
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
  have hstarSum : (∑ a ∈ V0, Star.degree a) =
      #Star.edgeFinset :=
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
    rcases hinParts with ⟨haN, hbN⟩ | ⟨haN, hbN⟩
    · rcases hstarParts with ⟨haV, _⟩ | ⟨_, hbV⟩
      · have haEq : a = v := by simpa [V0] using haV
        exact hvN (haEq ▸ haN)
      · have hbEq : b = v := by simpa [V0] using hbV
        exact hvN (hbEq ▸ hbN)
    · rcases hstarParts with ⟨haV, _⟩ | ⟨_, hbV⟩
      · have haEq : a = v := by simpa [V0] using haV
        exact hvN (haEq ▸ haN)
      · have hbEq : b = v := by simpa [V0] using hbV
        exact hvN (hbEq ▸ hbN)
  have hdisEdges : Disjoint Star.edgeFinset Inside.edgeFinset :=
    SimpleGraph.disjoint_edgeFinset.mpr hdisGraphs
  have hJcard : #J.edgeFinset = #Star.edgeFinset + #Inside.edgeFinset := by
    change #(Star ⊔ Inside).edgeFinset = _
    rw [SimpleGraph.edgeFinset_sup,
      Finset.card_union_of_disjoint hdisEdges]
  have hstarLe : Star ≤ K := by
    intro a b hab
    have hparts := SimpleGraph.between_adj.mp hab
    rcases hparts.2 with ⟨haV, hbN⟩ | ⟨haN, hbV⟩
    · have haEq : a = v := by simpa [V0] using haV
      have haS : a ∈ S := haEq ▸ Finset.mem_insert_self v N
      have hbS : b ∈ S := Finset.mem_insert_of_mem hbN
      exact SimpleGraph.between_adj.mpr
        ⟨hparts.1, Or.inl ⟨haS, hbS⟩⟩
    · have haS : a ∈ S := Finset.mem_insert_of_mem haN
      have hbEq : b = v := by simpa [V0] using hbV
      have hbS : b ∈ S := hbEq ▸ Finset.mem_insert_self v N
      exact SimpleGraph.between_adj.mpr
        ⟨hparts.1, Or.inl ⟨haS, hbS⟩⟩
  have hinsideLe : Inside ≤ K := by
    intro a b hab
    have hparts := SimpleGraph.between_adj.mp hab
    rcases hparts.2 with ⟨haN, hbN⟩ | ⟨haN, hbN⟩
    · exact SimpleGraph.between_adj.mpr
        ⟨hparts.1, Or.inl
          ⟨Finset.mem_insert_of_mem haN, Finset.mem_insert_of_mem hbN⟩⟩
    · exact SimpleGraph.between_adj.mpr
        ⟨hparts.1, Or.inl
          ⟨Finset.mem_insert_of_mem haN, Finset.mem_insert_of_mem hbN⟩⟩
  have hJle : J ≤ K := by
    apply sup_le
    · exact hstarLe
    · exact hinsideLe
  have hcardLe : #J.edgeFinset ≤ #K.edgeFinset :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hJle)
  have hKcard : #K.edgeFinset =
      #(G.induce (S : Set V)).edgeFinset := by
    simpa [K] using card_between_self_eq_card_induce G S
  calc
    G.degree v + neighborhoodInternalEdgeCount G v = #J.edgeFinset := by
      rw [hJcard, hstarCard]
      rfl
    _ ≤ #K.edgeFinset := hcardLe
    _ = #(G.induce (S : Set V)).edgeFinset := hKcard

/-- In an admissible graph, a minimum-degree vertex of degree five has at most
six edges inside its neighborhood. -/
theorem neighborhoodInternalEdgeCount_le_six_of_admissible_degree_five
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : Admissible G)
    (v : V) (hdegree : G.degree v = 5) :
    neighborhoodInternalEdgeCount G v ≤ 6 := by
  let S := insert v (G.neighborFinset v)
  have hvN : v ∉ G.neighborFinset v := G.notMem_neighborFinset_self v
  have hcardS : #S = 6 := by
    simp [S, hvN, SimpleGraph.card_neighborFinset_eq_degree, hdegree]
  have hlocal := hG S hcardS
  have hlower := degree_add_internal_le_closedNeighborhood G v
  dsimp [S] at hlocal
  omega

/-- At an admissible degree-five minimum vertex, the combined crossing and
internal count is at least fourteen. -/
theorem neighborhood_cross_add_internal_ge_fourteen
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : Admissible G)
    (v : V) (hdegree : G.degree v = 5)
    (hmin : ∀ w, G.degree v ≤ G.degree w) :
    14 ≤ neighborhoodCrossEdgeCount G v +
      neighborhoodInternalEdgeCount G v := by
  have hfirst := neighborhood_cross_add_twice_internal_ge G v hmin
  have hY := neighborhoodInternalEdgeCount_le_six_of_admissible_degree_five
    G hG v hdegree
  rw [hdegree] at hfirst
  norm_num at hfirst
  omega

/-- A finite vertex set is an isolated clique when every two distinct vertices
inside it are adjacent and no edge leaves it. -/
def IsIsolatedCliqueOn {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : Prop :=
  (∀ ⦃a b : V⦄, a ∈ S → b ∈ S → a ≠ b → G.Adj a b) ∧
    (∀ ⦃a b : V⦄, a ∈ S → b ∉ S → ¬G.Adj a b)

/-- Equality in the basic neighborhood-accounting bound forces all possible
internal edges and no crossing edges. -/
theorem neighborhood_accounting_equality_forces_extremes
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hmin : ∀ w, G.degree v ≤ G.degree w)
    (heq : neighborhoodCrossEdgeCount G v +
        neighborhoodInternalEdgeCount G v = (G.degree v).choose 2) :
    neighborhoodCrossEdgeCount G v = 0 ∧
      neighborhoodInternalEdgeCount G v = (G.degree v).choose 2 := by
  have hfirst := neighborhood_cross_add_twice_internal_ge G v hmin
  have hY := neighborhoodInternalEdgeCount_le_choose_degree G v
  have htwice : 2 * (G.degree v).choose 2 =
      G.degree v * (G.degree v - 1) := by
    rw [Nat.choose_two_right, mul_comm 2,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self (G.degree v))]
  omega

/-- If no edge leaves a vertex's open neighborhood and that neighborhood has
the maximum possible number of internal edges, then the closed neighborhood
is an isolated clique. -/
theorem neighborhood_extreme_counts_isolatedClique
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hcross : neighborhoodCrossEdgeCount G v = 0)
    (hinternal : neighborhoodInternalEdgeCount G v =
      (G.degree v).choose 2) :
    IsIsolatedCliqueOn G (insert v (G.neighborFinset v)) := by
  let N := G.neighborFinset v
  let U := exteriorFinset G v
  let F := G.induce (N : Set V)
  let B := G.between (N : Set V) (U : Set V)
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
  have hBcard : #B.edgeFinset = 0 := by
    simpa [B, N, U, neighborhoodCrossEdgeCount] using hcross
  have hBedges : B.edgeFinset = (⊥ : SimpleGraph V).edgeFinset := by
    rw [SimpleGraph.edgeFinset_bot]
    exact Finset.card_eq_zero.mp hBcard
  have hBbot : B = (⊥ : SimpleGraph V) :=
    SimpleGraph.edgeFinset_inj.mp hBedges
  constructor
  · intro a b haS hbS hab
    by_cases hav : a = v
    · subst a
      have hbN : b ∈ N := by
        rcases Finset.mem_insert.mp hbS with hbv | hbN
        · exact (hab hbv.symm).elim
        · exact hbN
      exact (SimpleGraph.mem_neighborFinset G v b).mp hbN
    · have haN : a ∈ N := (Finset.mem_insert.mp haS).resolve_left hav
      by_cases hbv : b = v
      · subst b
        exact ((SimpleGraph.mem_neighborFinset G v a).mp haN).symm
      · have hbN : b ∈ N := (Finset.mem_insert.mp hbS).resolve_left hbv
        let aN : (N : Set V) := ⟨a, haN⟩
        let bN : (N : Set V) := ⟨b, hbN⟩
        have habN : aN ≠ bN := by
          intro h
          exact hab (congrArg Subtype.val h)
        have hFab : F.Adj aN bN :=
          (SimpleGraph.eq_top_iff_forall_ne_adj.mp hFtop) aN bN habN
        simpa [F, aN, bN, SimpleGraph.induce_adj] using hFab
  · intro a b haS hbS
    by_cases hav : a = v
    · subst a
      intro hab
      have hbN : b ∈ G.neighborFinset v :=
        (SimpleGraph.mem_neighborFinset G v b).mpr hab
      exact hbS (Finset.mem_insert_of_mem hbN)
    · have haN : a ∈ N := (Finset.mem_insert.mp haS).resolve_left hav
      have hbU : b ∈ U := by
        simpa [U, exteriorFinset, N] using hbS
      intro hab
      have hBab : B.Adj a b :=
        SimpleGraph.between_adj.mpr ⟨hab, Or.inl ⟨haN, hbU⟩⟩
      rw [hBbot] at hBab
      exact hBab

/-- The equality case in the minimum-degree neighborhood bound is precisely
an isolated closed-neighborhood clique. -/
theorem neighborhood_accounting_equality_isolatedClique
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hmin : ∀ w, G.degree v ≤ G.degree w)
    (heq : neighborhoodCrossEdgeCount G v +
        neighborhoodInternalEdgeCount G v = (G.degree v).choose 2) :
    IsIsolatedCliqueOn G (insert v (G.neighborFinset v)) := by
  obtain ⟨hcross, hinternal⟩ :=
    neighborhood_accounting_equality_forces_extremes G v hmin heq
  exact neighborhood_extreme_counts_isolatedClique G v hcross hinternal

end Erdos617
