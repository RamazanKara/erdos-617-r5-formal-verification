/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.EdgeEqualization
public import Mathlib.Logic.Equiv.Fintype

/-!
# Semantic and symmetry bridge for the finite special-Brooks certificates

This file contains the graph-theoretic part of the E058 bridge.  In
particular, it records relabelling invariance and the first normalization used
by every finite branch: vertex zero is fixed and its five neighbors are
labelled `1, ..., 5`.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

/-- The fixed five-element neighborhood used by all special-Brooks CNFs. -/
def r5FixedNeighbors : Finset (Fin 26) := {1, 2, 3, 4, 5}

@[simp]
theorem card_r5FixedNeighbors : #r5FixedNeighbors = 5 := by
  decide

@[simp]
theorem zero_notMem_r5FixedNeighbors : (0 : Fin 26) ∉ r5FixedNeighbors := by
  decide

/-- Adjoin a distinguished point to a finite-set enumeration.  The resulting
embedding is used twice below, once for the fixed labels and once for the
actual graph neighborhood. -/
noncomputable def pointAndFinsetEmbedding
    {α : Type*} [DecidableEq α] (a : α) (s : Finset α) (ha : a ∉ s)
    {n : ℕ} (hcard : #s = n) : Option (Fin n) ↪ α where
  toFun
    | none => a
    | some i => ((s.equivFinOfCardEq hcard).symm i : α)
  inj' := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some j =>
            exfalso
            apply ha
            have hj := ((s.equivFinOfCardEq hcard).symm j).property
            simpa only [hxy] using hj
    | some i =>
        cases y with
        | none =>
            exfalso
            apply ha
            have hi := ((s.equivFinOfCardEq hcard).symm i).property
            simpa only [hxy] using hi
        | some j =>
            congr 1
            apply (s.equivFinOfCardEq hcard).symm.injective
            apply Subtype.ext
            exact hxy

/-- Pull a graph back along a permutation of its vertex labels. -/
abbrev relabelGraph (G : SimpleGraph (Fin 26)) (e : Equiv.Perm (Fin 26)) :
    SimpleGraph (Fin 26) :=
  G.comap e

@[simp]
theorem relabelGraph_adj_iff (G : SimpleGraph (Fin 26))
    (e : Equiv.Perm (Fin 26)) (u v : Fin 26) :
    (relabelGraph G e).Adj u v ↔ G.Adj (e u) (e v) := by
  rfl

@[simp]
theorem relabelGraph_degree (G : SimpleGraph (Fin 26))
    [DecidableRel G.Adj] (e : Equiv.Perm (Fin 26)) (v : Fin 26) :
    (relabelGraph G e).degree v = G.degree (e v) := by
  rw [← (SimpleGraph.Iso.comap e G).degree_eq v]
  rfl

/-- Clique-freeness is invariant under a permutation of the vertex labels. -/
theorem cliqueFree_relabelGraph_iff (G : SimpleGraph (Fin 26))
    (e : Equiv.Perm (Fin 26)) (n : ℕ) :
    (relabelGraph G e).CliqueFree n ↔ G.CliqueFree n := by
  rw [show relabelGraph G e = G.map e.symm.toEmbedding by
    simpa [relabelGraph] using (SimpleGraph.map_symm G e).symm]
  exact SimpleGraph.cliqueFree_map_iff

/-- Independent-set-freeness is invariant under a permutation of the vertex
labels. -/
theorem indepSetFree_relabelGraph_iff (G : SimpleGraph (Fin 26))
    (e : Equiv.Perm (Fin 26)) (n : ℕ) :
    (relabelGraph G e).IndepSetFree n ↔ G.IndepSetFree n := by
  rw [← SimpleGraph.cliqueFree_compl, ← SimpleGraph.cliqueFree_compl]
  let H := relabelGraph G e
  have hcompl : Hᶜ = relabelGraph Gᶜ e := by
    ext u v
    simp only [H, relabelGraph, SimpleGraph.compl_adj,
      SimpleGraph.comap_adj]
    exact and_congr (not_congr e.injective.eq_iff).symm Iff.rfl
  rw [hcompl, cliqueFree_relabelGraph_iff]

/-- The six-vertex admissibility bound is preserved by a permutation of the
vertex labels. -/
theorem admissible_relabelGraph (G : SimpleGraph (Fin 26))
    [DecidableRel G.Adj] (e : Equiv.Perm (Fin 26)) :
    Admissible G → Admissible (relabelGraph G e) := by
  intro h S hS
  let T := S.map e.toEmbedding
  have hT : #T = 6 := by simpa [T] using hS
  have hbound := h T hT
  let iso := SimpleGraph.Iso.comap e G
  have himage : e '' (S : Set (Fin 26)) = (T : Set (Fin 26)) := by
    ext v
    simp [T]
  have hbij : Set.BijOn e (S : Set (Fin 26)) (T : Set (Fin 26)) :=
    e.image_eq_iff_bijOn.mp himage
  have hedge := (iso.induce hbij).card_edgeFinset_eq
  simpa [relabelGraph] using hedge.trans_le hbound

/-- The six-vertex admissibility bound is invariant under a permutation of
the vertex labels. -/
theorem admissible_relabelGraph_iff (G : SimpleGraph (Fin 26))
    [DecidableRel G.Adj] (e : Equiv.Perm (Fin 26)) :
    Admissible (relabelGraph G e) ↔ Admissible G := by
  constructor
  · intro h
    have hback :=
      admissible_relabelGraph (relabelGraph G e) e.symm h
    have hgraph :
        relabelGraph (relabelGraph G e) e.symm = G := by
      ext u v
      simp [relabelGraph]
    simpa only [hgraph] using hback
  · exact admissible_relabelGraph G e

/-- A five-regular graph can be relabelled while fixing vertex zero so that
the neighborhood of zero is exactly `{1,2,3,4,5}`. -/
theorem exists_relabelGraph_neighborFinset_zero_eq_fixed
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ v, G.degree v = 5) :
    ∃ e : Equiv.Perm (Fin 26),
      e 0 = 0 ∧
      (relabelGraph G e).neighborFinset 0 = r5FixedNeighbors := by
  classical
  have hgraphCard : #(G.neighborFinset 0) = 5 := by
    simpa using hregular 0
  let source := pointAndFinsetEmbedding (0 : Fin 26) r5FixedNeighbors
    zero_notMem_r5FixedNeighbors card_r5FixedNeighbors
  let target := pointAndFinsetEmbedding (0 : Fin 26) (G.neighborFinset 0)
    (G.notMem_neighborFinset_self 0) hgraphCard
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair
    source target source.injective target.injective
  refine ⟨e, ?_, ?_⟩
  · simpa [source, target, pointAndFinsetEmbedding] using he none
  · have he0 : e 0 = 0 := by
      simpa [source, target, pointAndFinsetEmbedding] using he none
    have hsubset :
        r5FixedNeighbors ⊆ (relabelGraph G e).neighborFinset 0 := by
      intro w hw
      let i : Fin 5 :=
        (r5FixedNeighbors.equivFinOfCardEq card_r5FixedNeighbors) ⟨w, hw⟩
      have hsource : source (some i) = w := by
        simp [source, pointAndFinsetEmbedding, i]
      have htarget :
          target (some i) ∈ G.neighborFinset 0 := by
        exact ((G.neighborFinset 0).equivFinOfCardEq hgraphCard).symm i |>.property
      have himage : e w = target (some i) := by
        rw [← hsource]
        exact he (some i)
      rw [SimpleGraph.mem_neighborFinset]
      rw [relabelGraph_adj_iff, he0, ← SimpleGraph.mem_neighborFinset]
      simpa [himage] using htarget
    have hdegree :
        (relabelGraph G e).degree 0 = 5 := by
      rw [relabelGraph_degree, hregular]
    have hcard :
        #((relabelGraph G e).neighborFinset 0) ≤ #r5FixedNeighbors := by
      simp [hdegree]
    exact (Finset.eq_of_subset_of_card_le hsubset hcard).symm

/-- The complete special-Brooks hypothesis package survives the initial
neighborhood normalization. -/
theorem exists_normalized_specialBrooks_graph
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ v, G.degree v = 5) (hG : Admissible G)
    (hclique : G.CliqueFree 6) (hindep : G.IndepSetFree 6) :
    ∃ e : Equiv.Perm (Fin 26),
      (∀ v, (relabelGraph G e).degree v = 5) ∧
      Admissible (relabelGraph G e) ∧
      (relabelGraph G e).CliqueFree 6 ∧
      (relabelGraph G e).IndepSetFree 6 ∧
      (relabelGraph G e).neighborFinset 0 = r5FixedNeighbors := by
  classical
  obtain ⟨e, -, hneighbor⟩ :=
    exists_relabelGraph_neighborFinset_zero_eq_fixed G hregular
  refine ⟨e, ?_, ?_, ?_, ?_, hneighbor⟩
  · intro v
    simpa using hregular (e v)
  · exact (admissible_relabelGraph_iff G e).2 hG
  · exact (cliqueFree_relabelGraph_iff G e 6).2 hclique
  · exact (indepSetFree_relabelGraph_iff G e 6).2 hindep

end Erdos617
