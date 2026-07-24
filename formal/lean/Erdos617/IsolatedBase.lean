/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.TuranBase

/-!
# Excluding an isolated vertex in a smallest colour graph

If a colour graph on 26 vertices had an isolated vertex, its complement would
have a universal vertex.  The remaining 25 vertices would therefore induce a
`K₅`-free graph.  Turán's theorem then forces at least 66 edges in the original
colour graph.  Consequently a colour graph with at most 65 edges in a
hypothetical counterexample has no isolated vertex.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

universe u

/-- Removing an isolated vertex from a graph on 26 vertices, and applying
Turán's theorem to the complementary `K₅`-free graph, leaves at least 66
edges. -/
theorem card_edgeFinset_ge_66_of_compl_cliqueFree_six_of_isIsolated
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hfree : Gᶜ.CliqueFree 6) {v : Fin 26} (hv : G.IsIsolated v) :
    66 ≤ #G.edgeFinset := by
  let s : Set (Fin 26) := {v}ᶜ
  have hvuniv : Gᶜ.IsUniversal v :=
    SimpleGraph.isUniversal_compl_iff_isIsolated.mpr hv
  have hfreeOn : Gᶜ.CliqueFreeOn s 5 := by
    have h := hfree.cliqueFreeOn (s := Set.univ)
    have h' := SimpleGraph.CliqueFreeOn.of_succ Gᶜ h
      (a := v) (Set.mem_univ v)
    simpa [s, hvuniv.neighborSet_eq] using h'
  have hfreeInduce : (Gᶜ.induce s).CliqueFree 5 :=
    (SimpleGraph.cliqueFree_induce_iff Gᶜ s 5).mpr hfreeOn
  have hcardS : Fintype.card s = 25 := by
    change Fintype.card (↥({v}ᶜ : Set (Fin 26))) = 25
    rw [Fintype.card_compl_set]
    norm_num
  have hcomplLe : #(Gᶜ.induce s).edgeFinset ≤ 234 := by
    have h := hfreeInduce.card_edgeFinset_le (r := 4)
    simp only [hcardS] at h
    norm_num at h ⊢
    exact h
  have hcomplInduce : (G.induce s)ᶜ = Gᶜ.induce s := by
    ext x y
    simp only [SimpleGraph.compl_adj, SimpleGraph.induce_adj]
    exact and_congr (Subtype.val_injective.ne_iff).symm Iff.rfl
  have hcomplCard : #((G.induce s)ᶜ).edgeFinset =
      #(Gᶜ.induce s).edgeFinset :=
    congrArg Finset.card (SimpleGraph.edgeFinset_inj.mpr hcomplInduce)
  have hpartition := card_edgeFinset_add_card_compl (G.induce s)
  rw [hcomplCard] at hpartition
  simp only [hcardS] at hpartition
  norm_num [Nat.choose] at hpartition
  have hsupport : G.support ⊆ s := by
    intro x hx
    simp only [s, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hxv
    subst x
    exact (G.mem_support_iff_not_isIsolated.mp hx) hv
  have hcardInduce : #(G.induce s).edgeFinset = #G.edgeFinset :=
    SimpleGraph.card_edgeFinset_induce_of_support_subset hsupport
  omega

/-- A colour graph with at most 65 edges in a hypothetical counterexample has
positive degree at every vertex. -/
theorem colorGraph_not_isIsolated_of_card_le_65
    (χ : EdgeColoring (Fin 26) (Fin 5)) (hχ : IsCounterexample 6 χ)
    (c : Fin 5) (hc : #(colorGraph χ c).edgeFinset ≤ 65) (v : Fin 26) :
    ¬(colorGraph χ c).IsIsolated v := by
  intro hv
  have hge := card_edgeFinset_ge_66_of_compl_cliqueFree_six_of_isIsolated
    (colorGraph χ c) (compl_colorGraph_cliqueFree_six χ hχ c) hv
  omega

/-- In particular, some colour graph has between 55 and 65 edges and no
isolated vertex. -/
theorem exists_sparse_nonisolated_colorGraph
    (χ : EdgeColoring (Fin 26) (Fin 5)) (hχ : IsCounterexample 6 χ) :
    ∃ c : Fin 5,
      55 ≤ #(colorGraph χ c).edgeFinset ∧
      #(colorGraph χ c).edgeFinset ≤ 65 ∧
      ∀ v, ¬(colorGraph χ c).IsIsolated v := by
  obtain ⟨c, hc⟩ := exists_colorGraph_card_le_65 χ
  exact ⟨c, colorGraph_card_ge_55 χ hχ c, hc,
    colorGraph_not_isIsolated_of_card_le_65 χ hχ c hc⟩

end Erdos617
