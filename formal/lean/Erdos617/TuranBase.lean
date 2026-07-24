/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.LocalBounds
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

/-!
# Kernel-checked Turán consequences

Mathlib already contains Turán's theorem.  This module specializes it to the
complementary colour graphs forced by a hypothetical fixed-`r = 5`
counterexample.  It deliberately does not state the stronger Kang--Pikhurko
bound, which is not yet in the checked dependency graph.
-/

@[expose] public section

namespace Erdos617

open Finset Fintype

universe u

/-- A finite graph and its complement partition all unordered pairs. -/
theorem card_edgeFinset_add_card_compl {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    #G.edgeFinset + #Gᶜ.edgeFinset = (Fintype.card V).choose 2 := by
  have hd : Disjoint G.edgeFinset Gᶜ.edgeFinset :=
    SimpleGraph.disjoint_edgeFinset.mpr disjoint_compl_right
  have hunion : G.edgeFinset ∪ Gᶜ.edgeFinset =
      (⊤ : SimpleGraph V).edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | hf x y =>
      simp only [Finset.mem_union, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj, SimpleGraph.top_adj]
      constructor
      · rintro (h | h)
        · exact G.ne_of_adj h
        · exact h.1
      · intro hne
        by_cases h : G.Adj x y
        · exact Or.inl h
        · exact Or.inr ⟨hne, h⟩
  rw [← Finset.card_union_of_disjoint hd, hunion,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]

/-- Every complementary colour graph of a counterexample is `K₆`-free. -/
theorem compl_colorGraph_cliqueFree_six
    (χ : EdgeColoring (Fin 26) (Fin 5)) (hχ : IsCounterexample 6 χ)
    (c : Fin 5) :
    (colorGraph χ c)ᶜ.CliqueFree 6 :=
  (isCounterexample_iff_compl_cliqueFree χ 6).mp hχ c

/-- Turán's theorem gives at most 270 edges in each complementary colour
graph on 26 vertices. -/
theorem compl_colorGraph_card_le_270
    (χ : EdgeColoring (Fin 26) (Fin 5)) (hχ : IsCounterexample 6 χ)
    (c : Fin 5) :
    #(colorGraph χ c)ᶜ.edgeFinset ≤ 270 := by
  have h := (compl_colorGraph_cliqueFree_six χ hχ c).card_edgeFinset_le (r := 5)
  norm_num at h ⊢
  exact h

/-- Consequently every colour graph has at least 55 edges. -/
theorem colorGraph_card_ge_55
    (χ : EdgeColoring (Fin 26) (Fin 5)) (hχ : IsCounterexample 6 χ)
    (c : Fin 5) :
    55 ≤ #(colorGraph χ c).edgeFinset := by
  have hpartition := card_edgeFinset_add_card_compl (colorGraph χ c)
  have hcompl := compl_colorGraph_card_le_270 χ hχ c
  norm_num [Nat.choose] at hpartition
  omega

end Erdos617
