/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.Basic
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Tactic.NormNum

/-!
# Simultaneous complementary colour graphs

These are the elementary facts used before the extremal argument.  Distinct
colour graphs are edge-disjoint, so the union of their complements is the
complete graph.  Pairing proper vertex colourings of two such complements
therefore gives an injection into the product of the two palettes.
-/

@[expose] public section

namespace Erdos617

open Fintype

universe u v

/-- Complements of two distinct colour graphs cover every edge. -/
theorem sup_compl_colorGraph_eq_top {V : Type u} {C : Type v}
    (χ : EdgeColoring V C) {c d : C} (hcd : c ≠ d) :
    (colorGraph χ c)ᶜ ⊔ (colorGraph χ d)ᶜ = (⊤ : SimpleGraph V) := by
  have hd : Disjoint (colorGraph χ c) (colorGraph χ d) :=
    pairwise_disjoint_colorGraph χ hcd
  calc
    (colorGraph χ c)ᶜ ⊔ (colorGraph χ d)ᶜ =
        (colorGraph χ c ⊓ colorGraph χ d)ᶜ := (compl_inf ..).symm
    _ = (⊥ : SimpleGraph V)ᶜ := congrArg (fun G : SimpleGraph V => Gᶜ) hd.eq_bot
    _ = ⊤ := compl_bot

/-- If two graphs cover the complete graph, proper colourings of them pair to
an injective map on vertices. -/
theorem card_le_mul_of_sup_eq_top_colorable {V : Type u} [Fintype V]
    {G H : SimpleGraph V} {a b : ℕ} (hsup : G ⊔ H = ⊤)
    (hG : G.Colorable a) (hH : H.Colorable b) :
    Fintype.card V ≤ a * b := by
  obtain ⟨CG⟩ := hG
  obtain ⟨CH⟩ := hH
  have hinj : Function.Injective (fun v : V => (CG v, CH v)) := by
    intro x y hxy
    by_contra hne
    have hadjTop : (⊤ : SimpleGraph V).Adj x y := by simpa
    have hadj : (G ⊔ H).Adj x y := hsup.symm ▸ hadjTop
    rw [SimpleGraph.sup_adj] at hadj
    cases hadj with
    | inl hx => exact CG.valid hx (congrArg Prod.fst hxy)
    | inr hx => exact CH.valid hx (congrArg Prod.snd hxy)
  simpa using Fintype.card_le_of_injective (fun v : V => (CG v, CH v)) hinj

/-- Chromatic-product inequality for two complementary colour graphs. -/
theorem card_le_mul_of_compl_colorGraph_colorable {V : Type u} [Fintype V]
    {C : Type v} (χ : EdgeColoring V C) {c d : C} (hcd : c ≠ d)
    {a b : ℕ} (hc : (colorGraph χ c)ᶜ.Colorable a)
    (hd : (colorGraph χ d)ᶜ.Colorable b) :
    Fintype.card V ≤ a * b :=
  card_le_mul_of_sup_eq_top_colorable (sup_compl_colorGraph_eq_top χ hcd) hc hd

/-- On 26 vertices, two distinct complementary colour graphs cannot both be
five-colourable, since the paired colouring would inject 26 vertices into 25
ordered colour pairs. -/
theorem not_two_compl_colorGraphs_fiveColorable
    (χ : EdgeColoring (Fin 26) (Fin 5)) {c d : Fin 5} (hcd : c ≠ d) :
    ¬((colorGraph χ c)ᶜ.Colorable 5 ∧ (colorGraph χ d)ᶜ.Colorable 5) := by
  rintro ⟨hc, hd⟩
  have h := card_le_mul_of_compl_colorGraph_colorable χ hcd hc hd
  norm_num at h

end Erdos617
