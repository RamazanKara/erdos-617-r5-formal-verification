/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Order

/-!
# The one-to-eleven local colour bound

Restrict an edge colouring to a finite vertex set and regard it as a function
on that complete graph's unordered edge type.  If every colour occurs, a
single colour can occupy at most `|E| - |C| + 1` edges.  At six vertices and
five colours this is the exact manuscript bound `1 ≤ e(G_c[S]) ≤ 11`.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

universe u v

/-- Restriction of a complete-graph edge colouring to a finite vertex set. -/
abbrev restrictColoring {V : Type u} {C : Type v} (χ : EdgeColoring V C)
    (S : Finset V) : EdgeColoring S C :=
  χ.pullback (Function.Embedding.subtype fun x => x ∈ S)

/-- The type of edges in `S` carrying the specified colour. -/
def ColorFiber {V : Type u} {C : Type v} (χ : EdgeColoring V C)
    (S : Finset V) (c : C) :=
  {e : (⊤ : SimpleGraph S).edgeSet // restrictColoring χ S e = c}

noncomputable instance colorFiberFintype {V : Type u} [DecidableEq V]
    {C : Type v} [DecidableEq C] (χ : EdgeColoring V C)
    (S : Finset V) (c : C) : Fintype (ColorFiber χ S c) := by
  classical
  unfold ColorFiber
  infer_instance

/-- Vertex-pair witnesses of all colours give surjectivity of the restricted
unordered-edge colouring. -/
theorem restrictColoring_surjective_of_seesEveryColor {V : Type u} {C : Type v}
    (χ : EdgeColoring V C) (S : Finset V)
    (hS : SeesEveryColor χ S) : Function.Surjective (restrictColoring χ S) := by
  classical
  intro c
  obtain ⟨u, hu, v, hv, huv, hcolor⟩ := hS c
  let uS : S := ⟨u, hu⟩
  let vS : S := ⟨v, hv⟩
  have huSvS : uS ≠ vS := fun h => huv (congrArg Subtype.val h)
  let e : (⊤ : SimpleGraph S).edgeSet := ⟨s(uS, vS), huSvS⟩
  refine ⟨e, ?_⟩
  change χ.get u v huv = c
  exact hcolor

/-- A surjection between finite types leaves room for at least one preimage
of every value other than `b`. -/
theorem card_fiber_add_pred_le_of_surjective {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq B] (f : A → B)
    (hf : Function.Surjective f) (b : B) :
    Fintype.card {a : A // f a = b} + (Fintype.card B - 1) ≤ Fintype.card A := by
  classical
  choose g hg using hf
  let embed : {a : A // f a = b} ⊕ {d : B // d ≠ b} → A
    | Sum.inl a => a
    | Sum.inr d => g d
  have hinj : Function.Injective embed := by
    intro x y hxy
    rcases x with x | x <;> rcases y with y | y
    · exact congrArg Sum.inl (Subtype.ext hxy)
    · exfalso
      exact y.property ((hg y).symm.trans ((congrArg f hxy).symm.trans x.property))
    · exfalso
      exact x.property ((hg x).symm.trans ((congrArg f hxy).trans y.property))
    · apply congrArg Sum.inr
      apply Subtype.ext
      exact hg x ▸ hg y ▸ congrArg f hxy
  have hcard := Fintype.card_le_of_injective embed hinj
  simpa [Fintype.card_subtype_compl, Fintype.card_subtype_eq] using hcard

/-- The complete graph on a six-element finite set has exactly fifteen
unordered edges. -/
theorem card_top_edges_of_card_six {V : Type u} [DecidableEq V]
    (S : Finset V) (hS : #S = 6) :
    Fintype.card (⊤ : SimpleGraph S).edgeSet = 15 := by
  rw [SimpleGraph.card_edgeSet,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  norm_num [hS, Nat.choose]

/-- In a counterexample, the colour-`c` fiber on every six-set has between
one and eleven edges. -/
theorem colorFiber_card_between_one_eleven {V : Type u} [DecidableEq V]
    (χ : EdgeColoring V (Fin 5)) (hχ : IsCounterexample 6 χ)
    (S : Finset V) (hS : #S = 6) (c : Fin 5) :
    1 ≤ Fintype.card (ColorFiber χ S c) ∧
      Fintype.card (ColorFiber χ S c) ≤ 11 := by
  have hsurj : Function.Surjective (restrictColoring χ S) :=
    restrictColoring_surjective_of_seesEveryColor χ S (hχ S hS)
  have hnonempty : Nonempty (ColorFiber χ S c) := by
    obtain ⟨e, he⟩ := hsurj c
    exact ⟨⟨e, he⟩⟩
  have hlower : 1 ≤ Fintype.card (ColorFiber χ S c) :=
    Fintype.card_pos_iff.mpr hnonempty
  have hupper := card_fiber_add_pred_le_of_surjective
    (restrictColoring χ S) hsurj c
  have hedge := card_top_edges_of_card_six S hS
  change Fintype.card (ColorFiber χ S c) + (Fintype.card (Fin 5) - 1) ≤
    Fintype.card (⊤ : SimpleGraph S).edgeSet at hupper
  simp only [Fintype.card_fin, hedge] at hupper
  exact ⟨hlower, by omega⟩

/-- Membership in the induced colour graph is the same as being an edge of
the complete graph on `S` whose restricted label is `c`. -/
theorem mem_induced_colorGraph_edgeSet_iff {V : Type u}
    {C : Type v} (χ : EdgeColoring V C) (S : Finset V) (c : C)
    (e : Sym2 S) :
    e ∈ ((colorGraph χ c).induce (S : Set V)).edgeSet ↔
      ∃ h : e ∈ (⊤ : SimpleGraph S).edgeSet,
        restrictColoring χ S ⟨e, h⟩ = c := by
  classical
  induction e using Sym2.inductionOn with
  | hf x y =>
      simp only [SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj,
        colorGraph_adj_iff]
      constructor
      · rintro ⟨hxy, hc⟩
        have hsxy : x ≠ y := fun h => hxy (congrArg Subtype.val h)
        exact ⟨hsxy, by change χ.get x y hxy = c; exact hc⟩
      · rintro ⟨hsxy, hc⟩
        have hxy : (x : V) ≠ y := fun h => hsxy (Subtype.ext h)
        exact ⟨hxy, by change χ.get x y hxy = c at hc; exact hc⟩

/-- The induced colour-graph edge type and the restricted-colouring fiber are
equivalent, with the same underlying unordered edge. -/
noncomputable def inducedColorEdgeEquiv {V : Type u} [DecidableEq V]
    {C : Type v} (χ : EdgeColoring V C) (S : Finset V) (c : C) :
    ((colorGraph χ c).induce (S : Set V)).edgeSet ≃ ColorFiber χ S c where
  toFun e :=
    let h := (mem_induced_colorGraph_edgeSet_iff χ S c e).mp e.property
    ⟨⟨e, h.choose⟩, h.choose_spec⟩
  invFun e :=
    ⟨e.1.1, (mem_induced_colorGraph_edgeSet_iff χ S c e.1.1).mpr
      ⟨e.1.property, e.property⟩⟩
  left_inv e := by apply Subtype.ext; rfl
  right_inv e := by apply Subtype.ext; apply Subtype.ext; rfl

/-- Cardinal form of the preceding exact edge-type equivalence. -/
theorem card_colorFiber_eq_card_induced_colorGraph {V : Type u} [DecidableEq V]
    {C : Type v} [DecidableEq C] (χ : EdgeColoring V C)
    (S : Finset V) (c : C) :
    Fintype.card (ColorFiber χ S c) =
      #((colorGraph χ c).induce (S : Set V)).edgeFinset := by
  calc
    Fintype.card (ColorFiber χ S c) =
        Fintype.card ((colorGraph χ c).induce (S : Set V)).edgeSet :=
      (Fintype.card_congr (inducedColorEdgeEquiv χ S c)).symm
    _ = #((colorGraph χ c).induce (S : Set V)).edgeFinset :=
      SimpleGraph.card_edgeSet

/-- Graph-theoretic form of the local one-to-eleven bound. -/
theorem induced_colorGraph_card_between_one_eleven {V : Type u} [DecidableEq V]
    (χ : EdgeColoring V (Fin 5)) (hχ : IsCounterexample 6 χ)
    (S : Finset V) (hS : #S = 6) (c : Fin 5) :
    1 ≤ #((colorGraph χ c).induce (S : Set V)).edgeFinset ∧
      #((colorGraph χ c).induce (S : Set V)).edgeFinset ≤ 11 := by
  simpa [card_colorFiber_eq_card_induced_colorGraph χ S c] using
    colorFiber_card_between_one_eleven χ hχ S hS c

/-- A graph is admissible when every six vertices span at most eleven edges. -/
def Admissible {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  ∀ S : Finset V, #S = 6 → #(G.induce (S : Set V)).edgeFinset ≤ 11

/-- Every colour graph of a counterexample is admissible. -/
theorem colorGraph_admissible_of_counterexample {V : Type u} [DecidableEq V]
    (χ : EdgeColoring V (Fin 5)) (hχ : IsCounterexample 6 χ) (c : Fin 5) :
    Admissible (colorGraph χ c) := by
  intro S hS
  exact (induced_colorGraph_card_between_one_eleven χ hχ S hS c).2

/-- The fibers of a function partition its finite domain. -/
theorem sum_card_fibers {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] (f : A → B) :
    ∑ b : B, Fintype.card {a : A // f a = b} = Fintype.card A := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv f)

/-- The restricted colour fibers partition all unordered edges on `S`. -/
theorem sum_card_colorFiber {V : Type u} [DecidableEq V]
    {C : Type v} [Fintype C] [DecidableEq C]
    (χ : EdgeColoring V C) (S : Finset V) :
    ∑ c : C, Fintype.card (ColorFiber χ S c) =
      Fintype.card (⊤ : SimpleGraph S).edgeSet := by
  change (∑ c : C, Fintype.card
    {e : (⊤ : SimpleGraph S).edgeSet // restrictColoring χ S e = c}) = _
  exact sum_card_fibers (restrictColoring χ S)

/-- Global colour-graph membership, expressed directly as a fiber of the
original edge-labelling function. -/
theorem mem_colorGraph_edgeSet_iff {V : Type u} {C : Type v}
    (χ : EdgeColoring V C) (c : C) (e : Sym2 V) :
    e ∈ (colorGraph χ c).edgeSet ↔
      ∃ h : e ∈ (⊤ : SimpleGraph V).edgeSet, χ ⟨e, h⟩ = c := by
  induction e using Sym2.inductionOn with
  | hf x y =>
      simp only [SimpleGraph.mem_edgeSet, colorGraph_adj_iff]
      rfl

/-- A colour graph's edge type is exactly the corresponding global label
fiber. -/
noncomputable def colorGraphEdgeEquiv {V : Type u} {C : Type v}
    (χ : EdgeColoring V C) (c : C) :
    (colorGraph χ c).edgeSet ≃
      {e : (⊤ : SimpleGraph V).edgeSet // χ e = c} where
  toFun e :=
    let h := (mem_colorGraph_edgeSet_iff χ c e).mp e.property
    ⟨⟨e, h.choose⟩, h.choose_spec⟩
  invFun e :=
    ⟨e.1.1, (mem_colorGraph_edgeSet_iff χ c e.1.1).mpr
      ⟨e.1.property, e.property⟩⟩
  left_inv e := by apply Subtype.ext; rfl
  right_inv e := by apply Subtype.ext; apply Subtype.ext; rfl

theorem card_colorGraph_edgeFinset_eq_card_fiber {V : Type u} [Fintype V] [DecidableEq V]
    {C : Type v} [DecidableEq C] (χ : EdgeColoring V C) (c : C) :
    #(colorGraph χ c).edgeFinset =
      Fintype.card {e : (⊤ : SimpleGraph V).edgeSet // χ e = c} := by
  rw [← SimpleGraph.card_edgeSet]
  exact Fintype.card_congr (colorGraphEdgeEquiv χ c)

/-- Globally, the colour-graph edge counts sum to the number of edges in the
complete graph. -/
theorem sum_card_colorGraph_edgeFinset {V : Type u} [Fintype V] [DecidableEq V]
    {C : Type v} [Fintype C] [DecidableEq C] (χ : EdgeColoring V C) :
    ∑ c : C, #(colorGraph χ c).edgeFinset = (Fintype.card V).choose 2 := by
  calc
    ∑ c : C, #(colorGraph χ c).edgeFinset =
        ∑ c : C, Fintype.card
          {e : (⊤ : SimpleGraph V).edgeSet // χ e = c} := by
      apply Finset.sum_congr rfl
      intro c hc
      exact card_colorGraph_edgeFinset_eq_card_fiber χ c
    _ = Fintype.card (⊤ : SimpleGraph V).edgeSet := sum_card_fibers χ
    _ = (Fintype.card V).choose 2 := by
      rw [SimpleGraph.card_edgeSet,
        SimpleGraph.card_edgeFinset_top_eq_card_choose_two]

/-- A five-colouring of `K₂₆` has a colour graph with at most 65 edges. -/
theorem exists_colorGraph_card_le_65
    (χ : EdgeColoring (Fin 26) (Fin 5)) :
    ∃ c : Fin 5, #(colorGraph χ c).edgeFinset ≤ 65 := by
  have hsum := sum_card_colorGraph_edgeFinset χ
  have hle : (∑ c : Fin 5, #(colorGraph χ c).edgeFinset) ≤
      ∑ _c : Fin 5, 65 := by
    rw [hsum]
    norm_num [Nat.choose]
  obtain ⟨c, hc, hcle⟩ :=
    Finset.exists_le_of_sum_le (s := (univ : Finset (Fin 5))) univ_nonempty hle
  exact ⟨c, hcle⟩

end Erdos617
