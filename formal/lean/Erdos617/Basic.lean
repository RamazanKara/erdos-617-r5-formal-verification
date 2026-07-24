/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling

/-!
# Exact edge-colouring semantics for Erdős Problem 617

This file fixes the quantifiers used by the project.  A colouring is a
`SimpleGraph.TopEdgeLabeling`, hence a total function on the unordered,
non-diagonal pairs of vertices.  In particular, loops are not silently given
colours and the two orientations of an edge cannot receive different colours.
-/

@[expose] public section

open Finset

namespace Erdos617

universe u v

/-- A total colouring of the unordered edges of the complete graph on `V`. -/
abbrev EdgeColoring (V : Type u) (C : Type v) :=
  SimpleGraph.TopEdgeLabeling V C

/-- The colour `c` occurs on an edge whose two endpoints lie in `S`. -/
def ColorPresent {V : Type u} {C : Type v} (χ : EdgeColoring V C)
    (S : Finset V) (c : C) : Prop :=
  ∃ u ∈ S, ∃ v ∈ S, ∃ h : u ≠ v, χ.get u v h = c

/-- No edge with both endpoints in `S` has colour `c`. -/
def ColorAbsent {V : Type u} {C : Type v} (χ : EdgeColoring V C)
    (S : Finset V) (c : C) : Prop :=
  ¬ColorPresent χ S c

/-- Every available colour occurs on an edge spanned by `S`. -/
def SeesEveryColor {V : Type u} {C : Type v} (χ : EdgeColoring V C)
    (S : Finset V) : Prop :=
  ∀ c, ColorPresent χ S c

/-- A counterexample at set size `k`: every `k`-set sees every colour. -/
def IsCounterexample {V : Type u} {C : Type v} (k : ℕ)
    (χ : EdgeColoring V C) : Prop :=
  ∀ S : Finset V, #S = k → SeesEveryColor χ S

/-- The desired upper assertion on a fixed vertex and colour type. -/
def UpperStatement (V : Type u) (C : Type v) (k : ℕ) : Prop :=
  ∀ χ : EdgeColoring V C,
    ∃ S : Finset V, #S = k ∧ ∃ c : C, ColorAbsent χ S c

/-- The exact fixed `r = 5` upper assertion under audit. -/
abbrev R5Upper : Prop := UpperStatement (Fin 26) (Fin 5) 6

/-- The assertion of Erdős Problem 617 at a fixed number `r` of colours. -/
def Problem617At (r : ℕ) : Prop :=
  UpperStatement (Fin (r ^ 2 + 1)) (Fin r) (r + 1)

/-- The full all-`r` conjecture, deliberately separated from every fixed case. -/
def Problem617 : Prop :=
  ∀ r : ℕ, 3 ≤ r → Problem617At r

/-- The original fixed-case formula at `r = 5` is definitionally the exact
`Fin 26`, five-colour, six-vertex upper statement used by the audit. -/
theorem problem617At_five_iff_r5Upper : Problem617At 5 ↔ R5Upper := by
  rfl

/-- The colour graph contains exactly the edges carrying `c`. -/
abbrev colorGraph {V : Type u} {C : Type v} (χ : EdgeColoring V C) (c : C) :
    SimpleGraph V :=
  χ.labelGraph c

theorem colorGraph_adj_iff {V : Type u} {C : Type v} (χ : EdgeColoring V C)
    (c : C) (u v : V) :
    (colorGraph χ c).Adj u v ↔ ∃ h : u ≠ v, χ.get u v h = c := by
  exact SimpleGraph.TopEdgeLabeling.labelGraph_adj u v

/-- A set misses `c` exactly when it is independent in the `c`-colour graph. -/
theorem colorAbsent_iff_isIndepSet {V : Type u} {C : Type v}
    (χ : EdgeColoring V C) (S : Finset V) (c : C) :
    ColorAbsent χ S c ↔ (colorGraph χ c).IsIndepSet (S : Set V) := by
  simp only [ColorAbsent, ColorPresent, SimpleGraph.isIndepSet_iff, Set.Pairwise]
  constructor
  · intro h u hu v hv huv hadj
    apply h
    rw [colorGraph_adj_iff] at hadj
    obtain ⟨hne, hcolor⟩ := hadj
    exact ⟨u, hu, v, hv, hne, hcolor⟩
  · intro h ⟨u, hu, v, hv, huv, hcolor⟩
    exact h hu hv huv (colorGraph_adj_iff χ c u v |>.2 ⟨huv, hcolor⟩)

/-- Equivalently, a missing colour is a clique in the complementary graph. -/
theorem colorAbsent_iff_isClique_compl {V : Type u} {C : Type v}
    (χ : EdgeColoring V C) (S : Finset V) (c : C) :
    ColorAbsent χ S c ↔ (colorGraph χ c)ᶜ.IsClique (S : Set V) := by
  rw [colorAbsent_iff_isIndepSet, SimpleGraph.isClique_compl]

/-- The counterexample condition is exactly independent-set-freeness of every
colour graph. -/
theorem isCounterexample_iff_indepSetFree {V : Type u} {C : Type v}
    (χ : EdgeColoring V C) (k : ℕ) :
    IsCounterexample k χ ↔ ∀ c : C, (colorGraph χ c).IndepSetFree k := by
  constructor
  · intro hχ c S hS
    exact (colorAbsent_iff_isIndepSet χ S c).mpr hS.isIndepSet
      (hχ S hS.card_eq c)
  · intro hfree S hcard c
    by_contra habsent
    exact hfree c S ⟨(colorAbsent_iff_isIndepSet χ S c).mp habsent, hcard⟩

/-- Equivalently, every complementary colour graph is `K_k`-free. -/
theorem isCounterexample_iff_compl_cliqueFree {V : Type u} {C : Type v}
    (χ : EdgeColoring V C) (k : ℕ) :
    IsCounterexample k χ ↔ ∀ c : C, (colorGraph χ c)ᶜ.CliqueFree k := by
  rw [isCounterexample_iff_indepSetFree]
  simp

/-- The label graphs partition all edges of the complete graph. -/
theorem iSup_colorGraph {V : Type u} {C : Type v} (χ : EdgeColoring V C) :
    ⨆ c : C, colorGraph χ c = (⊤ : SimpleGraph V) := by
  exact χ.iSup_labelGraph

/-- Different colour graphs have disjoint edge sets. -/
theorem pairwise_disjoint_colorGraph {V : Type u} {C : Type v}
    (χ : EdgeColoring V C) :
    Pairwise fun c d : C => Disjoint (colorGraph χ c) (colorGraph χ d) := by
  exact SimpleGraph.EdgeLabeling.pairwise_disjoint_labelGraph

/-- Relabel the vertices of a complete-graph edge colouring by an equivalence. -/
abbrev pullbackEquiv {V : Type u} {W : Type*} {C : Type v}
    (χ : EdgeColoring V C) (e : W ≃ V) : EdgeColoring W C :=
  χ.pullback e.toEmbedding

/-- The counterexample property is preserved by a bijective vertex relabelling. -/
theorem IsCounterexample.pullbackEquiv {V : Type u} {W : Type*} {C : Type v}
    {k : ℕ} {χ : EdgeColoring V C} (hχ : IsCounterexample k χ) (e : W ≃ V) :
    IsCounterexample k (pullbackEquiv χ e) := by
  intro S hS c
  obtain ⟨u, hu, v, hv, huv, hcolor⟩ :=
    hχ (S.map e.toEmbedding) (by simpa using hS) c
  rw [Finset.mem_map] at hu hv
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨v', hv', hv'eq⟩ := hv
  subst v
  have hu'v' : u' ≠ v' := fun h => huv (congrArg e h)
  refine ⟨u', hu', v', hv', hu'v', ?_⟩
  change χ.get (e u') (e v') huv = c
  exact hcolor

/-- Logical bridge between the witness form and nonexistence of a counterexample. -/
theorem upperStatement_iff_no_counterexample (V : Type u) (C : Type v) (k : ℕ) :
    UpperStatement V C k ↔ ¬∃ χ : EdgeColoring V C, IsCounterexample k χ := by
  simp only [UpperStatement, IsCounterexample, SeesEveryColor, ColorAbsent]
  aesop

/-- Exact specialization of the preceding bridge at `(n,r,k) = (26,5,6)`. -/
theorem r5Upper_iff_no_counterexample :
    R5Upper ↔ ¬∃ χ : EdgeColoring (Fin 26) (Fin 5), IsCounterexample 6 χ := by
  exact upperStatement_iff_no_counterexample _ _ _

end Erdos617
