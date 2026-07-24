/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.NeighborhoodAccounting
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Initial degree reduction for the fixed `r = 5` case

This module records the elementary parts surrounding the special Brooks
obligation: a five-colouring on 26 vertices has an independent six-set, and a
graph with at most 65 edges and minimum degree at least five is 5-regular.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

universe u

/-- If `q * k` is smaller than the number of vertices, a `q`-colourable graph
has an independent set of size `k + 1`. -/
theorem not_colorable_of_indepSetFree_of_mul_lt_card
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) {q k : ℕ}
    (hfree : G.IndepSetFree (k + 1))
    (hcard : q * k < Fintype.card V) :
    ¬G.Colorable q := by
  classical
  rintro ⟨C⟩
  obtain ⟨c, hfiber⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card (f := C) (by simpa using hcard)
  let S : Finset V := univ.filter fun x => C x = c
  have hfiber' : k < #S := by
    dsimp [S]
    exact hfiber
  have hlarge : k + 1 ≤ #S := by omega
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hlarge
  apply hfree T
  refine ⟨?_, hTcard⟩
  intro a ha b hb hab
  have haS : a ∈ S := hTS ha
  have hbS : b ∈ S := hTS hb
  have haC : C a = c := (Finset.mem_filter.mp haS).2
  have hbC : C b = c := (Finset.mem_filter.mp hbS).2
  exact (C.isIndepSet_colorClass c) haC hbC hab

/-- A graph on 26 vertices with no independent six-set cannot be
five-colourable. -/
theorem indepSetFree_six_not_colorable_five_fin26
    (G : SimpleGraph (Fin 26))
    (hfree : G.IndepSetFree 6) :
    ¬G.Colorable 5 := by
  apply not_colorable_of_indepSetFree_of_mul_lt_card G
  · simpa using hfree
  · norm_num

/-- Consequently every colour graph of a hypothetical counterexample is not
five-colourable. -/
theorem colorGraph_not_colorable_five_of_counterexample
    (χ : EdgeColoring (Fin 26) (Fin 5)) (hχ : IsCounterexample 6 χ)
    (c : Fin 5) :
    ¬(colorGraph χ c).Colorable 5 :=
  indepSetFree_six_not_colorable_five_fin26 (colorGraph χ c)
    ((isCounterexample_iff_indepSetFree χ 6).mp hχ c)

/-- The local eleven-edge condition rules out a six-clique. -/
theorem admissible_cliqueFree_six
    {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) :
    G.CliqueFree 6 := by
  intro S hclique
  have htop : G.induce (S : Set V) = (⊤ : SimpleGraph (S : Set V)) := by
    apply SimpleGraph.eq_top_iff_forall_ne_adj.mpr
    intro a b hab
    have hval : (a : V) ≠ b := fun h => hab (Subtype.ext h)
    exact hclique.isClique a.property b.property hval
  have hlocal := hG S hclique.card_eq
  have hcardS : Fintype.card (S : Set V) = 6 := by
    simpa using hclique.card_eq
  have hedgeCard : #(G.induce (S : Set V)).edgeFinset =
      #((⊤ : SimpleGraph (S : Set V)).edgeFinset) :=
    congrArg Finset.card (SimpleGraph.edgeFinset_inj.mpr htop)
  rw [hedgeCard, SimpleGraph.card_edgeFinset_top_eq_card_choose_two,
    hcardS] at hlocal
  norm_num [Nat.choose] at hlocal

/-- On 26 vertices, the handshaking identity forces a graph with at most 65
edges and minimum degree at least five to be exactly 5-regular. -/
theorem degree_eq_five_of_card_le_65_of_degree_ge_five
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hedges : #G.edgeFinset ≤ 65)
    (hdegree : ∀ v, 5 ≤ G.degree v) :
    ∀ v, G.degree v = 5 := by
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hconst : (∑ _v : Fin 26, 5) = 130 := by norm_num
  have hsumLower : (∑ _v : Fin 26, 5) ≤ ∑ v, G.degree v := by
    exact Finset.sum_le_sum fun v _ => hdegree v
  have hsumEq : (∑ _v : Fin 26, 5) = ∑ v, G.degree v := by
    rw [hconst, hsum]
    rw [hconst, hsum] at hsumLower
    omega
  have hpoint := (Finset.sum_eq_sum_iff_of_le
    (s := (univ : Finset (Fin 26)))
    (fun v _ => hdegree v)).mp hsumEq
  intro v
  exact (hpoint v (Finset.mem_univ v)).symm

/-- The sparse colour graph supplied by the averaging and Turán layers is
simultaneously nonisolated and non-five-colourable. -/
theorem exists_sparse_nonisolated_nonfiveColorable_colorGraph
    (χ : EdgeColoring (Fin 26) (Fin 5)) (hχ : IsCounterexample 6 χ) :
    ∃ c : Fin 5,
      55 ≤ #(colorGraph χ c).edgeFinset ∧
      #(colorGraph χ c).edgeFinset ≤ 65 ∧
      (∀ v, ¬(colorGraph χ c).IsIsolated v) ∧
      ¬(colorGraph χ c).Colorable 5 := by
  obtain ⟨c, hlower, hupper, hnonisolated⟩ :=
    exists_sparse_nonisolated_colorGraph χ hχ
  exact ⟨c, hlower, hupper, hnonisolated,
    colorGraph_not_colorable_five_of_counterexample χ hχ c⟩

/-- If the sparse colour graph had minimum degree at least five, it would be
5-regular.  This isolates the exact input needed by the special Brooks step. -/
theorem sparse_colorGraph_degree_eq_five_of_degree_ge_five
    (χ : EdgeColoring (Fin 26) (Fin 5)) (c : Fin 5)
    (hedges : #(colorGraph χ c).edgeFinset ≤ 65)
    (hdegree : ∀ v, 5 ≤ (colorGraph χ c).degree v) :
    ∀ v, (colorGraph χ c).degree v = 5 :=
  degree_eq_five_of_card_le_65_of_degree_ge_five
    (colorGraph χ c) hedges hdegree

/-- Exact conditional reduction of the remaining high-minimum-degree case.
The sole mathematical hypothesis is the finite obstruction needed from the
special five-regular Brooks argument: no 26-vertex graph is simultaneously
5-regular, admissible, `CliqueFree 6`, and `IndepSetFree 6`.  No version of
Brooks's theorem is assumed globally. -/
theorem exists_sparse_colorGraph_vertex_degree_le_four_of_special_brooks
    (hbrooks : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj],
      (∀ v, G.degree v = 5) → Admissible G →
        G.CliqueFree 6 → G.IndepSetFree 6 → False)
    (χ : EdgeColoring (Fin 26) (Fin 5)) (hχ : IsCounterexample 6 χ) :
    ∃ c : Fin 5,
      55 ≤ #(colorGraph χ c).edgeFinset ∧
      #(colorGraph χ c).edgeFinset ≤ 65 ∧
      (∀ v, ¬(colorGraph χ c).IsIsolated v) ∧
      ∃ v, (colorGraph χ c).degree v ≤ 4 := by
  obtain ⟨c, hlower, hupper, hnonisolated⟩ :=
    exists_sparse_nonisolated_colorGraph χ hχ
  refine ⟨c, hlower, hupper, hnonisolated, ?_⟩
  by_contra hnone
  have hdegreeGe : ∀ v, 5 ≤ (colorGraph χ c).degree v := by
    intro v
    have hv : ¬(colorGraph χ c).degree v ≤ 4 := by
      intro hle
      exact hnone ⟨v, hle⟩
    omega
  have hregular : ∀ v, (colorGraph χ c).degree v = 5 :=
    sparse_colorGraph_degree_eq_five_of_degree_ge_five χ c hupper hdegreeGe
  have hadmissible : Admissible (colorGraph χ c) :=
    colorGraph_admissible_of_counterexample χ hχ c
  exact hbrooks (colorGraph χ c) hregular hadmissible
    (admissible_cliqueFree_six (colorGraph χ c) hadmissible)
    ((isCounterexample_iff_indepSetFree χ 6).mp hχ c)

end Erdos617
