/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.AlphaFourSmall

/-!
# Edge equalization and the low-degree reduction

This module formalizes the equalization step of the fixed-`r = 5` proof and
the subsequent exclusion of minimum degrees two and three.  The only
remaining external hypothesis is the explicit finite special-Brooks
obstruction isolated in `DegreeReduction`.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

universe u

/-- The exact finite proposition left by the special five-regular Brooks
reduction.  E038 and E042--E045 certificate-check its exhaustive finite
branches; a later bridge must connect those certificates to the kernel. -/
def R5SpecialBrooksObstruction : Prop :=
  ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj],
    (∀ v, G.degree v = 5) → Admissible G →
      G.CliqueFree 6 → G.IndepSetFree 6 → False

/-- Under the finite special-Brooks obstruction, any color graph with at most
65 edges has a genuine minimum-degree vertex of degree two, three, or four. -/
theorem exists_minimal_colorGraph_degree_two_to_four_of_card_le_65
    (hbrooks : R5SpecialBrooksObstruction)
    (χ : EdgeColoring (Fin 26) (Fin 5)) (hχ : IsCounterexample 6 χ)
    (c : Fin 5) (hedges : #(colorGraph χ c).edgeFinset ≤ 65) :
    ∃ v : Fin 26,
      (∀ w, (colorGraph χ c).degree v ≤ (colorGraph χ c).degree w) ∧
      2 ≤ (colorGraph χ c).degree v ∧
      (colorGraph χ c).degree v ≤ 4 := by
  classical
  let G := colorGraph χ c
  have hG : Admissible G := by
    simpa [G] using colorGraph_admissible_of_counterexample χ hχ c
  have hfree : G.IndepSetFree 6 := by
    simpa [G] using (isCounterexample_iff_indepSetFree χ 6).mp hχ c
  have hnonisolated : ∀ w, ¬G.IsIsolated w := by
    intro w
    simpa [G] using
      colorGraph_not_isIsolated_of_card_le_65 χ hχ c hedges w
  have hlow : ∃ a, G.degree a ≤ 4 := by
    by_contra hnone
    have hdegreeGe : ∀ a, 5 ≤ G.degree a := by
      intro a
      by_contra hnot
      have hle : G.degree a ≤ 4 := by omega
      exact hnone ⟨a, hle⟩
    have hregular : ∀ a, G.degree a = 5 :=
      degree_eq_five_of_card_le_65_of_degree_ge_five G
        (by simpa [G] using hedges) hdegreeGe
    exact hbrooks G hregular hG (admissible_cliqueFree_six G hG) hfree
  obtain ⟨a, ha⟩ := hlow
  obtain ⟨v, hmin, _⟩ :=
    exists_minimal_vertex_card_mul_degree_le_twice_edges G
  have hdegreeUpper : G.degree v ≤ 4 := le_trans (hmin a) ha
  have hdegreePositive : 1 ≤ G.degree v := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hzero
    have hvNotSupport : v ∉ G.support :=
      (SimpleGraph.degree_eq_zero_iff_notMem_support G v).mp hzero
    exact hvNotSupport
      (G.mem_support_iff_not_isIsolated.mpr (hnonisolated v))
  have hdegreeNotOne : G.degree v ≠ 1 := by
    intro hdegree
    let U := exteriorFinset G v
    let R := G.induce (U : Set (Fin 26))
    have hUcardRaw := card_exterior_type_add_degree_add_one G v
    have hUcard : Fintype.card (U : Set (Fin 26)) = 24 := by
      rw [hdegree] at hUcardRaw
      norm_num at hUcardRaw
      simpa [U] using hUcardRaw
    have hRadmissible : Admissible R := by
      simpa [R, U] using admissible_induce G hG U
    have hRfree : R.IndepSetFree 5 := by
      simpa [R, U] using
        (indepSetFree_exterior_induce G (k := 5) (by simpa using hfree) v)
    have hRbound :=
      card_edges_ge_sixtyFive_of_admissible_indepSetFree_five_card_twentyFour
        R hRadmissible hRfree hUcard
    have hsplit := exterior_edges_add_degree_add_choose_le_edges G v hmin
    have hsplitR : #R.edgeFinset + G.degree v + (G.degree v).choose 2 ≤
        #G.edgeFinset := by
      simpa [R, U] using hsplit
    rw [hdegree] at hsplitR
    norm_num [Nat.choose] at hsplitR
    have hedgeG : #G.edgeFinset ≤ 65 := by simpa [G] using hedges
    omega
  refine ⟨v, ?_, ?_, ?_⟩
  · simpa [G] using hmin
  · change 2 ≤ G.degree v
    omega
  · simpa [G] using hdegreeUpper

/-- Every color graph at or below the average edge count actually has the
average edge count. -/
theorem colorGraph_card_eq_65_of_card_le_65_of_special_brooks
    (hbrooks : R5SpecialBrooksObstruction)
    (χ : EdgeColoring (Fin 26) (Fin 5)) (hχ : IsCounterexample 6 χ)
    (c : Fin 5) (hedges : #(colorGraph χ c).edgeFinset ≤ 65) :
    #(colorGraph χ c).edgeFinset = 65 := by
  classical
  let G := colorGraph χ c
  have hG : Admissible G := by
    simpa [G] using colorGraph_admissible_of_counterexample χ hχ c
  have hfree : G.IndepSetFree 6 := by
    simpa [G] using (isCounterexample_iff_indepSetFree χ 6).mp hχ c
  obtain ⟨v, hmin, hdegreeLower, hdegreeUpper⟩ :=
    exists_minimal_colorGraph_degree_two_to_four_of_card_le_65
      hbrooks χ hχ c hedges
  by_contra hnot
  have hnotG : ¬#G.edgeFinset = 65 := by simpa [G] using hnot
  have hedgeUpper : #G.edgeFinset ≤ 64 := by
    have : #G.edgeFinset ≤ 65 := by simpa [G] using hedges
    omega
  have hminG : ∀ w, G.degree v ≤ G.degree w := by simpa [G] using hmin
  have hdegreeLowerG : 2 ≤ G.degree v := by simpa [G] using hdegreeLower
  have hdegreeUpperG : G.degree v ≤ 4 := by simpa [G] using hdegreeUpper
  let U := exteriorFinset G v
  let R := G.induce (U : Set (Fin 26))
  have hUcardRaw := card_exterior_type_add_degree_add_one G v
  have hRadmissible : Admissible R := by
    simpa [R, U] using admissible_induce G hG U
  have hRfree : R.IndepSetFree 5 := by
    simpa [R, U] using
      (indepSetFree_exterior_induce G (k := 5) (by simpa using hfree) v)
  have hsplit := exterior_edges_add_degree_add_choose_le_edges G v hminG
  have hsplitR : #R.edgeFinset + G.degree v + (G.degree v).choose 2 ≤
      #G.edgeFinset := by
    simpa [R, U] using hsplit
  interval_cases hdegree : G.degree v
  · have hRcard : Fintype.card (U : Set (Fin 26)) = 23 := by
      norm_num at hUcardRaw
      simpa [U] using hUcardRaw
    have hRbound :=
      card_edges_ge_sixtyTwo_of_admissible_indepSetFree_five_card_twentyThree
        R hRadmissible hRfree hRcard
    norm_num [hdegree, Nat.choose] at hsplitR
    omega
  · have hRcard : Fintype.card (U : Set (Fin 26)) = 22 := by
      norm_num at hUcardRaw
      simpa [U] using hUcardRaw
    have hRbound :=
      card_edges_ge_fiftyNine_of_admissible_indepSetFree_five_card_twentyTwo
        R hRadmissible hRfree hRcard
    norm_num [hdegree, Nat.choose] at hsplitR
    omega
  · have hRcard : Fintype.card (U : Set (Fin 26)) = 21 := by
      norm_num at hUcardRaw
      simpa [U] using hUcardRaw
    have hRbound :=
      card_edges_ge_fiftyFive_of_admissible_indepSetFree_five_card_twentyOne
        R hRadmissible hRfree hRcard
    norm_num [hdegree, Nat.choose] at hsplitR
    omega

/-- Conditional edge equalization: every color class has exactly 65 edges. -/
theorem all_colorGraph_card_eq_65_of_special_brooks
    (hbrooks : R5SpecialBrooksObstruction)
    (χ : EdgeColoring (Fin 26) (Fin 5)) (hχ : IsCounterexample 6 χ) :
    ∀ c : Fin 5, #(colorGraph χ c).edgeFinset = 65 := by
  classical
  have hge : ∀ c : Fin 5, 65 ≤ #(colorGraph χ c).edgeFinset := by
    intro c
    by_contra hnot
    have hle : #(colorGraph χ c).edgeFinset ≤ 65 := by omega
    have heq := colorGraph_card_eq_65_of_card_le_65_of_special_brooks
      hbrooks χ hχ c hle
    omega
  have hsum := sum_card_colorGraph_edgeFinset χ
  have hsumEq : (∑ _c : Fin 5, 65) =
      ∑ c : Fin 5, #(colorGraph χ c).edgeFinset := by
    rw [hsum]
    norm_num [Nat.choose]
  have hpoint := (Finset.sum_eq_sum_iff_of_le
    (s := (univ : Finset (Fin 5)))
    (fun c _ => hge c)).mp hsumEq
  intro c
  exact (hpoint c (Finset.mem_univ c)).symm

/-- If a finite set is an isolated clique, every vertex in its complement
retains its ambient degree in the induced complementary graph. -/
theorem degree_induce_finset_compl_eq_of_isIsolatedCliqueOn
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    [Fintype (Sᶜ : Finset V)]
    (hS : IsIsolatedCliqueOn G S) (u : (Sᶜ : Finset V)) :
    (G.induce ((Sᶜ : Finset V) : Set V)).degree u = G.degree u := by
  classical
  let U : Finset V := Sᶜ
  let H := G.induce (U : Set V)
  have huNotS : (u : V) ∉ S := Finset.mem_compl.mp u.property
  have hneighborIn (w : V) (huw : G.Adj u w) : w ∈ U := by
    change w ∈ Sᶜ
    rw [Finset.mem_compl]
    intro hwS
    exact (hS.2 hwS huNotS) huw.symm
  let e : H.neighborSet u ≃ G.neighborSet (u : V) := {
    toFun := fun w => ⟨w.1.1, by
      have hw : H.Adj u w.1 := w.2
      change G.Adj (u : V) (w.1 : V) at hw
      exact hw⟩
    invFun := fun w => ⟨⟨w.1, hneighborIn w.1 w.2⟩, by
      change G.Adj (u : V) w.1
      exact w.2⟩
    left_inv := by
      intro w
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv := by
      intro w
      apply Subtype.ext
      rfl
  }
  have hcard := Fintype.card_congr e
  rw [SimpleGraph.card_neighborSet_eq_degree,
    SimpleGraph.card_neighborSet_eq_degree] at hcard
  simpa [H, U] using hcard

/-- Specialization of degree inheritance to the exterior of a vertex whose
closed neighborhood is an isolated clique. -/
theorem degree_induce_exterior_eq_of_isolatedClosedNeighborhood
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    [Fintype (exteriorFinset G v : Set V)]
    (hS : IsIsolatedCliqueOn G (insert v (G.neighborFinset v)))
    (u : (exteriorFinset G v : Set V)) :
    (G.induce (exteriorFinset G v : Set V)).degree u = G.degree u := by
  classical
  let U := exteriorFinset G v
  let H := G.induce (U : Set V)
  have huMem : (u : V) ∈ (insert v (G.neighborFinset v))ᶜ := u.property
  have huNot : (u : V) ∉ insert v (G.neighborFinset v) :=
    Finset.mem_compl.mp huMem
  have hneighborIn (w : V) (huw : G.Adj u w) : w ∈ U := by
    change w ∈ (insert v (G.neighborFinset v))ᶜ
    rw [Finset.mem_compl]
    intro hwS
    exact (hS.2 hwS huNot) huw.symm
  let e : H.neighborSet u ≃ G.neighborSet (u : V) := {
    toFun := fun w => ⟨w.1.1, by
      have hw : H.Adj u w.1 := w.2
      change G.Adj (u : V) (w.1 : V) at hw
      exact hw⟩
    invFun := fun w => ⟨⟨w.1, hneighborIn w.1 w.2⟩, by
      change G.Adj (u : V) w.1
      exact w.2⟩
    left_inv := by
      intro w
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv := by
      intro w
      apply Subtype.ext
      rfl
  }
  have hcard := Fintype.card_congr e
  rw [SimpleGraph.card_neighborSet_eq_degree,
    SimpleGraph.card_neighborSet_eq_degree] at hcard
  simpa [H, U] using hcard

/-- The exact 65-edge setting cannot have minimum degree two.  The proof
peels the forced isolated `K3`, then the forced isolated `K4`, and terminates
with the large independence-two bound. -/
theorem false_of_admissible_indepSetFree_six_card_twentySix_edges_sixtyFive_minDegree_two
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 6)
    (hcard : Fintype.card V = 26) (hedges : #G.edgeFinset = 65)
    (v : V) (hmin : ∀ w, G.degree v ≤ G.degree w)
    (hdegree : G.degree v = 2) : False := by
  classical
  let U := exteriorFinset G v
  let H := G.induce (U : Set V)
  have hUcardRaw := card_exterior_type_add_degree_add_one G v
  have hUcard : Fintype.card (U : Set V) = 23 := by
    rw [hcard, hdegree] at hUcardRaw
    norm_num at hUcardRaw
    simpa [U] using hUcardRaw
  have hHadmissible : Admissible H := by
    simpa [H, U] using admissible_induce G hG U
  have hHfree : H.IndepSetFree 5 := by
    simpa [H, U] using
      (indepSetFree_exterior_induce G (k := 5) (by simpa using hfree) v)
  have hHlower :=
    card_edges_ge_sixtyTwo_of_admissible_indepSetFree_five_card_twentyThree
      H hHadmissible hHfree hUcard
  have hexact := card_edges_eq_exterior_add_degree_add_accounting G v
  have hexactH : #H.edgeFinset + G.degree v +
      (neighborhoodCrossEdgeCount G v +
        neighborhoodInternalEdgeCount G v) = #G.edgeFinset := by
    simpa [H, U] using hexact
  have haccountLower :=
    neighborhood_cross_add_internal_ge_choose_degree G v hmin
  have hHedges : #H.edgeFinset = 62 := by
    rw [hdegree, hedges] at hexactH
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
  have hHdegreeLower : ∀ w : (U : Set V), 2 ≤ H.degree w := by
    intro w
    have heq : H.degree w = G.degree w := by
      simpa [H, U] using
        degree_induce_exterior_eq_of_isolatedClosedNeighborhood G v
          hisolated w
    rw [heq, ← hdegree]
    exact hmin w
  letI : Nonempty (U : Set V) := Fintype.card_pos_iff.mp (by
    rw [hUcard]
    norm_num)
  obtain ⟨w, hHmin, hHavg⟩ :=
    exists_minimal_vertex_card_mul_degree_le_twice_edges H
  have hHdegreeLowerW : 2 ≤ H.degree w := hHdegreeLower w
  have hHdegreeUpperW : H.degree w ≤ 5 := by
    rw [hUcard, hHedges] at hHavg
    omega
  let U2 := exteriorFinset H w
  let Q := H.induce (U2 : Set (U : Set V))
  have hU2cardRaw := card_exterior_type_add_degree_add_one H w
  have hQadmissible : Admissible Q := by
    simpa [Q, U2] using admissible_induce H hHadmissible U2
  have hQfree : Q.IndepSetFree 4 := by
    simpa [Q, U2] using
      (indepSetFree_exterior_induce H (k := 4) (by simpa using hHfree) w)
  have hsplitH := exterior_edges_add_degree_add_choose_le_edges H w hHmin
  have hsplitHQ : #Q.edgeFinset + H.degree w + (H.degree w).choose 2 ≤
      #H.edgeFinset := by
    simpa [Q, U2] using hsplitH
  interval_cases hdegreeW : H.degree w
  · have hQcard : Fintype.card (U2 : Set (U : Set V)) = 20 := by
      rw [hUcard] at hU2cardRaw
      norm_num at hU2cardRaw
      simpa [U2] using hU2cardRaw
    have hQbound :=
      card_edges_ge_sixtyTwo_of_admissible_indepSetFree_four_card_twenty
        Q hQadmissible hQfree hQcard
    rw [hHedges] at hsplitHQ
    norm_num [hdegreeW, Nat.choose] at hsplitHQ
    omega
  · have hQcard : Fintype.card (U2 : Set (U : Set V)) = 19 := by
      rw [hUcard] at hU2cardRaw
      norm_num at hU2cardRaw
      simpa [U2] using hU2cardRaw
    have hQbound :=
      card_edges_ge_fiftySix_of_admissible_indepSetFree_four_card_nineteen
        Q hQadmissible hQfree hQcard
    have hexactH' := card_edges_eq_exterior_add_degree_add_accounting H w
    have hexactHQ : #Q.edgeFinset + H.degree w +
        (neighborhoodCrossEdgeCount H w +
          neighborhoodInternalEdgeCount H w) = #H.edgeFinset := by
      simpa [Q, U2] using hexactH'
    have hHminW : ∀ x, H.degree w ≤ H.degree x := by
      intro x
      rw [hdegreeW]
      exact hHmin x
    have haccountLowerH :=
      neighborhood_cross_add_internal_ge_choose_degree H w hHminW
    have hQedges : #Q.edgeFinset = 56 := by
      rw [hdegreeW, hHedges] at hexactHQ
      rw [hdegreeW] at haccountLowerH
      norm_num [Nat.choose] at haccountLowerH
      omega
    have haccountEqH : neighborhoodCrossEdgeCount H w +
        neighborhoodInternalEdgeCount H w = (H.degree w).choose 2 := by
      rw [hdegreeW]
      norm_num [Nat.choose]
      omega
    have hisolatedH :=
      neighborhood_accounting_equality_isolatedClique H w hHminW haccountEqH
    have hQdegreeLower : ∀ z : (U2 : Set (U : Set V)), 3 ≤ Q.degree z := by
      intro z
      have heq : Q.degree z = H.degree z := by
        simpa [Q, U2] using
          degree_induce_exterior_eq_of_isolatedClosedNeighborhood H w
            hisolatedH z
      rw [heq, ← hdegreeW]
      exact hHminW z
    letI : Nonempty (U2 : Set (U : Set V)) := Fintype.card_pos_iff.mp (by
      rw [hQcard]
      norm_num)
    obtain ⟨z, hQmin, hQavg⟩ :=
      exists_minimal_vertex_card_mul_degree_le_twice_edges Q
    have hQdegreeLowerZ : 3 ≤ Q.degree z := hQdegreeLower z
    have hQdegreeUpperZ : Q.degree z ≤ 5 := by
      rw [hQcard, hQedges] at hQavg
      omega
    let U3 := exteriorFinset Q z
    let P := Q.induce (U3 : Set (U2 : Set (U : Set V)))
    have hU3cardRaw := card_exterior_type_add_degree_add_one Q z
    have hPadmissible : Admissible P := by
      simpa [P, U3] using admissible_induce Q hQadmissible U3
    have hPfree : P.IndepSetFree 3 := by
      simpa [P, U3] using
        (indepSetFree_exterior_induce Q (k := 3) (by simpa using hQfree) z)
    have hsplitQ := exterior_edges_add_degree_add_choose_le_edges Q z hQmin
    have hsplitQP : #P.edgeFinset + Q.degree z + (Q.degree z).choose 2 ≤
        #Q.edgeFinset := by
      simpa [P, U3] using hsplitQ
    interval_cases hdegreeZ : Q.degree z
    · have hPcard : Fintype.card (U3 : Set (U2 : Set (U : Set V))) = 15 := by
        rw [hQcard] at hU3cardRaw
        norm_num at hU3cardRaw
        simpa [U3] using hU3cardRaw
      have hPbound :=
        choose_card_le_edges_add_twice_card_of_admissible_indepSetFree_three
          P hPadmissible hPfree (by rw [hPcard]; norm_num)
      rw [hPcard] at hPbound
      norm_num [Nat.choose] at hPbound
      rw [hQedges] at hsplitQP
      norm_num [hdegreeZ, Nat.choose] at hsplitQP
      omega
    · have hPcard : Fintype.card (U3 : Set (U2 : Set (U : Set V))) = 14 := by
        rw [hQcard] at hU3cardRaw
        norm_num at hU3cardRaw
        simpa [U3] using hU3cardRaw
      have hPbound :=
        choose_card_le_edges_add_twice_card_of_admissible_indepSetFree_three
          P hPadmissible hPfree (by rw [hPcard]; norm_num)
      rw [hPcard] at hPbound
      norm_num [Nat.choose] at hPbound
      rw [hQedges] at hsplitQP
      norm_num [hdegreeZ, Nat.choose] at hsplitQP
      omega
    · have hPcard : Fintype.card (U3 : Set (U2 : Set (U : Set V))) = 13 := by
        rw [hQcard] at hU3cardRaw
        norm_num at hU3cardRaw
        simpa [U3] using hU3cardRaw
      have hPbound :=
        choose_card_le_edges_add_twice_card_of_admissible_indepSetFree_three
          P hPadmissible hPfree (by rw [hPcard]; norm_num)
      rw [hPcard] at hPbound
      norm_num [Nat.choose] at hPbound
      have hstrong :=
        exterior_edges_add_nineteen_le_edges_of_admissible_degree_five
          Q hQadmissible z hdegreeZ (by
            intro x
            rw [hdegreeZ]
            exact hQmin x)
      have hstrongP : #P.edgeFinset + 19 ≤ #Q.edgeFinset := by
        simpa [P, U3] using hstrong
      rw [hQedges] at hstrongP
      omega
  · have hQcard : Fintype.card (U2 : Set (U : Set V)) = 18 := by
      rw [hUcard] at hU2cardRaw
      norm_num at hU2cardRaw
      simpa [U2] using hU2cardRaw
    have hQbound :=
      card_edges_ge_fiftyFour_of_admissible_indepSetFree_four_card_eighteen
        Q hQadmissible hQfree hQcard
    rw [hHedges] at hsplitHQ
    norm_num [hdegreeW, Nat.choose] at hsplitHQ
    omega
  · have hQcard : Fintype.card (U2 : Set (U : Set V)) = 17 := by
      rw [hUcard] at hU2cardRaw
      norm_num at hU2cardRaw
      simpa [U2] using hU2cardRaw
    have hQbound :=
      card_edges_ge_fifty_of_admissible_indepSetFree_four_card_seventeen
        Q hQadmissible hQfree hQcard
    have hstrong :=
      exterior_edges_add_nineteen_le_edges_of_admissible_degree_five
        H hHadmissible w hdegreeW (by
          intro x
          rw [hdegreeW]
          exact hHmin x)
    have hstrongQ : #Q.edgeFinset + 19 ≤ #H.edgeFinset := by
      simpa [Q, U2] using hstrong
    rw [hHedges] at hstrongQ
    omega

/-- The exact 65-edge setting cannot have minimum degree three.  Equality
would isolate a `K4`; every possible new minimum degree in the order-22
residual violates the small independence-three bounds. -/
theorem false_of_admissible_indepSetFree_six_card_twentySix_edges_sixtyFive_minDegree_three
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 6)
    (hcard : Fintype.card V = 26) (hedges : #G.edgeFinset = 65)
    (v : V) (hmin : ∀ w, G.degree v ≤ G.degree w)
    (hdegree : G.degree v = 3) : False := by
  classical
  let U := exteriorFinset G v
  let H := G.induce (U : Set V)
  have hUcardRaw := card_exterior_type_add_degree_add_one G v
  have hUcard : Fintype.card (U : Set V) = 22 := by
    rw [hcard, hdegree] at hUcardRaw
    norm_num at hUcardRaw
    simpa [U] using hUcardRaw
  have hHadmissible : Admissible H := by
    simpa [H, U] using admissible_induce G hG U
  have hHfree : H.IndepSetFree 5 := by
    simpa [H, U] using
      (indepSetFree_exterior_induce G (k := 5) (by simpa using hfree) v)
  have hHlower :=
    card_edges_ge_fiftyNine_of_admissible_indepSetFree_five_card_twentyTwo
      H hHadmissible hHfree hUcard
  have hexact := card_edges_eq_exterior_add_degree_add_accounting G v
  have hexactH : #H.edgeFinset + G.degree v +
      (neighborhoodCrossEdgeCount G v +
        neighborhoodInternalEdgeCount G v) = #G.edgeFinset := by
    simpa [H, U] using hexact
  have haccountLower :=
    neighborhood_cross_add_internal_ge_choose_degree G v hmin
  have hHedges : #H.edgeFinset = 59 := by
    rw [hdegree, hedges] at hexactH
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
  have hHdegreeLower : ∀ w : (U : Set V), 3 ≤ H.degree w := by
    intro w
    have heq : H.degree w = G.degree w := by
      simpa [H, U] using
        degree_induce_exterior_eq_of_isolatedClosedNeighborhood G v
          hisolated w
    rw [heq, ← hdegree]
    exact hmin w
  letI : Nonempty (U : Set V) := Fintype.card_pos_iff.mp (by
    rw [hUcard]
    norm_num)
  obtain ⟨w, hHmin, hHavg⟩ :=
    exists_minimal_vertex_card_mul_degree_le_twice_edges H
  have hHdegreeLowerW : 3 ≤ H.degree w := hHdegreeLower w
  have hHdegreeUpperW : H.degree w ≤ 5 := by
    rw [hUcard, hHedges] at hHavg
    omega
  let U2 := exteriorFinset H w
  let Q := H.induce (U2 : Set (U : Set V))
  have hU2cardRaw := card_exterior_type_add_degree_add_one H w
  have hQadmissible : Admissible Q := by
    simpa [Q, U2] using admissible_induce H hHadmissible U2
  have hQfree : Q.IndepSetFree 4 := by
    simpa [Q, U2] using
      (indepSetFree_exterior_induce H (k := 4) (by simpa using hHfree) w)
  have hsplitH := exterior_edges_add_degree_add_choose_le_edges H w hHmin
  have hsplitHQ : #Q.edgeFinset + H.degree w + (H.degree w).choose 2 ≤
      #H.edgeFinset := by
    simpa [Q, U2] using hsplitH
  interval_cases hdegreeW : H.degree w
  · have hQcard : Fintype.card (U2 : Set (U : Set V)) = 18 := by
      rw [hUcard] at hU2cardRaw
      norm_num at hU2cardRaw
      simpa [U2] using hU2cardRaw
    have hQbound :=
      card_edges_ge_fiftyFour_of_admissible_indepSetFree_four_card_eighteen
        Q hQadmissible hQfree hQcard
    rw [hHedges] at hsplitHQ
    norm_num [hdegreeW, Nat.choose] at hsplitHQ
    omega
  · have hQcard : Fintype.card (U2 : Set (U : Set V)) = 17 := by
      rw [hUcard] at hU2cardRaw
      norm_num at hU2cardRaw
      simpa [U2] using hU2cardRaw
    have hQbound :=
      card_edges_ge_fifty_of_admissible_indepSetFree_four_card_seventeen
        Q hQadmissible hQfree hQcard
    rw [hHedges] at hsplitHQ
    norm_num [hdegreeW, Nat.choose] at hsplitHQ
    omega
  · have hQcard : Fintype.card (U2 : Set (U : Set V)) = 16 := by
      rw [hUcard] at hU2cardRaw
      norm_num at hU2cardRaw
      simpa [U2] using hU2cardRaw
    have hQbound :=
      card_edges_ge_fortyFive_of_admissible_indepSetFree_four_card_sixteen
        Q hQadmissible hQfree hQcard
    have hstrong :=
      exterior_edges_add_nineteen_le_edges_of_admissible_degree_five
        H hHadmissible w hdegreeW (by
          intro x
          rw [hdegreeW]
          exact hHmin x)
    have hstrongQ : #Q.edgeFinset + 19 ≤ #H.edgeFinset := by
      simpa [Q, U2] using hstrong
    rw [hHedges] at hstrongQ
    omega

/-- After equalization, every color graph has minimum degree exactly four. -/
theorem exists_minimal_colorGraph_degree_four_of_special_brooks
    (hbrooks : R5SpecialBrooksObstruction)
    (χ : EdgeColoring (Fin 26) (Fin 5)) (hχ : IsCounterexample 6 χ)
    (c : Fin 5) :
    ∃ v : Fin 26,
      (∀ w, (colorGraph χ c).degree v ≤ (colorGraph χ c).degree w) ∧
      (colorGraph χ c).degree v = 4 := by
  classical
  let G := colorGraph χ c
  have hedges : #G.edgeFinset = 65 := by
    simpa [G] using all_colorGraph_card_eq_65_of_special_brooks
      hbrooks χ hχ c
  have hG : Admissible G := by
    simpa [G] using colorGraph_admissible_of_counterexample χ hχ c
  have hfree : G.IndepSetFree 6 := by
    simpa [G] using (isCounterexample_iff_indepSetFree χ 6).mp hχ c
  obtain ⟨v, hmin, hdegreeLower, hdegreeUpper⟩ :=
    exists_minimal_colorGraph_degree_two_to_four_of_card_le_65
      hbrooks χ hχ c (by simp [G, hedges])
  have hminG : ∀ w, G.degree v ≤ G.degree w := by simpa [G] using hmin
  have hdegreeLowerG : 2 ≤ G.degree v := by simpa [G] using hdegreeLower
  have hdegreeUpperG : G.degree v ≤ 4 := by simpa [G] using hdegreeUpper
  interval_cases hdegree : G.degree v
  · have hminCase : ∀ w, G.degree v ≤ G.degree w := by
      intro w
      rw [hdegree]
      exact hminG w
    exact (false_of_admissible_indepSetFree_six_card_twentySix_edges_sixtyFive_minDegree_two
      G hG hfree (by norm_num) hedges v hminCase hdegree).elim
  · have hminCase : ∀ w, G.degree v ≤ G.degree w := by
      intro w
      rw [hdegree]
      exact hminG w
    exact (false_of_admissible_indepSetFree_six_card_twentySix_edges_sixtyFive_minDegree_three
      G hG hfree (by norm_num) hedges v hminCase hdegree).elim
  · have hminCase : ∀ w, G.degree v ≤ G.degree w := by
      intro w
      rw [hdegree]
      exact hminG w
    exact ⟨v, by simpa [G] using hminCase, by simpa [G] using hdegree⟩

/-- The exact residual structure reached after equalization and low-degree
exclusion. -/
def R5ColorGraphResidualStructure (G : SimpleGraph (Fin 26))
    [DecidableRel G.Adj] : Prop :=
  ∃ v : Fin 26,
    (∀ w, G.degree v ≤ G.degree w) ∧
    G.degree v = 4 ∧
    IsIsolatedCliqueOn G (insert v (G.neighborFinset v)) ∧
    Fintype.card (exteriorFinset G v : Set (Fin 26)) = 21 ∧
    #(G.induce (exteriorFinset G v : Set (Fin 26))).edgeFinset = 55 ∧
    Admissible (G.induce (exteriorFinset G v : Set (Fin 26))) ∧
    (G.induce (exteriorFinset G v : Set (Fin 26))).IndepSetFree 5 ∧
    ∀ u : (exteriorFinset G v : Set (Fin 26)),
      4 ≤ (G.induce (exteriorFinset G v : Set (Fin 26))).degree u

/-- Every color graph in a hypothetical counterexample reaches an isolated
`K5` plus an exact 21-vertex, 55-edge residual of minimum degree at least
four. -/
theorem colorGraph_residualStructure_of_special_brooks
    (hbrooks : R5SpecialBrooksObstruction)
    (χ : EdgeColoring (Fin 26) (Fin 5)) (hχ : IsCounterexample 6 χ)
    (c : Fin 5) :
    R5ColorGraphResidualStructure (colorGraph χ c) := by
  classical
  let G := colorGraph χ c
  have hedges : #G.edgeFinset = 65 := by
    simpa [G] using all_colorGraph_card_eq_65_of_special_brooks
      hbrooks χ hχ c
  have hG : Admissible G := by
    simpa [G] using colorGraph_admissible_of_counterexample χ hχ c
  have hfree : G.IndepSetFree 6 := by
    simpa [G] using (isCounterexample_iff_indepSetFree χ 6).mp hχ c
  obtain ⟨v, hmin, hdegree⟩ :=
    exists_minimal_colorGraph_degree_four_of_special_brooks
      hbrooks χ hχ c
  have hminG : ∀ w, G.degree v ≤ G.degree w := by simpa [G] using hmin
  have hdegreeG : G.degree v = 4 := by simpa [G] using hdegree
  let U := exteriorFinset G v
  let H := G.induce (U : Set (Fin 26))
  have hUcardRaw := card_exterior_type_add_degree_add_one G v
  have hUcard : Fintype.card (U : Set (Fin 26)) = 21 := by
    rw [hdegreeG] at hUcardRaw
    norm_num at hUcardRaw
    simpa [U] using hUcardRaw
  have hHadmissible : Admissible H := by
    simpa [H, U] using admissible_induce G hG U
  have hHfree : H.IndepSetFree 5 := by
    simpa [H, U] using
      (indepSetFree_exterior_induce G (k := 5) (by simpa using hfree) v)
  have hHlower :=
    card_edges_ge_fiftyFive_of_admissible_indepSetFree_five_card_twentyOne
      H hHadmissible hHfree hUcard
  have hexact := card_edges_eq_exterior_add_degree_add_accounting G v
  have hexactH : #H.edgeFinset + G.degree v +
      (neighborhoodCrossEdgeCount G v +
        neighborhoodInternalEdgeCount G v) = #G.edgeFinset := by
    simpa [H, U] using hexact
  have haccountLower :=
    neighborhood_cross_add_internal_ge_choose_degree G v hminG
  have hHedges : #H.edgeFinset = 55 := by
    rw [hdegreeG, hedges] at hexactH
    rw [hdegreeG] at haccountLower
    norm_num [Nat.choose] at haccountLower
    omega
  have haccountEq : neighborhoodCrossEdgeCount G v +
      neighborhoodInternalEdgeCount G v = (G.degree v).choose 2 := by
    rw [hdegreeG]
    norm_num [Nat.choose]
    omega
  have hisolated :=
    neighborhood_accounting_equality_isolatedClique G v hminG haccountEq
  have hHdegreeLower : ∀ u : (U : Set (Fin 26)), 4 ≤ H.degree u := by
    intro u
    have heq : H.degree u = G.degree u := by
      simpa [H, U] using
        degree_induce_exterior_eq_of_isolatedClosedNeighborhood G v
          hisolated u
    rw [heq, ← hdegreeG]
    exact hminG u
  change R5ColorGraphResidualStructure G
  refine ⟨v, hminG, hdegreeG, hisolated, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [U] using hUcard
  · simpa [H, U] using hHedges
  · simpa [H, U] using hHadmissible
  · simpa [H, U] using hHfree
  · simpa [H, U] using hHdegreeLower

end Erdos617
