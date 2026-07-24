/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.AlphaPropagation
public import Mathlib.Tactic.IntervalCases

/-!
# The admissible order-eleven independence-two endpoint

This module proves the small terminal estimate used at order eleven in the
fixed-`r = 5` argument.  The proof is direct: it excludes complementary degree
five, forces exact two-element neighborhood labels around a degree-four
vertex, and replaces the manuscript's path-and-cycle classification by a
finite label-collision lemma.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

theorem six_cross_values_eq_two
    {β : Type*} [Fintype β]
    (H : SimpleGraph β) [DecidableRel H.Adj] (p : β → ℕ)
    (hcard : Fintype.card β = 6)
    (hsum : (∑ i, p i) ≤ 12)
    (hpair : ∀ i j, i ≠ j →
      4 ≤ p i + p j + if H.Adj i j then 1 else 0)
    (hdegree : ∀ i, p i + H.degree i ≤ 4) :
    ∀ i, p i = 2 := by
  classical
  have hallLower (i : β) : 2 ≤ p i := by
    let R : Finset β := Finset.univ.erase i
    have hRcard : #R = 5 := by
      dsimp [R]
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, hcard]
    have hpairSum :
        (∑ _j ∈ R, 4) ≤
          ∑ j ∈ R, (p i + p j + if H.Adj i j then 1 else 0) := by
      exact Finset.sum_le_sum fun j hj =>
        hpair i j (Ne.symm (by simpa [R] using hj))
    have hadjSum :
        (∑ j ∈ R, if H.Adj i j then 1 else 0) = H.degree i := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      calc
        (∑ j ∈ R, if H.Adj i j then 1 else 0) =
            #((R.filter fun j => H.Adj i j)) := by simp
        _ = #(H.neighborFinset i) := by
          congr 1
          ext j
          simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
          exact ⟨And.right, fun hij => ⟨by simp [R, hij.ne.symm], hij⟩⟩
    have hpSplit : p i + ∑ j ∈ R, p j = ∑ j, p j := by
      simpa [R] using
        (Finset.add_sum_erase Finset.univ p (Finset.mem_univ i))
    simp only [Finset.sum_add_distrib] at hpairSum
    have hfourSum : (∑ _j ∈ R, 4) = 20 := by simp [hRcard]
    have hpiSum : (∑ _j ∈ R, p i) = 5 * p i := by
      simp [hRcard, Nat.mul_comm]
    rw [hfourSum, hpiSum, hadjSum] at hpairSum
    have hiDegree := hdegree i
    by_contra hnot
    have hpiUpper : p i ≤ 1 := by omega
    have hsumPart : p i + ∑ j ∈ R, p j ≤ 12 := by
      rw [hpSplit]
      exact hsum
    have hupper :
        3 * p i + (p i + ∑ j ∈ R, p j) +
          (p i + H.degree i) ≤ 19 := by omega
    omega
  have htotalLower : (∑ _j : β, 2) ≤ ∑ j, p j :=
    Finset.sum_le_sum fun j _ => hallLower j
  have hconst : (∑ _j : β, 2) = 12 := by simp [hcard]
  rw [hconst] at htotalLower
  intro i
  have hiLower := hallLower i
  let R : Finset β := Finset.univ.erase i
  have hRcard : #R = 5 := by
    dsimp [R]
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, hcard]
  have hrestLower : (∑ _j ∈ R, 2) ≤ ∑ j ∈ R, p j :=
    Finset.sum_le_sum fun j _ => hallLower j
  have hrestConst : (∑ _j ∈ R, 2) = 10 := by simp [hRcard]
  rw [hrestConst] at hrestLower
  have hpSplit : p i + ∑ j ∈ R, p j = ∑ j, p j := by
    simpa [R] using
      (Finset.add_sum_erase Finset.univ p (Finset.mem_univ i))
  omega

theorem eq_sdiff_of_subset_card_two_disjoint
    {α : Type*} [DecidableEq α] {A Q R : Finset α}
    (hA : #A = 4) (hQsub : Q ⊆ A) (hQ : #Q = 2)
    (hRsub : R ⊆ A) (hR : #R = 2) (hdis : Disjoint Q R) :
    R = A \ Q := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hxR
    exact Finset.mem_sdiff.mpr
      ⟨hRsub hxR, fun hxQ => (Finset.disjoint_left.mp hdis) hxQ hxR⟩
  · rw [Finset.card_sdiff_of_subset hQsub, hA, hQ, hR]

theorem exists_equal_label_pair_and_third
    {α β : Type*} [Fintype β] [DecidableEq α]
    (A : Finset α) (q : β → Finset α)
    (hβ : Fintype.card β = 6) (hA : #A = 4)
    (hqsub : ∀ b, q b ⊆ A) (hqcard : ∀ b, #(q b) = 2)
    (hnotinj : ¬ Function.Injective q) :
    ∃ x y z, x ≠ y ∧ z ≠ x ∧ z ≠ y ∧
      q x = q y ∧ q z ≠ A \ q x := by
  classical
  simp only [Function.Injective] at hnotinj
  push Not at hnotinj
  obtain ⟨x, y, hlabel, hxy⟩ := hnotinj
  let R : Finset β := (Finset.univ.erase x).erase y
  have hRcard : #R = 4 := by
    dsimp [R]
    rw [Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_univ y⟩),
      Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, hβ]
  by_cases hz : ∃ z ∈ R, q z ≠ A \ q x
  · obtain ⟨z, hzR, hzlabel⟩ := hz
    have hzy : z ≠ y := (Finset.mem_erase.mp hzR).1
    have hzx : z ≠ x :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hzR).2).1
    exact ⟨x, y, z, hxy, hzx, hzy, hlabel, hzlabel⟩
  · push Not at hz
    have hRlarge : 2 < #R := by omega
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
      Finset.two_lt_card_iff.mp hRlarge
    have haLabel := hz a ha
    have hbLabel := hz b hb
    have hcLabel := hz c hc
    let P : Finset α := A \ q x
    have hPcard : #P = 2 := by
      dsimp [P]
      rw [Finset.card_sdiff_of_subset (hqsub x), hA, hqcard]
    have hPne : P ≠ A \ P := by
      intro heq
      have hPpos : 0 < #P := by omega
      obtain ⟨t, htP⟩ := Finset.card_pos.mp hPpos
      have htDiff : t ∈ A \ P := heq ▸ htP
      exact (Finset.mem_sdiff.mp htDiff).2 htP
    refine ⟨a, b, c, hab, hac.symm, hbc.symm, ?_, ?_⟩
    · simpa [P] using haLabel.trans hbLabel.symm
    · rw [haLabel, hcLabel]
      exact hPne

theorem labels_not_injective_of_six_vertices_four_edges
    {α β : Type*} [Fintype β]
    (H : SimpleGraph β) [DecidableRel H.Adj]
    (A : Finset α) (q : β → Finset α)
    (hβ : Fintype.card β = 6) (hA : #A = 4)
    (hqsub : ∀ b, q b ⊆ A) (hqcard : ∀ b, #(q b) = 2)
    (hadjDisjoint : ∀ {x y}, H.Adj x y → Disjoint (q x) (q y))
    (hedges : 4 ≤ #H.edgeFinset) :
    ¬Function.Injective q := by
  classical
  intro hinj
  have hdegreeOne (x : β) : H.degree x ≤ 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      Finset.card_le_one]
    intro y hy z hz
    have hxy : H.Adj x y := by simpa using hy
    have hxz : H.Adj x z := by simpa using hz
    have hyLabel := eq_sdiff_of_subset_card_two_disjoint
      hA (hqsub x) (hqcard x) (hqsub y) (hqcard y)
        (hadjDisjoint hxy)
    have hzLabel := eq_sdiff_of_subset_card_two_disjoint
      hA (hqsub x) (hqcard x) (hqsub z) (hqcard z)
        (hadjDisjoint hxz)
    exact hinj (hyLabel.trans hzLabel.symm)
  have hsumUpper : (∑ x, H.degree x) ≤ ∑ _x : β, 1 :=
    Finset.sum_le_sum fun x _ => hdegreeOne x
  rw [H.sum_degrees_eq_twice_card_edges] at hsumUpper
  simp [hβ] at hsumUpper
  omega

theorem card_induce_pair_add_between_degrees_of_independent
    {V : Type*} [Fintype V] [DecidableEq V]
    (L : SimpleGraph V) [DecidableRel L.Adj]
    (A B : Finset V) (x y : V) (hxB : x ∈ B) (hyB : y ∈ B)
    (hxy : x ≠ y) (hdis : Disjoint A B)
    (hA : L.IsIndepSet (A : Set V)) :
    #(L.induce ((insert x (insert y A) : Finset V) : Set V)).edgeFinset =
      (L.between (A : Set V) (B : Set V)).degree x +
        (L.between (A : Set V) (B : Set V)).degree y +
          (if L.Adj x y then 1 else 0) := by
  classical
  let T : Finset V := {x, y}
  let S : Finset V := insert x (insert y A)
  let D := L.between (A : Set V) (T : Set V)
  let E := L.between (T : Set V) (T : Set V)
  let J := L.between (S : Set V) (S : Set V)
  let C := L.between (A : Set V) (B : Set V)
  have hxNotA : x ∉ A := fun hxA =>
    (Finset.disjoint_left.mp hdis) hxA hxB
  have hyNotA : y ∉ A := fun hyA =>
    (Finset.disjoint_left.mp hdis) hyA hyB
  have hTsub : T ⊆ B := by
    intro z hz
    have hz' : z = x ∨ z = y := by simpa [T] using hz
    rcases hz' with rfl | rfl
    · exact hxB
    · exact hyB
  have hAT : Disjoint A T := hdis.mono_right hTsub
  have hAtoS : A ⊆ S := by
    intro z hz
    simp [S, hz]
  have hTtoS : T ⊆ S := by
    intro z hz
    have hz' : z = x ∨ z = y := by simpa [T] using hz
    rcases hz' with rfl | rfl <;> simp [S]
  have hSsplit (z : V) (hz : z ∈ S) : z ∈ A ∨ z ∈ T := by
    have hz' : z = x ∨ z = y ∨ z ∈ A := by simpa [S] using hz
    rcases hz' with hzx | hzy | hzA
    · exact Or.inr (by simp [T, hzx])
    · exact Or.inr (by simp [T, hzy])
    · exact Or.inl hzA
  have hJ : J = D ⊔ E := by
    ext a b
    simp only [J, D, E, SimpleGraph.sup_adj, SimpleGraph.between_adj]
    constructor
    · rintro ⟨hab, hparts⟩
      have haS : a ∈ S := hparts.elim And.left And.left
      have hbS : b ∈ S := hparts.elim And.right And.right
      have haParts : a ∈ A ∨ a ∈ T := hSsplit a haS
      have hbParts : b ∈ A ∨ b ∈ T := hSsplit b hbS
      rcases haParts with haA | haT
      · rcases hbParts with hbA | hbT
        · exact (hA haA hbA hab.ne hab).elim
        · exact Or.inl ⟨hab, Or.inl ⟨haA, hbT⟩⟩
      · rcases hbParts with hbA | hbT
        · exact Or.inl ⟨hab, Or.inr ⟨haT, hbA⟩⟩
        · exact Or.inr ⟨hab, Or.inl ⟨haT, hbT⟩⟩
    · rintro (⟨hab, hparts⟩ | ⟨hab, hparts⟩)
      · rcases hparts with ⟨haA, hbT⟩ | ⟨haT, hbA⟩
        · exact ⟨hab, Or.inl
            ⟨hAtoS haA, hTtoS hbT⟩⟩
        · exact ⟨hab, Or.inl
            ⟨hTtoS haT, hAtoS hbA⟩⟩
      · rcases hparts with ⟨haT, hbT⟩ | ⟨haT, hbT⟩
        · exact ⟨hab, Or.inl
            ⟨hTtoS haT, hTtoS hbT⟩⟩
        · exact ⟨hab, Or.inl
            ⟨hTtoS haT, hTtoS hbT⟩⟩
  have hDE : Disjoint D E := by
    rw [SimpleGraph.disjoint_left]
    intro a b habD habE
    have hd := (SimpleGraph.between_adj.mp habD).2
    have he := (SimpleGraph.between_adj.mp habE).2
    rcases hd with ⟨haA, hbT⟩ | ⟨haT, hbA⟩ <;>
      rcases he with ⟨haT', hbT'⟩ | ⟨haT', hbT'⟩
    · exact (Finset.disjoint_left.mp hAT) haA haT'
    · exact (Finset.disjoint_left.mp hAT) haA haT'
    · exact (Finset.disjoint_left.mp hAT) hbA hbT'
    · exact (Finset.disjoint_left.mp hAT) hbA hbT'
  have hJcard : #J.edgeFinset = #D.edgeFinset + #E.edgeFinset := by
    calc
      #J.edgeFinset = #(D ⊔ E).edgeFinset :=
        congrArg Finset.card (SimpleGraph.edgeFinset_inj.mpr hJ)
      _ = #D.edgeFinset + #E.edgeFinset := by
        rw [SimpleGraph.edgeFinset_sup,
          Finset.card_union_of_disjoint
            (SimpleGraph.disjoint_edgeFinset.mpr hDE)]
  have hDdegreeX : D.degree x = C.degree x := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext z
    simp [D, C, T, SimpleGraph.between_adj, hxB, hxNotA]
  have hDdegreeY : D.degree y = C.degree y := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext z
    simp [D, C, T, SimpleGraph.between_adj, hyB, hyNotA]
  have hDbip : D.IsBipartiteWith (A : Set V) (T : Set V) := by
    simpa [D] using
      (SimpleGraph.between_isBipartiteWith (G := L)
        (Finset.disjoint_coe.mpr hAT))
  have hDcard : #D.edgeFinset = C.degree x + C.degree y := by
    have hsum :=
      SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hDbip.symm
    rw [← hsum]
    simp [T, hxy, hDdegreeX, hDdegreeY]
  have hEcard : #E.edgeFinset = if L.Adj x y then 1 else 0 := by
    by_cases hadj : L.Adj x y
    · have hEeq : E = SimpleGraph.edge x y := by
        ext a b
        rw [SimpleGraph.edge_adj]
        constructor
        · rintro ⟨hab, hparts⟩
          have haT : a ∈ T := hparts.elim And.left And.left
          have hbT : b ∈ T := hparts.elim And.right And.right
          have haT' : a = x ∨ a = y := by simpa [T] using haT
          have hbT' : b = x ∨ b = y := by simpa [T] using hbT
          rcases haT' with rfl | rfl <;> rcases hbT' with rfl | rfl
          · exact (hab.ne rfl).elim
          · exact ⟨Or.inl ⟨rfl, rfl⟩, hxy⟩
          · exact ⟨Or.inr ⟨rfl, rfl⟩, hxy.symm⟩
          · exact (hab.ne rfl).elim
        · rintro ⟨hends, hab⟩
          rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨hadj, Or.inl ⟨by simp [T], by simp [T]⟩⟩
          · exact ⟨hadj.symm, Or.inl ⟨by simp [T], by simp [T]⟩⟩
      have hedgeOne : #(SimpleGraph.edge x y).edgeFinset = 1 := by
        simp [SimpleGraph.edgeFinset,
          SimpleGraph.edgeSet_edge_of_ne hxy]
      have hcardEq : #E.edgeFinset = #(SimpleGraph.edge x y).edgeFinset :=
        congrArg Finset.card (SimpleGraph.edgeFinset_inj.mpr hEeq)
      simp [hadj, hcardEq, hedgeOne]
    · have hEeq : E = ⊥ := by
        ext a b
        simp only [E, SimpleGraph.between_adj, SimpleGraph.bot_adj,
          iff_false]
        rintro ⟨hab, hparts⟩
        have haT : a ∈ T := hparts.elim And.left And.left
        have hbT : b ∈ T := hparts.elim And.right And.right
        have haT' : a = x ∨ a = y := by simpa [T] using haT
        have hbT' : b = x ∨ b = y := by simpa [T] using hbT
        rcases haT' with rfl | rfl <;> rcases hbT' with rfl | rfl
        · exact hab.ne rfl
        · exact hadj hab
        · exact hadj hab.symm
        · exact hab.ne rfl
      have hcardEq : #E.edgeFinset = #((⊥ : SimpleGraph V).edgeFinset) :=
        congrArg Finset.card (SimpleGraph.edgeFinset_inj.mpr hEeq)
      simp [hadj, hcardEq, SimpleGraph.edgeFinset_bot]
  have hJinduce := card_between_self_eq_card_induce L S
  rw [hJcard, hDcard, hEcard] at hJinduce
  simpa [S, C] using hJinduce.symm

theorem degree_eq_between_neighbor_exterior_add_induce_exterior
    {V : Type*} [Fintype V] [DecidableEq V]
    (L : SimpleGraph V) [DecidableRel L.Adj] (w : V)
    (b : (exteriorFinset L w : Set V)) :
    L.degree (b : V) =
      (L.between (L.neighborFinset w : Set V)
        (exteriorFinset L w : Set V)).degree (b : V) +
      (L.induce (exteriorFinset L w : Set V)).degree b := by
  classical
  let A := L.neighborFinset w
  let B := exteriorFinset L w
  let C := L.between (A : Set V) (B : Set V)
  let M : Finset V :=
    ((L.induce (exteriorFinset L w : Set V)).neighborFinset b).map
      (.subtype (· ∈ (exteriorFinset L w : Set V)))
  have hbB : (b : V) ∈ B := by
    change (b : V) ∈ exteriorFinset L w
    exact b.property
  have hbNotA : (b : V) ∉ A := by
    intro hbA
    have hwb : L.Adj w (b : V) := by simpa [A] using hbA
    have hbExterior : (b : V) ≠ w ∧ ¬L.Adj w (b : V) := by
      simpa [B, exteriorFinset] using hbB
    exact hbExterior.2 hwb
  have hmap : M = L.neighborFinset (b : V) ∩ B := by
    ext y
    simp [M, B]
  have hC : C.neighborFinset (b : V) =
      L.neighborFinset (b : V) ∩ A := by
    ext y
    simp [C, SimpleGraph.between_adj, hbNotA]
  have hsplit : L.neighborFinset (b : V) =
      C.neighborFinset (b : V) ∪ M := by
    ext y
    constructor
    · intro hby
      have hbyAdj : L.Adj (b : V) y :=
        by simpa using hby
      by_cases hyA : y ∈ A
      · apply Finset.mem_union_left M
        rw [hC]
        exact Finset.mem_inter.mpr ⟨hby, hyA⟩
      · have hyw : y ≠ w := by
          intro hyw
          subst y
          have hbExterior : (b : V) ≠ w ∧ ¬L.Adj w (b : V) := by
            simpa [B, exteriorFinset] using hbB
          exact hbExterior.2 hbyAdj.symm
        have hyB : y ∈ B := by
          simp [B, exteriorFinset, A, hyw, hyA]
        apply Finset.mem_union_right _
        rw [hmap]
        exact Finset.mem_inter.mpr ⟨hby, hyB⟩
    · intro hy
      rcases Finset.mem_union.mp hy with hyC | hyM
      · rw [hC] at hyC
        exact (Finset.mem_inter.mp hyC).1
      · rw [hmap] at hyM
        exact (Finset.mem_inter.mp hyM).1
  have hdis : Disjoint (C.neighborFinset (b : V)) M := by
    rw [Finset.disjoint_left]
    intro y hyC hyM
    rw [hC] at hyC
    rw [hmap] at hyM
    have hyA : y ∈ A := (Finset.mem_inter.mp hyC).2
    have hyB : y ∈ B := (Finset.mem_inter.mp hyM).2
    have hyExterior : y ≠ w ∧ ¬L.Adj w y := by
      simpa [B, exteriorFinset] using hyB
    have hwy : L.Adj w y := by simpa [A] using hyA
    exact hyExterior.2 hwy
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree, hsplit,
    Finset.card_union_of_disjoint hdis]
  simp [M, C, A, B]

theorem card_induce_closedNeighborhood_eq_degree_of_triangleFree
    {V : Type*} [Fintype V] [DecidableEq V]
    (L : SimpleGraph V) [DecidableRel L.Adj]
    (htriangle : L.CliqueFree 3) (w : V) :
    #(L.induce
      ((insert w (L.neighborFinset w) : Finset V) : Set V)).edgeFinset =
      L.degree w := by
  classical
  let A := L.neighborFinset w
  let W : Finset V := {w}
  let C := L.between (A : Set V) (W : Set V)
  have hwNotA : w ∉ A := by simp [A]
  have hwW : w ∈ W := by simp [W]
  have hdis : Disjoint A W := by
    exact Finset.disjoint_singleton_right.mpr hwNotA
  have hAindependent : L.IsIndepSet (A : Set V) := by
    simpa [A] using
      (SimpleGraph.isIndepSet_neighborSet_of_triangleFree L htriangle w)
  have hstar := card_induce_insert_eq_between_degree_of_independent
    L A W w hwW hdis hAindependent
  have hCdegree : C.degree w = L.degree w := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext y
    simp [C, A, W, SimpleGraph.between_adj]
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet] at hstar
  simpa [A, W, C, hCdegree] using hstar

theorem card_induce_union_eq_between_add_induce_of_independent
    {V : Type*} [Fintype V] [DecidableEq V]
    (L : SimpleGraph V) [DecidableRel L.Adj]
    (A T : Finset V) (hdis : Disjoint A T)
    (hA : L.IsIndepSet (A : Set V)) :
    #(L.induce ((A ∪ T : Finset V) : Set V)).edgeFinset =
      #(L.between (A : Set V) (T : Set V)).edgeFinset +
        #(L.induce (T : Set V)).edgeFinset := by
  classical
  let S : Finset V := A ∪ T
  let D := L.between (A : Set V) (T : Set V)
  let E := L.between (T : Set V) (T : Set V)
  let J := L.between (S : Set V) (S : Set V)
  have hJ : J = D ⊔ E := by
    ext x y
    simp only [J, D, E, SimpleGraph.sup_adj, SimpleGraph.between_adj]
    constructor
    · rintro ⟨hxy, hparts⟩
      have hxS : x ∈ S := hparts.elim And.left And.left
      have hyS : y ∈ S := hparts.elim And.right And.right
      have hxParts : x ∈ A ∨ x ∈ T := by simpa [S] using hxS
      have hyParts : y ∈ A ∨ y ∈ T := by simpa [S] using hyS
      rcases hxParts with hxA | hxT
      · rcases hyParts with hyA | hyT
        · exact (hA hxA hyA hxy.ne hxy).elim
        · exact Or.inl ⟨hxy, Or.inl ⟨hxA, hyT⟩⟩
      · rcases hyParts with hyA | hyT
        · exact Or.inl ⟨hxy, Or.inr ⟨hxT, hyA⟩⟩
        · exact Or.inr ⟨hxy, Or.inl ⟨hxT, hyT⟩⟩
    · rintro (⟨hxy, hparts⟩ | ⟨hxy, hparts⟩)
      · rcases hparts with ⟨hxA, hyT⟩ | ⟨hxT, hyA⟩
        · exact ⟨hxy, Or.inl ⟨by simp [S, hxA], by simp [S, hyT]⟩⟩
        · exact ⟨hxy, Or.inl ⟨by simp [S, hxT], by simp [S, hyA]⟩⟩
      · rcases hparts with ⟨hxT, hyT⟩ | ⟨hxT, hyT⟩
        · exact ⟨hxy, Or.inl ⟨by simp [S, hxT], by simp [S, hyT]⟩⟩
        · exact ⟨hxy, Or.inl ⟨by simp [S, hxT], by simp [S, hyT]⟩⟩
  have hDE : Disjoint D E := by
    rw [SimpleGraph.disjoint_left]
    intro x y hxyD hxyE
    have hd := (SimpleGraph.between_adj.mp hxyD).2
    have he := (SimpleGraph.between_adj.mp hxyE).2
    rcases hd with ⟨hxA, hyT⟩ | ⟨hxT, hyA⟩ <;>
      rcases he with ⟨hxT', hyT'⟩ | ⟨hxT', hyT'⟩
    · exact (Finset.disjoint_left.mp hdis) hxA hxT'
    · exact (Finset.disjoint_left.mp hdis) hxA hxT'
    · exact (Finset.disjoint_left.mp hdis) hyA hyT'
    · exact (Finset.disjoint_left.mp hdis) hyA hyT'
  have hJcard : #J.edgeFinset = #D.edgeFinset + #E.edgeFinset := by
    calc
      #J.edgeFinset = #(D ⊔ E).edgeFinset :=
        congrArg Finset.card (SimpleGraph.edgeFinset_inj.mpr hJ)
      _ = #D.edgeFinset + #E.edgeFinset := by
        rw [SimpleGraph.edgeFinset_sup,
          Finset.card_union_of_disjoint
            (SimpleGraph.disjoint_edgeFinset.mpr hDE)]
  have hJinduce := card_between_self_eq_card_induce L S
  have hEinduce := card_between_self_eq_card_induce L T
  rw [hJcard, hEinduce] at hJinduce
  simpa [S, D] using hJinduce.symm

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
theorem card_induce_eq_zero_of_independent
    {V : Type*} [Fintype V] [DecidableEq V]
    (L : SimpleGraph V) [DecidableRel L.Adj]
    (S : Finset V) (hS : L.IsIndepSet (S : Set V)) :
    #(L.induce (S : Set V)).edgeFinset = 0 := by
  have hbot : L.induce (S : Set V) = ⊥ := by
    ext x y
    simp only [SimpleGraph.induce_adj, SimpleGraph.bot_adj, iff_false]
    intro hxy
    exact hS x.property y.property hxy.ne hxy
  have hempty : (L.induce (S : Set V)).edgeFinset = ∅ :=
    SimpleGraph.edgeFinset_eq_empty.mpr hbot
  rw [hempty, Finset.card_empty]

theorem compl_degree_le_four_of_admissible_indepSetFree_three_card_eleven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 3)
    (hcard : Fintype.card V = 11) :
    ∀ v, Gᶜ.degree v ≤ 4 := by
  classical
  let L := Gᶜ
  have hleFive : ∀ v, L.degree v ≤ 5 := by
    simpa [L] using
      compl_degree_le_five_of_admissible_indepSetFree_three G hG hfree
  have htriangle : L.CliqueFree 3 := by simpa [L] using hfree
  intro w
  by_contra hnot
  change ¬L.degree w ≤ 4 at hnot
  have hwle := hleFive w
  have hwdegree : L.degree w = 5 := by omega
  let A := L.neighborFinset w
  let B := exteriorFinset L w
  let C := L.between (A : Set V) (B : Set V)
  have hAcard : #A = 5 := by
    simpa [A, SimpleGraph.card_neighborFinset_eq_degree] using hwdegree
  have hwNotA : w ∉ A := by simp [A]
  have hclosedCard : #(insert w A) = 6 := by
    rw [card_insert_of_notMem hwNotA, hAcard]
  have hBcard : #B = 5 := by
    change #((insert w A)ᶜ) = 5
    rw [Finset.card_compl, hclosedCard, hcard]
  have hwNotB : w ∉ B := by simp [B, exteriorFinset]
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a haA haB
    have hwa : L.Adj w a := by simpa [A] using haA
    have haB' : a ≠ w ∧ ¬L.Adj w a := by
      simpa [B, exteriorFinset] using haB
    exact haB'.2 hwa
  have hdisSet : Disjoint (A : Set V) (B : Set V) :=
    Finset.disjoint_coe.mpr hdis
  have hbip : C.IsBipartiteWith (A : Set V) (B : Set V) := by
    simpa [C] using
      (SimpleGraph.between_isBipartiteWith (G := L) hdisSet)
  have hAindependent : L.IsIndepSet (A : Set V) := by
    simpa [A] using
      (SimpleGraph.isIndepSet_neighborSet_of_triangleFree L htriangle w)
  have hpointLower (x : V) (hxB : x ∈ B) : 4 ≤ C.degree x := by
    have hxA : x ∉ A := fun hx => (Finset.disjoint_left.mp hdis) hx hxB
    have hS : #(insert x A) = 6 := by
      rw [card_insert_of_notMem hxA, hAcard]
    have hfour :=
      four_le_card_induced_compl_of_admissible_six G hG (insert x A) hS
    have hfourNat :
        4 ≤ Nat.card (L.induce ((insert x A : Finset V) : Set V)).edgeSet := by
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
      simpa [L] using hfour
    have hedge := card_induce_insert_eq_between_degree_of_independent
      L A B x hxB hdis hAindependent
    rw [hedge] at hfourNat
    simpa [C] using hfourNat
  have hBindependent : L.IsIndepSet (B : Set V) := by
    intro x hxB y hyB hxy hxyL
    let Nx := C.neighborFinset x
    let Ny := C.neighborFinset y
    have hNxCard : 4 ≤ #Nx := by
      simpa [Nx, SimpleGraph.card_neighborFinset_eq_degree] using
        hpointLower x hxB
    have hNyCard : 4 ≤ #Ny := by
      simpa [Ny, SimpleGraph.card_neighborFinset_eq_degree] using
        hpointLower y hyB
    have hNxSub : Nx ⊆ A := by
      simpa [Nx] using
        (SimpleGraph.isBipartiteWith_neighborFinset_subset' hbip hxB)
    have hNySub : Ny ⊆ A := by
      simpa [Ny] using
        (SimpleGraph.isBipartiteWith_neighborFinset_subset' hbip hyB)
    have hUnionSub : Nx ∪ Ny ⊆ A := Finset.union_subset hNxSub hNySub
    have hUnionCard : #(Nx ∪ Ny) ≤ 5 := by
      have := Finset.card_le_card hUnionSub
      simpa [hAcard] using this
    have hCardIdentity := Finset.card_union_add_card_inter Nx Ny
    have hInterPos : 0 < #(Nx ∩ Ny) := by omega
    obtain ⟨a, haInter⟩ := Finset.card_pos.mp hInterPos
    have haxC : C.Adj a x := by
      have hxaC : C.Adj x a := by
        simpa [Nx] using (Finset.mem_inter.mp haInter).1
      exact hxaC.symm
    have hayC : C.Adj a y := by
      have hyaC : C.Adj y a := by
        simpa [Ny] using (Finset.mem_inter.mp haInter).2
      exact hyaC.symm
    have haxL : L.Adj a x := (SimpleGraph.between_adj.mp haxC).1
    have hayL : L.Adj a y := (SimpleGraph.between_adj.mp hayC).1
    have hneighborIndependent : L.IsIndepSet (L.neighborSet a) :=
      SimpleGraph.isIndepSet_neighborSet_of_triangleFree L htriangle a
    exact hneighborIndependent haxL hayL hxy hxyL
  let S : Finset V := insert w B
  have hScard : #S = 6 := by
    dsimp [S]
    rw [card_insert_of_notMem hwNotB, hBcard]
  have hSindependent : L.IsIndepSet (S : Set V) := by
    intro x hxS y hyS hxy
    rcases Finset.mem_insert.mp hxS with hxw | hxB
    · subst x
      rcases Finset.mem_insert.mp hyS with hyw | hyB
      · exact (hxy hyw.symm).elim
      · have hyExterior : ¬L.Adj w y := by
          have hyExterior' : y ≠ w ∧ ¬L.Adj w y := by
            simpa [B, exteriorFinset] using hyB
          exact hyExterior'.2
        exact hyExterior
    · rcases Finset.mem_insert.mp hyS with hyw | hyB
      · subst y
        have hxExterior : ¬L.Adj w x := by
          have hxExterior' : x ≠ w ∧ ¬L.Adj w x := by
            simpa [B, exteriorFinset] using hxB
          exact hxExterior'.2
        exact fun hxw => hxExterior hxw.symm
      · exact hBindependent hxB hyB hxy
  have hfour := four_le_card_induced_compl_of_admissible_six G hG S hScard
  have hinduce : L.induce (S : Set V) = ⊥ := by
    ext x y
    simp only [SimpleGraph.induce_adj, SimpleGraph.bot_adj, iff_false]
    intro hxyL
    exact hSindependent x.property y.property
      hxyL.ne hxyL
  have hzero : #(L.induce (S : Set V)).edgeFinset = 0 := by
    have hedgeEmpty : (L.induce (S : Set V)).edgeFinset = ∅ :=
      SimpleGraph.edgeFinset_eq_empty.mpr hinduce
    rw [hedgeEmpty, Finset.card_empty]
  change 4 ≤ #(L.induce (S : Set V)).edgeFinset at hfour
  omega

theorem exterior_cross_degree_eq_two_of_admissible_order_eleven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 3)
    (hcard : Fintype.card V = 11) (w : V)
    (hwdegree : Gᶜ.degree w = 4) :
    ∀ b : (exteriorFinset Gᶜ w : Set V),
      (Gᶜ.between (Gᶜ.neighborFinset w : Set V)
        (exteriorFinset Gᶜ w : Set V)).degree (b : V) = 2 := by
  classical
  let L := Gᶜ
  let A := L.neighborFinset w
  let B := exteriorFinset L w
  let C := L.between (A : Set V) (B : Set V)
  let H := L.induce (B : Set V)
  let p : ↥(B : Set V) → ℕ := fun b => C.degree (b : V)
  have hdegree : ∀ v, L.degree v ≤ 4 := by
    simpa [L] using
      compl_degree_le_four_of_admissible_indepSetFree_three_card_eleven
        G hG hfree hcard
  have htriangle : L.CliqueFree 3 := by simpa [L] using hfree
  have hAcard : #A = 4 := by
    simpa [A, L, SimpleGraph.card_neighborFinset_eq_degree] using hwdegree
  have hBcard : #B = 6 := by
    have hBraw := card_exteriorFinset L w
    have hLdegree : L.degree w = 4 := by simpa [L] using hwdegree
    rw [hcard, hLdegree] at hBraw
    simpa [B] using hBraw
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a haA haB
    have hwa : L.Adj w a := by simpa [A] using haA
    have haExterior : a ≠ w ∧ ¬L.Adj w a := by
      simpa [B, exteriorFinset] using haB
    exact haExterior.2 hwa
  have hdisSet : Disjoint (A : Set V) (B : Set V) :=
    Finset.disjoint_coe.mpr hdis
  have hbip : C.IsBipartiteWith (A : Set V) (B : Set V) := by
    simpa [C] using
      (SimpleGraph.between_isBipartiteWith (G := L) hdisSet)
  have hsumA : (∑ a ∈ A, C.degree a) = #C.edgeFinset :=
    SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hbip
  have hsumB : (∑ b ∈ B, C.degree b) = #C.edgeFinset :=
    SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hbip.symm
  have hpointUpper (a : V) (haA : a ∈ A) : C.degree a ≤ 3 := by
    have haccount := degree_neighbor_eq_one_add_internal_add_cross
      L w a (by simpa [A] using haA)
    have haccount' :
        L.degree a =
          1 + (neighborhoodInternalGraph L w).degree a + C.degree a := by
      simpa [C, A, B] using haccount
    have haDegree := hdegree a
    omega
  have hsumUpperA : (∑ a ∈ A, C.degree a) ≤ 3 * #A := by
    calc
      (∑ a ∈ A, C.degree a) ≤ ∑ _a ∈ A, 3 :=
        Finset.sum_le_sum fun a ha => hpointUpper a ha
      _ = 3 * #A := by simp [Nat.mul_comm]
  have hpSum : (∑ b, p b) ≤ 12 := by
    calc
      (∑ b, p b) = ∑ b ∈ B, C.degree b := by
        simpa [p] using (sum_attach B fun b => C.degree b)
      _ = #C.edgeFinset := hsumB
      _ = ∑ a ∈ A, C.degree a := hsumA.symm
      _ ≤ 3 * #A := hsumUpperA
      _ = 12 := by rw [hAcard]
  have hAindependent : L.IsIndepSet (A : Set V) := by
    simpa [A] using
      (SimpleGraph.isIndepSet_neighborSet_of_triangleFree L htriangle w)
  have hpPair : ∀ x y : (B : Set V), x ≠ y →
      4 ≤ p x + p y + if H.Adj x y then 1 else 0 := by
    intro x y hxy
    have hxyV : (x : V) ≠ (y : V) := fun h => hxy (Subtype.ext h)
    have hxB : (x : V) ∈ B := x.property
    have hyB : (y : V) ∈ B := y.property
    have hxA : (x : V) ∉ A := fun hx =>
      (Finset.disjoint_left.mp hdis) hx hxB
    have hyA : (y : V) ∉ A := fun hy =>
      (Finset.disjoint_left.mp hdis) hy hyB
    let S : Finset V := insert (x : V) (insert (y : V) A)
    have hxNot : (x : V) ∉ insert (y : V) A := by
      simp [hxyV, hxA]
    have hScard : #S = 6 := by
      dsimp [S]
      rw [Finset.card_insert_of_notMem hxNot,
        Finset.card_insert_of_notMem hyA, hAcard]
    have hfour :=
      four_le_card_induced_compl_of_admissible_six G hG S hScard
    have hexact := card_induce_pair_add_between_degrees_of_independent
      L A B (x : V) (y : V) hxB hyB hxyV hdis hAindependent
    change 4 ≤ #(L.induce (S : Set V)).edgeFinset at hfour
    dsimp [S] at hfour
    rw [hexact] at hfour
    simpa [p, H, C] using hfour
  have hpDegree : ∀ b : (B : Set V), p b + H.degree b ≤ 4 := by
    intro b
    have hsplit :=
      degree_eq_between_neighbor_exterior_add_induce_exterior L w b
    have hbDegree := hdegree (b : V)
    have hsplit' : L.degree (b : V) = p b + H.degree b := by
      simpa [p, H, C, A, B] using hsplit
    omega
  have hBtype : Fintype.card (B : Set V) = 6 := by simpa using hBcard
  have hpTwo := six_cross_values_eq_two H p hBtype hpSum hpPair hpDegree
  intro b
  exact hpTwo b

theorem four_le_card_exterior_edges_of_admissible_order_eleven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 3)
    (hcard : Fintype.card V = 11) (w : V)
    (hwdegree : Gᶜ.degree w = 4) (hcomplEdges : 20 ≤ #Gᶜ.edgeFinset) :
    4 ≤ #(Gᶜ.induce (exteriorFinset Gᶜ w : Set V)).edgeFinset := by
  classical
  let L := Gᶜ
  let A := L.neighborFinset w
  let B := exteriorFinset L w
  let C := L.between (A : Set V) (B : Set V)
  let S : Finset V := insert w A
  have hLedges : 20 ≤ #L.edgeFinset := by simpa [L] using hcomplEdges
  have hLdegree : L.degree w = 4 := by simpa [L] using hwdegree
  have hAcard : #A = 4 := by
    simpa [A, SimpleGraph.card_neighborFinset_eq_degree] using hLdegree
  have hBcard : #B = 6 := by
    have hBraw := card_exteriorFinset L w
    rw [hcard, hLdegree] at hBraw
    simpa [B] using hBraw
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a haA haB
    have hwa : L.Adj w a := by simpa [A] using haA
    have haExterior : a ≠ w ∧ ¬L.Adj w a := by
      simpa [B, exteriorFinset] using haB
    exact haExterior.2 hwa
  have hbip : C.IsBipartiteWith (A : Set V) (B : Set V) := by
    simpa [C] using
      (SimpleGraph.between_isBipartiteWith (G := L)
        (Finset.disjoint_coe.mpr hdis))
  have htwoRaw := exterior_cross_degree_eq_two_of_admissible_order_eleven
    G hG hfree hcard w hwdegree
  have htwo (b : V) (hbB : b ∈ B) : C.degree b = 2 := by
    let bB : (B : Set V) := ⟨b, hbB⟩
    simpa [L, A, B, C, bB] using htwoRaw bB
  have hsumB : (∑ b ∈ B, C.degree b) = #C.edgeFinset :=
    SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hbip.symm
  have hCedges : #C.edgeFinset = 12 := by
    rw [← hsumB]
    calc
      (∑ b ∈ B, C.degree b) = ∑ _b ∈ B, 2 :=
        Finset.sum_congr rfl htwo
      _ = 12 := by simp [hBcard]
  have htriangle : L.CliqueFree 3 := by simpa [L] using hfree
  have hclosed :=
    card_induce_closedNeighborhood_eq_degree_of_triangleFree L htriangle w
  have hpartition := card_edgeFinset_eq_induce_add_between_add_induce_compl L S
  have hBcompl : B = Sᶜ := by rfl
  have hcrossGraph :
      L.between (S : Set V) (B : Set V) = C := by
    simpa [S, A, B, C] using
      between_closedNeighborhood_exterior_eq_between_neighbor_exterior L w
  have hcrossCard :
      #(L.between (S : Set V) (B : Set V)).edgeFinset = #C.edgeFinset :=
    congrArg Finset.card (SimpleGraph.edgeFinset_inj.mpr hcrossGraph)
  rw [← hBcompl, hcrossCard] at hpartition
  have hclosed' : #(L.induce (S : Set V)).edgeFinset = 4 := by
    simpa [S, A, hLdegree] using hclosed
  rw [hclosed', hCedges] at hpartition
  have hfour : 4 ≤ #(L.induce (B : Set V)).edgeFinset := by omega
  simpa [L, B] using hfour

theorem exists_exterior_equal_label_pair_and_third_of_order_eleven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 3)
    (hcard : Fintype.card V = 11) (w : V)
    (hwdegree : Gᶜ.degree w = 4) (hcomplEdges : 20 ≤ #Gᶜ.edgeFinset) :
    let L := Gᶜ
    let A := L.neighborFinset w
    let B := exteriorFinset L w
    let C := L.between (A : Set V) (B : Set V)
    ∃ x y z : (B : Set V),
      x ≠ y ∧ z ≠ x ∧ z ≠ y ∧
        C.neighborFinset (x : V) = C.neighborFinset (y : V) ∧
        C.neighborFinset (z : V) ≠ A \ C.neighborFinset (x : V) := by
  classical
  dsimp only
  let L := Gᶜ
  let A := L.neighborFinset w
  let B := exteriorFinset L w
  let C := L.between (A : Set V) (B : Set V)
  let H := L.induce (B : Set V)
  let q : ↥(B : Set V) → Finset V := fun b => C.neighborFinset (b : V)
  have hLdegree : L.degree w = 4 := by simpa [L] using hwdegree
  have hAcard : #A = 4 := by
    simpa [A, SimpleGraph.card_neighborFinset_eq_degree] using hLdegree
  have hBcard : #B = 6 := by
    have hBraw := card_exteriorFinset L w
    rw [hcard, hLdegree] at hBraw
    simpa [B] using hBraw
  have hBtype : Fintype.card (B : Set V) = 6 := by simpa using hBcard
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a haA haB
    have hwa : L.Adj w a := by simpa [A] using haA
    have haExterior : a ≠ w ∧ ¬L.Adj w a := by
      simpa [B, exteriorFinset] using haB
    exact haExterior.2 hwa
  have hbip : C.IsBipartiteWith (A : Set V) (B : Set V) := by
    simpa [C] using
      (SimpleGraph.between_isBipartiteWith (G := L)
        (Finset.disjoint_coe.mpr hdis))
  have htwoRaw := exterior_cross_degree_eq_two_of_admissible_order_eleven
    G hG hfree hcard w hwdegree
  have hqcard (b : (B : Set V)) : #(q b) = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    simpa [q, C, A, B, L] using htwoRaw b
  have hqsub (b : (B : Set V)) : q b ⊆ A := by
    simpa [q] using
      (SimpleGraph.isBipartiteWith_neighborFinset_subset' hbip b.property)
  have htriangle : L.CliqueFree 3 := by simpa [L] using hfree
  have hadjDisjoint : ∀ {x y : (B : Set V)},
      H.Adj x y → Disjoint (q x) (q y) := by
    intro x y hxy
    rw [Finset.disjoint_left]
    intro a hax hay
    have hxaC : C.Adj (x : V) a := by simpa [q] using hax
    have hyaC : C.Adj (y : V) a := by simpa [q] using hay
    have hxaL : L.Adj (x : V) a := (SimpleGraph.between_adj.mp hxaC).1
    have hyaL : L.Adj (y : V) a := (SimpleGraph.between_adj.mp hyaC).1
    have hxyL : L.Adj (x : V) (y : V) := by simpa [H] using hxy
    have hneighborIndependent : L.IsIndepSet (L.neighborSet a) :=
      SimpleGraph.isIndepSet_neighborSet_of_triangleFree L htriangle a
    exact hneighborIndependent hxaL.symm hyaL.symm hxyL.ne hxyL
  have hHedgesRaw := four_le_card_exterior_edges_of_admissible_order_eleven
    G hG hfree hcard w hwdegree hcomplEdges
  have hHedges : 4 ≤ #H.edgeFinset := by simpa [H, B, L] using hHedgesRaw
  have hnotinj := labels_not_injective_of_six_vertices_four_edges
    H A q hBtype hAcard hqsub hqcard hadjDisjoint hHedges
  have hcollision := exists_equal_label_pair_and_third
    A q hBtype hAcard hqsub hqcard hnotinj
  simpa [L, A, B, C, q] using hcollision

theorem degree_four_compl_impossible_of_twenty_edges_order_eleven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 3)
    (hcard : Fintype.card V = 11) (w : V)
    (hwdegree : Gᶜ.degree w = 4) (hcomplEdges : 20 ≤ #Gᶜ.edgeFinset) :
    False := by
  classical
  let L := Gᶜ
  let A := L.neighborFinset w
  let B := exteriorFinset L w
  let C := L.between (A : Set V) (B : Set V)
  let H := L.induce (B : Set V)
  let q : ↥(B : Set V) → Finset V := fun b => C.neighborFinset (b : V)
  have hLdegree : L.degree w = 4 := by simpa [L] using hwdegree
  have hAcard : #A = 4 := by
    simpa [A, SimpleGraph.card_neighborFinset_eq_degree] using hLdegree
  have hBcard : #B = 6 := by
    have hBraw := card_exteriorFinset L w
    rw [hcard, hLdegree] at hBraw
    simpa [B] using hBraw
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a haA haB
    have hwa : L.Adj w a := by simpa [A] using haA
    have haExterior : a ≠ w ∧ ¬L.Adj w a := by
      simpa [B, exteriorFinset] using haB
    exact haExterior.2 hwa
  have hbip : C.IsBipartiteWith (A : Set V) (B : Set V) := by
    simpa [C] using
      (SimpleGraph.between_isBipartiteWith (G := L)
        (Finset.disjoint_coe.mpr hdis))
  have htwoRaw := exterior_cross_degree_eq_two_of_admissible_order_eleven
    G hG hfree hcard w hwdegree
  have hqcard (b : (B : Set V)) : #(q b) = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    simpa [q, C, A, B, L] using htwoRaw b
  have hqsub (b : (B : Set V)) : q b ⊆ A := by
    simpa [q] using
      (SimpleGraph.isBipartiteWith_neighborFinset_subset' hbip b.property)
  have htriangle : L.CliqueFree 3 := by simpa [L] using hfree
  have hAindependent : L.IsIndepSet (A : Set V) := by
    simpa [A] using
      (SimpleGraph.isIndepSet_neighborSet_of_triangleFree L htriangle w)
  have hadjDisjoint : ∀ {x y : (B : Set V)},
      H.Adj x y → Disjoint (q x) (q y) := by
    intro x y hxy
    rw [Finset.disjoint_left]
    intro a hax hay
    have hxaC : C.Adj (x : V) a := by simpa [q] using hax
    have hyaC : C.Adj (y : V) a := by simpa [q] using hay
    have hxaL : L.Adj (x : V) a := (SimpleGraph.between_adj.mp hxaC).1
    have hyaL : L.Adj (y : V) a := (SimpleGraph.between_adj.mp hyaC).1
    have hxyL : L.Adj (x : V) (y : V) := by simpa [H] using hxy
    have hneighborIndependent : L.IsIndepSet (L.neighborSet a) :=
      SimpleGraph.isIndepSet_neighborSet_of_triangleFree L htriangle a
    exact hneighborIndependent hxaL.symm hyaL.symm hxyL.ne hxyL
  have hcollisionRaw :=
    exists_exterior_equal_label_pair_and_third_of_order_eleven
      G hG hfree hcard w hwdegree hcomplEdges
  have hcollision :
      ∃ x y z : (B : Set V),
        x ≠ y ∧ z ≠ x ∧ z ≠ y ∧ q x = q y ∧ q z ≠ A \ q x := by
    simpa [L, A, B, C, q] using hcollisionRaw
  obtain ⟨x, y, z, hxy, hzx, hzy, hqxy, hqz⟩ := hcollision
  have hxyV : (x : V) ≠ (y : V) := fun h => hxy (Subtype.ext h)
  have hxzV : (x : V) ≠ (z : V) := fun h => hzx (Subtype.ext h.symm)
  have hyzV : (y : V) ≠ (z : V) := fun h => hzy (Subtype.ext h.symm)
  let P : Finset V := A \ q x
  let T : Finset V := {(x : V), (y : V), (z : V)}
  have hPsub : P ⊆ A := by exact Finset.sdiff_subset
  have hPcard : #P = 2 := by
    dsimp [P]
    rw [Finset.card_sdiff_of_subset (hqsub x), hAcard, hqcard]
  have hTsub : T ⊆ B := by
    intro a ha
    have ha' : a = (x : V) ∨ a = (y : V) ∨ a = (z : V) := by
      simpa [T] using ha
    rcases ha' with rfl | rfl | rfl
    · exact x.property
    · exact y.property
    · exact z.property
  have hTcard : #T = 3 := by
    simp [T, hxyV, hxzV, hyzV]
  have hPTdis : Disjoint P T :=
    (hdis.mono_left hPsub).mono_right hTsub
  have hnotHxy : ¬H.Adj x y := by
    intro hAdj
    have hlabelsDis := hadjDisjoint hAdj
    have hqPos : 0 < #(q x) := by rw [hqcard]; norm_num
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hqPos
    have hay : a ∈ q y := by rw [← hqxy]; exact ha
    exact (Finset.disjoint_left.mp hlabelsDis) ha hay
  have hnotHxz : ¬H.Adj x z := by
    intro hAdj
    have heq := eq_sdiff_of_subset_card_two_disjoint
      hAcard (hqsub x) (hqcard x) (hqsub z) (hqcard z)
        (hadjDisjoint hAdj)
    exact hqz heq
  have hnotHyz : ¬H.Adj y z := by
    intro hAdj
    have heq := eq_sdiff_of_subset_card_two_disjoint
      hAcard (hqsub y) (hqcard y) (hqsub z) (hqcard z)
        (hadjDisjoint hAdj)
    rw [← hqxy] at heq
    exact hqz heq
  have hnotLxy : ¬L.Adj (x : V) (y : V) := by
    simpa [H] using hnotHxy
  have hnotLxz : ¬L.Adj (x : V) (z : V) := by
    simpa [H] using hnotHxz
  have hnotLyz : ¬L.Adj (y : V) (z : V) := by
    simpa [H] using hnotHyz
  have hTindependent : L.IsIndepSet (T : Set V) := by
    intro a ha b hb hab
    have ha' : a = (x : V) ∨ a = (y : V) ∨ a = (z : V) := by
      simpa [T] using ha
    have hb' : b = (x : V) ∨ b = (y : V) ∨ b = (z : V) := by
      simpa [T] using hb
    rcases ha' with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl
    · exact (hab rfl).elim
    · exact hnotLxy
    · exact hnotLxz
    · exact fun h => hnotLxy h.symm
    · exact (hab rfl).elim
    · exact hnotLyz
    · exact fun h => hnotLxz h.symm
    · exact fun h => hnotLyz h.symm
    · exact (hab rfl).elim
  have hTzero := card_induce_eq_zero_of_independent L T hTindependent
  have hPindependent : L.IsIndepSet (P : Set V) := by
    intro a ha b hb hab
    exact hAindependent (hPsub ha) (hPsub hb) hab
  let D := L.between (P : Set V) (T : Set V)
  have hDneighbors (b : (B : Set V)) (hbT : (b : V) ∈ T) :
      D.neighborFinset (b : V) = q b ∩ P := by
    ext a
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_inter]
    constructor
    · intro hbaD
      have hparts := (SimpleGraph.between_adj.mp hbaD).2
      have haP : a ∈ P := by
        rcases hparts with ⟨hbP, _⟩ | ⟨_, haP⟩
        · exact ((Finset.disjoint_left.mp hPTdis) hbP hbT).elim
        · exact haP
      have hbaC : C.Adj (b : V) a :=
        ⟨(SimpleGraph.between_adj.mp hbaD).1,
          Or.inr ⟨b.property, hPsub haP⟩⟩
      exact ⟨by simpa [q] using hbaC, haP⟩
    · rintro ⟨hbaQ, haP⟩
      have hbaC : C.Adj (b : V) a := by simpa [q] using hbaQ
      exact ⟨(SimpleGraph.between_adj.mp hbaC).1,
        Or.inr ⟨hbT, haP⟩⟩
  have hDdegree (b : (B : Set V)) (hbT : (b : V) ∈ T) :
      D.degree (b : V) = #(q b ∩ P) := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hDneighbors b hbT]
  have hxT : (x : V) ∈ T := by simp [T]
  have hyT : (y : V) ∈ T := by simp [T]
  have hzT : (z : V) ∈ T := by simp [T]
  have hxInterZero : #(q x ∩ P) = 0 := by
    apply Finset.card_eq_zero.mpr
    ext a
    simp [P]
  have hyInterZero : #(q y ∩ P) = 0 := by
    rw [← hqxy]
    exact hxInterZero
  have hzInterLe : #(q z ∩ P) ≤ 1 := by
    by_contra hnot
    have hle : #(q z ∩ P) ≤ #(q z) :=
      Finset.card_le_card Finset.inter_subset_left
    have hinterCard : #(q z ∩ P) = 2 := by
      rw [hqcard z] at hle
      omega
    have hinterEq : q z ∩ P = q z := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      rw [hinterCard, hqcard]
    have hqzSubP : q z ⊆ P := by
      intro a ha
      have haInter : a ∈ q z ∩ P := by
        rw [hinterEq]
        exact ha
      exact (Finset.mem_inter.mp haInter).2
    have hqzEqP : q z = P := by
      apply Finset.eq_of_subset_of_card_le hqzSubP
      rw [hPcard, hqcard]
    exact hqz hqzEqP
  have hDx : D.degree (x : V) = 0 := by
    rw [hDdegree x hxT, hxInterZero]
  have hDy : D.degree (y : V) = 0 := by
    rw [hDdegree y hyT, hyInterZero]
  have hDz : D.degree (z : V) ≤ 1 := by
    rw [hDdegree z hzT]
    exact hzInterLe
  have hDbip : D.IsBipartiteWith (P : Set V) (T : Set V) := by
    simpa [D] using
      (SimpleGraph.between_isBipartiteWith (G := L)
        (Finset.disjoint_coe.mpr hPTdis))
  have hsumT : (∑ t ∈ T, D.degree t) = #D.edgeFinset :=
    SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hDbip.symm
  have hsumTexpand :
      (∑ t ∈ T, D.degree t) =
        D.degree (x : V) + D.degree (y : V) + D.degree (z : V) := by
    simp [T, hxyV, hxzV, hyzV, Nat.add_assoc]
  have hDedges : #D.edgeFinset ≤ 1 := by
    rw [← hsumT, hsumTexpand, hDx, hDy]
    simpa using hDz
  let R : Finset V := P ∪ T
  have hRcard : #R = 5 := by
    dsimp [R]
    rw [Finset.card_union_of_disjoint hPTdis, hPcard, hTcard]
  have hRinduced :=
    card_induce_union_eq_between_add_induce_of_independent
      L P T hPTdis hPindependent
  have hRedges : #(L.induce (R : Set V)).edgeFinset ≤ 1 := by
    have hRinduced' :
        #(L.induce (R : Set V)).edgeFinset =
          #D.edgeFinset + #(L.induce (T : Set V)).edgeFinset := by
      simpa [R, D] using hRinduced
    rw [hRinduced', hTzero]
    simpa using hDedges
  let W : Finset V := {w}
  have hwW : w ∈ W := by simp [W]
  have hwNotP : w ∉ P := by
    intro hwP
    have hwA := hPsub hwP
    change w ∈ L.neighborFinset w at hwA
    exact (L.notMem_neighborFinset_self w) hwA
  have hwNotT : w ∉ T := by
    intro hwT
    have hwB := hTsub hwT
    change w ∈ exteriorFinset L w at hwB
    have hwNotB : w ∉ exteriorFinset L w := by simp [exteriorFinset]
    exact hwNotB hwB
  have hwNotR : w ∉ R := by simp [R, hwNotP, hwNotT]
  have hWRdis : Disjoint W R :=
    Finset.disjoint_singleton_left.mpr hwNotR
  have hWindependent : L.IsIndepSet (W : Set V) := by
    intro a ha b hb hab
    have ha' : a = w := by simpa [W] using ha
    have hb' : b = w := by simpa [W] using hb
    subst a
    subst b
    exact (hab rfl).elim
  let K := L.between (W : Set V) (R : Set V)
  have hKbip : K.IsBipartiteWith (W : Set V) (R : Set V) := by
    simpa [K] using
      (SimpleGraph.between_isBipartiteWith (G := L)
        (Finset.disjoint_coe.mpr hWRdis))
  have hKneighbors : K.neighborFinset w = P := by
    ext a
    constructor
    · intro hwaK
      have haR :=
        SimpleGraph.isBipartiteWith_neighborFinset_subset hKbip hwW hwaK
      rcases Finset.mem_union.mp (by simpa [R] using haR) with haP | haT
      · exact haP
      · have haB := hTsub haT
        have haExterior : a ≠ w ∧ ¬L.Adj w a := by
          simpa [B, exteriorFinset] using haB
        have hwaL : L.Adj w a :=
          (SimpleGraph.between_adj.mp (by simpa using hwaK)).1
        exact (haExterior.2 hwaL).elim
    · intro haP
      have hwaL : L.Adj w a := by simpa [A] using hPsub haP
      have haR : a ∈ R := by simp [R, haP]
      have hwaK : K.Adj w a := ⟨hwaL, Or.inl ⟨hwW, haR⟩⟩
      simpa using hwaK
  have hKdegree : K.degree w = 2 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hKneighbors, hPcard]
  have hsumW : (∑ a ∈ W, K.degree a) = #K.edgeFinset :=
    SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hKbip
  have hKedges : #K.edgeFinset = 2 := by
    rw [← hsumW]
    simp [W, hKdegree]
  let S : Finset V := W ∪ R
  have hScard : #S = 6 := by
    dsimp [S]
    rw [Finset.card_union_of_disjoint hWRdis, Finset.card_singleton, hRcard]
  have hSinduced :=
    card_induce_union_eq_between_add_induce_of_independent
      L W R hWRdis hWindependent
  have hSedges : #(L.induce (S : Set V)).edgeFinset ≤ 3 := by
    have hSinduced' :
        #(L.induce (S : Set V)).edgeFinset =
          #K.edgeFinset + #(L.induce (R : Set V)).edgeFinset := by
      simpa [S, K] using hSinduced
    rw [hSinduced', hKedges]
    omega
  have hfour := four_le_card_induced_compl_of_admissible_six G hG S hScard
  change 4 ≤ #(L.induce (S : Set V)).edgeFinset at hfour
  omega

theorem card_edges_ge_thirtySix_of_admissible_indepSetFree_three_card_eleven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 3)
    (hcard : Fintype.card V = 11) :
    36 ≤ #G.edgeFinset := by
  classical
  let L := Gᶜ
  have hdegree : ∀ v, L.degree v ≤ 4 := by
    simpa [L] using
      compl_degree_le_four_of_admissible_indepSetFree_three_card_eleven
        G hG hfree hcard
  by_contra hnot
  have hGupper : #G.edgeFinset ≤ 35 := by omega
  have hpartition := card_edgeFinset_add_card_compl G
  change #G.edgeFinset + #L.edgeFinset =
    (Fintype.card V).choose 2 at hpartition
  rw [hcard] at hpartition
  norm_num [Nat.choose] at hpartition
  have hLedges : 20 ≤ #L.edgeFinset := by omega
  have hexistsDegreeFour : ∃ w, L.degree w = 4 := by
    by_contra hnone
    push Not at hnone
    have hdegreeThree : ∀ v, L.degree v ≤ 3 := by
      intro v
      have hvle := hdegree v
      have hvne := hnone v
      omega
    have hsumUpper : (∑ v, L.degree v) ≤ 3 * Fintype.card V := by
      calc
        (∑ v, L.degree v) ≤ ∑ _v : V, 3 :=
          Finset.sum_le_sum fun v _ => hdegreeThree v
        _ = 3 * Fintype.card V := by simp [Nat.mul_comm]
    rw [L.sum_degrees_eq_twice_card_edges, hcard] at hsumUpper
    omega
  obtain ⟨w, hwdegree⟩ := hexistsDegreeFour
  exact degree_four_compl_impossible_of_twenty_edges_order_eleven
    G hG hfree hcard w (by simpa [L] using hwdegree)
      (by simpa [L] using hLedges)

end Erdos617
