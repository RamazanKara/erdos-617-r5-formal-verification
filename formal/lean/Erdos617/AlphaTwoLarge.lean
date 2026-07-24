/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.DegreeReduction
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Large admissible graphs with independence number two

This module formalizes the elementary terminal estimate used for the large
independence-two cases in the fixed-`r = 5` argument.  If every six vertices
span at most eleven edges and a graph has no independent triple, then its
complement has maximum degree at most four once the order is at least twelve.
Consequently the original graph has at least `choose n 2 - 2 * n` edges.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

universe u

/-- In an admissible graph with no independent triple, the complement has
maximum degree at most five. -/
theorem compl_degree_le_five_of_admissible_indepSetFree_three
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 3) :
    ∀ v, Gᶜ.degree v ≤ 5 := by
  classical
  have htriangle : Gᶜ.CliqueFree 3 := by simpa using hfree
  have hcliqueSix : G.CliqueFree 6 := admissible_cliqueFree_six G hG
  intro v
  by_contra hnot
  have hlarge : 6 ≤ #(Gᶜ.neighborFinset v) := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨S, hsubset, hcard⟩ := Finset.exists_subset_card_eq hlarge
  have hneighbor : Gᶜ.IsIndepSet (Gᶜ.neighborSet v) :=
    SimpleGraph.isIndepSet_neighborSet_of_triangleFree Gᶜ htriangle v
  have hindependent : Gᶜ.IsIndepSet (S : Set V) := by
    intro a ha b hb hab
    apply hneighbor
    · have ha' : a ∈ Gᶜ.neighborFinset v := hsubset ha
      simpa using ha'
    · have hb' : b ∈ Gᶜ.neighborFinset v := hsubset hb
      simpa using hb'
    · exact hab
  have hclique : G.IsClique (S : Set V) := by simpa using hindependent
  exact hcliqueSix S ⟨hclique, hcard⟩

/-- If `A` is independent and `x` lies in a disjoint set `B`, then every edge
induced by `insert x A` is an `A`--`B` edge incident with `x`.  `Nat.card` makes
the statement independent of the chosen finite-type instance on the subtype.
-/
theorem card_induce_insert_eq_between_degree_of_independent
    {V : Type u} [Fintype V] [DecidableEq V]
    (L : SimpleGraph V) [DecidableRel L.Adj]
    (A B : Finset V) (x : V) (hxB : x ∈ B) (hdis : Disjoint A B)
    (hA : L.IsIndepSet (A : Set V)) :
    Nat.card (L.induce ((insert x A : Finset V) : Set V)).edgeSet =
      (L.between (A : Set V) (B : Set V)).degree x := by
  classical
  have hx : x ∉ A := fun hxA => (Finset.disjoint_left.mp hdis) hxA hxB
  let S : Finset V := insert x A
  let s : Set V := (S : Set V)
  letI : Fintype s := Subtype.fintype (Membership.mem s)
  let C := L.between (A : Set V) (B : Set V)
  let xS : s := ⟨x, by simp [s, S]⟩
  have hdelete : (L.induce s).deleteIncidenceSet xS = ⊥ := by
    ext p q
    rw [SimpleGraph.deleteIncidenceSet_adj]
    simp only [SimpleGraph.bot_adj, iff_false]
    rintro ⟨hpq, hpne, hqne⟩
    have hpA : (p : V) ∈ A := by
      rcases Finset.mem_insert.mp p.property with hp | hp
      · exact (hpne (Subtype.ext hp)).elim
      · exact hp
    have hqA : (q : V) ∈ A := by
      rcases Finset.mem_insert.mp q.property with hq | hq
      · exact (hqne (Subtype.ext hq)).elim
      · exact hq
    have hpqL : L.Adj (p : V) (q : V) := hpq
    exact hA hpA hqA (fun hpqv => hpq.ne (Subtype.ext hpqv)) hpqL
  have hdeleted := (L.induce s).card_edgeFinset_deleteIncidenceSet xS
  have hdegreeLe := (L.induce s).degree_le_card_edgeFinset xS
  have hedgeDegree : #(L.induce s).edgeFinset =
      (L.induce s).degree xS := by
    have hdeleteFinset :
        ((L.induce s).deleteIncidenceSet xS).edgeFinset = ∅ := by
      rw [← SimpleGraph.edgeFinset_bot]
      exact SimpleGraph.edgeFinset_inj.mpr hdelete
    have hdeleteCard :
        #((L.induce s).deleteIncidenceSet xS).edgeFinset = 0 := by
      rw [hdeleteFinset, Finset.card_empty]
    rw [hdeleteCard] at hdeleted
    omega
  have hmap := L.map_neighborFinset_induce xS
  have hneighbors : L.neighborFinset x ∩ s.toFinset = C.neighborFinset x := by
    ext y
    simp [s, S, C, SimpleGraph.between_adj, hx, hxB]
  have hdegree : (L.induce s).degree xS = C.degree x := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree]
    calc
      #((L.induce s).neighborFinset xS) =
          #(((L.induce s).neighborFinset xS).map
            (.subtype (· ∈ s))) := by
        rw [Finset.card_map]
      _ = #(L.neighborFinset x ∩ s.toFinset) :=
        congrArg Finset.card hmap
      _ = #(C.neighborFinset x) := congrArg Finset.card hneighbors
  have hgraph :
      L.induce (((insert x A : Finset V) : Set V)) = L.induce s := by
    ext p q
    simp [s, S]
  have hedgeNat : Nat.card (L.induce s).edgeSet = C.degree x := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
    exact hedgeDegree.trans hdegree
  calc
    Nat.card (L.induce (((insert x A : Finset V) : Set V))).edgeSet =
        Nat.card (L.induce s).edgeSet := by rw [hgraph]
    _ = C.degree x := hedgeNat
    _ = (L.between (A : Set V) (B : Set V)).degree x := by rfl

/-- Inducing and then complementing agrees with complementing and then
inducing. -/
theorem induce_compl_eq_compl_induce
    {V : Type u} (G : SimpleGraph V) (S : Finset V) :
    (G.induce (S : Set V))ᶜ = Gᶜ.induce (S : Set V) := by
  ext a b
  simp

/-- Admissibility forces at least four complementary edges on every six
vertices. -/
theorem four_le_card_induced_compl_of_admissible_six
    {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (S : Finset V) (hS : #S = 6) :
    4 ≤ #(Gᶜ.induce (S : Set V)).edgeFinset := by
  have hlocal := hG S hS
  have hpartition := card_edgeFinset_add_card_compl (G.induce (S : Set V))
  have hcomp := induce_compl_eq_compl_induce G S
  have hcompCard : #((G.induce (S : Set V))ᶜ).edgeFinset =
      #(Gᶜ.induce (S : Set V)).edgeFinset :=
    congrArg Finset.card (SimpleGraph.edgeFinset_inj.mpr hcomp)
  rw [hcompCard] at hpartition
  have hcard : Fintype.card (S : Set V) = 6 := by simpa using hS
  norm_num [hcard, Nat.choose] at hpartition
  omega

/-- In an admissible graph with no independent triple and at least twelve
vertices, the complement has maximum degree at most four. -/
theorem compl_degree_le_four_of_admissible_indepSetFree_three
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 3)
    (hcard : 12 ≤ Fintype.card V) :
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
  have hwdegree : L.degree w = 5 := by
    have hlower : 5 ≤ L.degree w := by omega
    exact Nat.le_antisymm (hleFive w) hlower
  let A := L.neighborFinset w
  let B := exteriorFinset L w
  let C := L.between (A : Set V) (B : Set V)
  have hAcard : #A = 5 := by
    simpa [A, SimpleGraph.card_neighborFinset_eq_degree] using hwdegree
  have hwNotA : w ∉ A := by simp [A]
  have hclosedCard : #(insert w A) = 6 := by
    rw [card_insert_of_notMem hwNotA, hAcard]
  have hBcard : #B = Fintype.card V - 6 := by
    change #((insert w A)ᶜ) = Fintype.card V - 6
    rw [Finset.card_compl, hclosedCard]
  have hBlarge : 6 ≤ #B := by omega
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a haA haB
    have hwa : L.Adj w a := by simpa [A] using haA
    have haB' : a ≠ w ∧ ¬L.Adj w a := by
      simpa [B, exteriorFinset] using haB
    exact haB'.2 hwa
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
  have hsumLower : 4 * #B ≤ ∑ x ∈ B, C.degree x := by
    calc
      4 * #B = ∑ _x ∈ B, 4 := by simp [Nat.mul_comm]
      _ ≤ ∑ x ∈ B, C.degree x :=
        Finset.sum_le_sum fun x hx => hpointLower x hx
  have htwentyFour : 24 ≤ ∑ x ∈ B, C.degree x := by omega
  have hdisSet : Disjoint (A : Set V) (B : Set V) :=
    Finset.disjoint_coe.mpr hdis
  have hbip : C.IsBipartiteWith (A : Set V) (B : Set V) := by
    simpa [C] using
      (SimpleGraph.between_isBipartiteWith (G := L) hdisSet)
  have hsumA : (∑ a ∈ A, C.degree a) = #C.edgeFinset :=
    SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hbip
  have hsumB : (∑ x ∈ B, C.degree x) = #C.edgeFinset :=
    SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hbip.symm
  have hpointUpper (a : V) (haA : a ∈ A) : C.degree a ≤ 4 := by
    have haccount := degree_neighbor_eq_one_add_internal_add_cross
      L w a (by simpa [A] using haA)
    have haccount' :
        L.degree a =
          1 + (neighborhoodInternalGraph L w).degree a + C.degree a := by
      simpa [C, A, B] using haccount
    have hdegree := hleFive a
    omega
  have hsumUpper : (∑ a ∈ A, C.degree a) ≤ 4 * #A := by
    calc
      (∑ a ∈ A, C.degree a) ≤ ∑ _a ∈ A, 4 :=
        Finset.sum_le_sum fun a ha => hpointUpper a ha
      _ = 4 * #A := by simp [Nat.mul_comm]
  rw [hsumB] at htwentyFour
  rw [hsumA, hAcard] at hsumUpper
  omega

/-- Subtraction-free edge lower bound for a large admissible graph with no
independent triple. -/
theorem choose_card_le_edges_add_twice_card_of_admissible_indepSetFree_three
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 3)
    (hcard : 12 ≤ Fintype.card V) :
    (Fintype.card V).choose 2 ≤
      #G.edgeFinset + 2 * Fintype.card V := by
  classical
  let L := Gᶜ
  have hdegree : ∀ v, L.degree v ≤ 4 := by
    simpa [L] using
      compl_degree_le_four_of_admissible_indepSetFree_three G hG hfree hcard
  have hsumUpper : (∑ v, L.degree v) ≤ 4 * Fintype.card V := by
    calc
      (∑ v, L.degree v) ≤ ∑ _v : V, 4 :=
        Finset.sum_le_sum fun v _ => hdegree v
      _ = 4 * Fintype.card V := by simp [Nat.mul_comm]
  have hhandshake := L.sum_degrees_eq_twice_card_edges
  have hLedges : #L.edgeFinset ≤ 2 * Fintype.card V := by
    rw [hhandshake] at hsumUpper
    omega
  have hpartition := card_edgeFinset_add_card_compl G
  change #G.edgeFinset + #L.edgeFinset =
    (Fintype.card V).choose 2 at hpartition
  omega

end Erdos617
