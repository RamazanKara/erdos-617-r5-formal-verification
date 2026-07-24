/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.AlphaTwoEleven
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Star
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.FinCases

/-!
# The order-ten terminal structure

This file develops the ten-vertex endpoint used by the fixed-`r = 5`
argument.  The finite five-vertex exterior split is checked by transparent
kernel reduction over all 1024 labelled edge vectors; no graph catalog,
solver certificate, native evaluator, or imported extremal classification is
used.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

universe u

/-- The canonical four-cycle together with one isolated vertex. -/
def cycleFourWithIsolate : SimpleGraph (Fin 5) :=
  (SimpleGraph.cycleGraph 4).map Fin.castSuccEmb

/-- The canonical balanced two-fold blow-up of the five-cycle.  Vertices in
the same two-element fibre are twins and are not adjacent. -/
def balancedC5Blowup : SimpleGraph (Fin 5 × Fin 2) :=
  (SimpleGraph.cycleGraph 5).comap Prod.fst

/-- The fixed enumeration of the ten canonical blow-up vertices. -/
def finTenEquivProd : Fin 10 ≃ Fin 5 × Fin 2 :=
  (finProdFinEquiv : Fin 5 × Fin 2 ≃ Fin 10).symm

@[simp] theorem balancedC5Blowup_adj (x y : Fin 5 × Fin 2) :
    balancedC5Blowup.Adj x y ↔
      (SimpleGraph.cycleGraph 5).Adj x.1 y.1 := by
  rfl

/-- The alternating three-part cover beginning at `i`. -/
def balancedC5MinCover (i : Fin 5) : Finset (Fin 5 × Fin 2) :=
  Finset.univ.filter fun v =>
    v.1 = i ∨ v.1 = i + 2 ∨ v.1 = i + 4

/-- Two nonadjacent fibres forming a canonical independent four-set. -/
def balancedC5MaxIndep : Finset (Fin 5 × Fin 2) :=
  Finset.univ.filter fun v => v.1 = 0 ∨ v.1 = 2

theorem balancedC5MaxIndep_card : #balancedC5MaxIndep = 4 := by
  decide

theorem balancedC5MaxIndep_index_check :
    ∀ a b : Fin 5, (a = 0 ∨ a = 2) → (b = 0 ∨ b = 2) →
      ¬(SimpleGraph.cycleGraph 5).Adj a b := by
  decide

theorem balancedC5MaxIndep_isIndepSet :
    balancedC5Blowup.IsIndepSet
      (balancedC5MaxIndep : Set (Fin 5 × Fin 2)) := by
  intro x hx y hy _hxy hAdj
  have hx' : x.1 = 0 ∨ x.1 = 2 := by simpa [balancedC5MaxIndep] using hx
  have hy' : y.1 = 0 ∨ y.1 = 2 := by simpa [balancedC5MaxIndep] using hy
  exact balancedC5MaxIndep_index_check x.1 y.1 hx' hy' hAdj

theorem balancedC5MinCover_card (i : Fin 5) : #(balancedC5MinCover i) = 6 := by
  fin_cases i <;> decide

theorem balancedC5MinCover_index_check :
    ∀ i a b : Fin 5, (SimpleGraph.cycleGraph 5).Adj a b →
      (a = i ∨ a = i + 2 ∨ a = i + 4) ∨
      (b = i ∨ b = i + 2 ∨ b = i + 4) := by
  decide

theorem balancedC5MinCover_isVertexCover (i : Fin 5) :
    balancedC5Blowup.IsVertexCover (balancedC5MinCover i : Set _) := by
  intro x y hxy
  have hindex := balancedC5MinCover_index_check i x.1 y.1 hxy
  simpa [balancedC5MinCover] using hindex

/-- Enumerate uniformly two-element fibres without making the enumeration
part of any theorem statement. -/
noncomputable def equivProdOfFiberCardTwo
    {V : Type u} [Fintype V] (part : V → Fin 5)
    (hcard : ∀ i, Fintype.card {v // part v = i} = 2) :
    V ≃ Fin 5 × Fin 2 :=
  (Equiv.sigmaFiberEquiv part).symm.trans
    (Equiv.sigmaEquivProdOfEquiv fun i =>
      Fintype.equivFinOfCardEq (hcard i))

@[simp] theorem equivProdOfFiberCardTwo_fst
    {V : Type u} [Fintype V] (part : V → Fin 5)
    (hcard : ∀ i, Fintype.card {v // part v = i} = 2) (v : V) :
    (equivProdOfFiberCardTwo part hcard v).1 = part v := by
  rfl

/-- A five-cycle labelling with two vertices in every fibre induces an
isomorphism with the canonical balanced blow-up. -/
noncomputable def isoBalancedC5BlowupOfPart
    {V : Type u} [Fintype V]
    (L : SimpleGraph V) (part : V → Fin 5)
    (hcard : ∀ i, Fintype.card {v // part v = i} = 2)
    (hadj : ∀ x y, L.Adj x y ↔
      (SimpleGraph.cycleGraph 5).Adj (part x) (part y)) :
    L ≃g balancedC5Blowup where
  __ := equivProdOfFiberCardTwo part hcard
  map_rel_iff' := by
    intro x y
    simp only [balancedC5Blowup_adj, equivProdOfFiberCardTwo_fst]
    exact (hadj x y).symm

/-- Two disjoint independent finsets covering the vertices are a bipartition. -/
theorem isBipartiteWith_of_independent_partition
    {V : Type u} [Fintype V] [DecidableEq V]
    (L : SimpleGraph V) (X Y : Finset V)
    (hdis : Disjoint X Y) (hcover : X ∪ Y = Finset.univ)
    (hX : L.IsIndepSet (X : Set V))
    (hY : L.IsIndepSet (Y : Set V)) :
    L.IsBipartiteWith (X : Set V) (Y : Set V) := by
  refine ⟨Finset.disjoint_coe.mpr hdis, ?_⟩
  intro x y hxy
  have hx : x ∈ X ∨ x ∈ Y := by
    have : x ∈ X ∪ Y := by rw [hcover]; simp
    simpa using this
  have hy : y ∈ X ∨ y ∈ Y := by
    have : y ∈ X ∪ Y := by rw [hcover]; simp
    simpa using this
  rcases hx with hxX | hxY
  · have hyY : y ∈ Y := by
      rcases hy with hyX | hyY
      · exact (hX hxX hyX hxy.ne hxy).elim
      · exact hyY
    exact Or.inl ⟨hxX, hyY⟩
  · have hyX : y ∈ X := by
      rcases hy with hyX | hyY
      · exact hyX
      · exact (hY hxY hyY hxy.ne hxy).elim
    exact Or.inr ⟨hxY, hyX⟩

/-- The index of the unique member of a labelled five-part partition. -/
noncomputable def labelOfUniqueFiveParts
    {V : Type u} [DecidableEq V] (P : Fin 5 → Finset V)
    (hunique : ∀ v, ∃! i, v ∈ P i) (v : V) : Fin 5 :=
  (hunique v).choose

theorem labelOfUniqueFiveParts_mem
    {V : Type u} [DecidableEq V] (P : Fin 5 → Finset V)
    (hunique : ∀ v, ∃! i, v ∈ P i) (v : V) :
    v ∈ P (labelOfUniqueFiveParts P hunique v) :=
  (hunique v).choose_spec.1

theorem labelOfUniqueFiveParts_eq_iff
    {V : Type u} [DecidableEq V] (P : Fin 5 → Finset V)
    (hunique : ∀ v, ∃! i, v ∈ P i) (v : V) (i : Fin 5) :
    labelOfUniqueFiveParts P hunique v = i ↔ v ∈ P i := by
  constructor
  · intro h
    rw [← h]
    exact labelOfUniqueFiveParts_mem P hunique v
  · intro h
    exact ((hunique v).choose_spec.2 i h).symm

/-- Five pairwise-disjoint two-element parts with five-cycle adjacency give
the canonical balanced blow-up. -/
noncomputable def isoBalancedC5BlowupOfFiveParts
    {V : Type u} [Fintype V] [DecidableEq V]
    (L : SimpleGraph V) (P : Fin 5 → Finset V)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (hcover : ∀ v, ∃ i, v ∈ P i)
    (hcard : ∀ i, #(P i) = 2)
    (hadj : ∀ i j x, x ∈ P i → ∀ y, y ∈ P j →
      (L.Adj x y ↔ (SimpleGraph.cycleGraph 5).Adj i j)) :
    L ≃g balancedC5Blowup := by
  have hunique : ∀ v, ∃! i, v ∈ P i := by
    intro v
    obtain ⟨i, hi⟩ := hcover v
    refine ⟨i, hi, ?_⟩
    intro j hj
    by_contra hij
    exact (Finset.disjoint_left.mp (hdis hij)) hj hi
  let part : V → Fin 5 := labelOfUniqueFiveParts P hunique
  have hpartMem (v : V) : v ∈ P (part v) := by
    exact labelOfUniqueFiveParts_mem P hunique v
  have hfiber : ∀ i, Fintype.card {v // part v = i} = 2 := by
    intro i
    let e : {v // part v = i} ≃ (P i : Set V) :=
      { toFun := fun v =>
          ⟨v, (labelOfUniqueFiveParts_eq_iff P hunique v i).mp v.property⟩
        invFun := fun v =>
          ⟨v, (labelOfUniqueFiveParts_eq_iff P hunique v i).mpr v.property⟩
        left_inv := by intro v; ext; rfl
        right_inv := by intro v; ext; rfl }
    calc
      Fintype.card {v // part v = i} = Fintype.card (P i : Set V) :=
        Fintype.card_congr e
      _ = #(P i) := by simp
      _ = 2 := hcard i
  apply isoBalancedC5BlowupOfPart L part hfiber
  intro x y
  exact hadj (part x) (part y) x (hpartMem x) y (hpartMem y)

/-- The degree of vertex zero expanded over the other four vertices. -/
theorem fin_five_degree_zero_formula
    (H : SimpleGraph (Fin 5)) [DecidableRel H.Adj] :
    H.degree 0 =
      (if H.Adj 0 1 then 1 else 0) + (if H.Adj 0 2 then 1 else 0) +
      (if H.Adj 0 3 then 1 else 0) + (if H.Adj 0 4 then 1 else 0) := by
  rw [SimpleGraph.degree]
  have hneighbors : H.neighborFinset 0 =
      ({1, 2, 3, 4} : Finset (Fin 5)).filter (H.Adj 0) := by
    ext x
    fin_cases x <;> simp
  rw [hneighbors]
  by_cases h01 : H.Adj 0 1 <;>
  by_cases h02 : H.Adj 0 2 <;>
  by_cases h03 : H.Adj 0 3 <;>
  by_cases h04 : H.Adj 0 4 <;>
  all_goals simp [Finset.filter_insert, Finset.filter_singleton, h01, h02, h03, h04]

/-- The degree of vertex one expanded over the other four vertices. -/
theorem fin_five_degree_one_formula
    (H : SimpleGraph (Fin 5)) [DecidableRel H.Adj] :
    H.degree 1 =
      (if H.Adj 0 1 then 1 else 0) + (if H.Adj 1 2 then 1 else 0) +
      (if H.Adj 1 3 then 1 else 0) + (if H.Adj 1 4 then 1 else 0) := by
  rw [SimpleGraph.degree]
  have hneighbors : H.neighborFinset 1 =
      ({0, 2, 3, 4} : Finset (Fin 5)).filter (H.Adj 1) := by
    ext x
    fin_cases x <;> simp
  rw [hneighbors]
  by_cases h01 : H.Adj 0 1 <;>
  by_cases h12 : H.Adj 1 2 <;>
  by_cases h13 : H.Adj 1 3 <;>
  by_cases h14 : H.Adj 1 4 <;>
  all_goals simp [Finset.filter_insert, Finset.filter_singleton,
    H.adj_comm, h01, h12, h13, h14]

/-- The degree of vertex two expanded over the other four vertices. -/
theorem fin_five_degree_two_formula
    (H : SimpleGraph (Fin 5)) [DecidableRel H.Adj] :
    H.degree 2 =
      (if H.Adj 0 2 then 1 else 0) + (if H.Adj 1 2 then 1 else 0) +
      (if H.Adj 2 3 then 1 else 0) + (if H.Adj 2 4 then 1 else 0) := by
  rw [SimpleGraph.degree]
  have hneighbors : H.neighborFinset 2 =
      ({0, 1, 3, 4} : Finset (Fin 5)).filter (H.Adj 2) := by
    ext x
    fin_cases x <;> simp
  rw [hneighbors]
  by_cases h02 : H.Adj 0 2 <;>
  by_cases h12 : H.Adj 1 2 <;>
  by_cases h23 : H.Adj 2 3 <;>
  by_cases h24 : H.Adj 2 4 <;>
  all_goals simp [Finset.filter_insert, Finset.filter_singleton,
    H.adj_comm, h02, h12, h23, h24]

/-- The degree of vertex three expanded over the other four vertices. -/
theorem fin_five_degree_three_formula
    (H : SimpleGraph (Fin 5)) [DecidableRel H.Adj] :
    H.degree 3 =
      (if H.Adj 0 3 then 1 else 0) + (if H.Adj 1 3 then 1 else 0) +
      (if H.Adj 2 3 then 1 else 0) + (if H.Adj 3 4 then 1 else 0) := by
  rw [SimpleGraph.degree]
  have hneighbors : H.neighborFinset 3 =
      ({0, 1, 2, 4} : Finset (Fin 5)).filter (H.Adj 3) := by
    ext x
    fin_cases x <;> simp
  rw [hneighbors]
  by_cases h03 : H.Adj 0 3 <;>
  by_cases h13 : H.Adj 1 3 <;>
  by_cases h23 : H.Adj 2 3 <;>
  by_cases h34 : H.Adj 3 4 <;>
  all_goals simp [Finset.filter_insert, Finset.filter_singleton,
    H.adj_comm, h03, h13, h23, h34]

/-- The degree of vertex four expanded over the other four vertices. -/
theorem fin_five_degree_four_formula
    (H : SimpleGraph (Fin 5)) [DecidableRel H.Adj] :
    H.degree 4 =
      (if H.Adj 0 4 then 1 else 0) + (if H.Adj 1 4 then 1 else 0) +
      (if H.Adj 2 4 then 1 else 0) + (if H.Adj 3 4 then 1 else 0) := by
  rw [SimpleGraph.degree]
  have hneighbors : H.neighborFinset 4 =
      ({0, 1, 2, 3} : Finset (Fin 5)).filter (H.Adj 4) := by
    ext x
    fin_cases x <;> simp
  rw [hneighbors]
  by_cases h04 : H.Adj 0 4 <;>
  by_cases h14 : H.Adj 1 4 <;>
  by_cases h24 : H.Adj 2 4 <;>
  by_cases h34 : H.Adj 3 4 <;>
  all_goals simp [Finset.filter_insert, Finset.filter_singleton,
    H.adj_comm, h04, h14, h24, h34]

/-- Convert one Boolean edge bit to its contribution to a degree. -/
def edgeBit (b : Bool) : ℕ := if b then 1 else 0

/-- The five vertex degrees determined by the ten upper-triangular edge bits. -/
def edgeBitsDegree (e : Fin 10 → Bool) : Fin 5 → ℕ :=
  ![edgeBit (e 0) + edgeBit (e 1) + edgeBit (e 2) + edgeBit (e 3),
    edgeBit (e 0) + edgeBit (e 4) + edgeBit (e 5) + edgeBit (e 6),
    edgeBit (e 1) + edgeBit (e 4) + edgeBit (e 7) + edgeBit (e 8),
    edgeBit (e 2) + edgeBit (e 5) + edgeBit (e 7) + edgeBit (e 9),
    edgeBit (e 3) + edgeBit (e 6) + edgeBit (e 8) + edgeBit (e 9)]

theorem bool_not_three_and_eq_true_iff (a b c : Bool) :
    ((!(a && b && c)) = true) ↔ ¬(a = true ∧ b = true ∧ c = true) := by
  cases a <;> cases b <;> cases c <;> decide

theorem bool_edge_condition_eq_true_iff
    (b : Bool) (p : Prop) [Decidable p] :
    ((!b || decide p) = true) ↔ (b = true → p) := by
  cases b <;> simp

/-- The finite Boolean proposition behind the five-vertex exterior lemma. -/
def fiveEdgeBitsDegreeProperty (e : Fin 10 → Bool) : Prop :=
    let e01 := e 0; let e02 := e 1; let e03 := e 2; let e04 := e 3
    let e12 := e 4; let e13 := e 5; let e14 := e 6
    let e23 := e 7; let e24 := e 8; let e34 := e 9
    let d0 := edgeBitsDegree e 0
    let d1 := edgeBitsDegree e 1
    let d2 := edgeBitsDegree e 2
    let d3 := edgeBitsDegree e 3
    let d4 := edgeBitsDegree e 4
    (¬(e01 = true ∧ e02 = true ∧ e12 = true)) ∧
    (¬(e01 = true ∧ e03 = true ∧ e13 = true)) ∧
    (¬(e01 = true ∧ e04 = true ∧ e14 = true)) ∧
    (¬(e02 = true ∧ e03 = true ∧ e23 = true)) ∧
    (¬(e02 = true ∧ e04 = true ∧ e24 = true)) ∧
    (¬(e03 = true ∧ e04 = true ∧ e34 = true)) ∧
    (¬(e12 = true ∧ e13 = true ∧ e23 = true)) ∧
    (¬(e12 = true ∧ e14 = true ∧ e24 = true)) ∧
    (¬(e13 = true ∧ e14 = true ∧ e34 = true)) ∧
    (¬(e23 = true ∧ e24 = true ∧ e34 = true)) →
    d0 + d1 + d2 + d3 + d4 = 8 →
    (e01 = true → 4 ≤ d0 + d1) ∧
    (e02 = true → 4 ≤ d0 + d2) ∧
    (e03 = true → 4 ≤ d0 + d3) ∧
    (e04 = true → 4 ≤ d0 + d4) ∧
    (e12 = true → 4 ≤ d1 + d2) ∧
    (e13 = true → 4 ≤ d1 + d3) ∧
    (e14 = true → 4 ≤ d1 + d4) ∧
    (e23 = true → 4 ≤ d2 + d3) ∧
    (e24 = true → 4 ≤ d2 + d4) ∧
    (e34 = true → 4 ≤ d3 + d4) →
    d0 = 4 ∨ d1 = 4 ∨ d2 = 4 ∨ d3 = 4 ∨ d4 = 4 ∨
    (d0 = 0 ∧ d1 = 2 ∧ d2 = 2 ∧ d3 = 2 ∧ d4 = 2) ∨
    (d1 = 0 ∧ d0 = 2 ∧ d2 = 2 ∧ d3 = 2 ∧ d4 = 2) ∨
    (d2 = 0 ∧ d0 = 2 ∧ d1 = 2 ∧ d3 = 2 ∧ d4 = 2) ∨
    (d3 = 0 ∧ d0 = 2 ∧ d1 = 2 ∧ d2 = 2 ∧ d4 = 2) ∨
    (d4 = 0 ∧ d0 = 2 ∧ d1 = 2 ∧ d2 = 2 ∧ d3 = 2)

/-- Executable decision procedure for the finite exterior proposition. -/
def fiveEdgeBitsDegreeCheck (e : Fin 10 → Bool) : Bool :=
  let e01 := e 0; let e02 := e 1; let e03 := e 2; let e04 := e 3
  let e12 := e 4; let e13 := e 5; let e14 := e 6
  let e23 := e 7; let e24 := e 8; let e34 := e 9
  let d0 := edgeBitsDegree e 0
  let d1 := edgeBitsDegree e 1
  let d2 := edgeBitsDegree e 2
  let d3 := edgeBitsDegree e 3
  let d4 := edgeBitsDegree e 4
  let triangleOK :=
    !(e01 && e02 && e12) && !(e01 && e03 && e13) &&
    !(e01 && e04 && e14) && !(e02 && e03 && e23) &&
    !(e02 && e04 && e24) && !(e03 && e04 && e34) &&
    !(e12 && e13 && e23) && !(e12 && e14 && e24) &&
    !(e13 && e14 && e34) && !(e23 && e24 && e34)
  let edgeOK :=
    (!e01 || decide (4 ≤ d0 + d1)) && (!e02 || decide (4 ≤ d0 + d2)) &&
    (!e03 || decide (4 ≤ d0 + d3)) && (!e04 || decide (4 ≤ d0 + d4)) &&
    (!e12 || decide (4 ≤ d1 + d2)) && (!e13 || decide (4 ≤ d1 + d3)) &&
    (!e14 || decide (4 ≤ d1 + d4)) && (!e23 || decide (4 ≤ d2 + d3)) &&
    (!e24 || decide (4 ≤ d2 + d4)) && (!e34 || decide (4 ≤ d3 + d4))
  let patternOK :=
    decide (d0 = 4) || decide (d1 = 4) || decide (d2 = 4) ||
    decide (d3 = 4) || decide (d4 = 4) ||
    (decide (d0 = 0) && decide (d1 = 2) && decide (d2 = 2) &&
      decide (d3 = 2) && decide (d4 = 2)) ||
    (decide (d1 = 0) && decide (d0 = 2) && decide (d2 = 2) &&
      decide (d3 = 2) && decide (d4 = 2)) ||
    (decide (d2 = 0) && decide (d0 = 2) && decide (d1 = 2) &&
      decide (d3 = 2) && decide (d4 = 2)) ||
    (decide (d3 = 0) && decide (d0 = 2) && decide (d1 = 2) &&
      decide (d2 = 2) && decide (d4 = 2)) ||
    (decide (d4 = 0) && decide (d0 = 2) && decide (d1 = 2) &&
      decide (d2 = 2) && decide (d3 = 2))
  !triangleOK || !(decide (d0 + d1 + d2 + d3 + d4 = 8)) || !edgeOK || patternOK

/-- Encode one Boolean as a binary digit. -/
def boolToFinTwo : Bool → Fin 2
  | false => 0
  | true => 1

/-- Decode a binary digit as a Boolean. -/
def finTwoToBool (i : Fin 2) : Bool := decide (i = 1)

@[simp] theorem finTwoToBool_boolToFinTwo (b : Bool) :
    finTwoToBool (boolToFinTwo b) = b := by
  cases b <;> decide

/-- Decode the compact base-two code used by the exhaustive certificate. -/
def edgeVectorOfCode (n : Fin (2 ^ 10)) : Fin 10 → Bool := fun i =>
  finTwoToBool ((finFunctionFinEquiv.symm n) i)

set_option maxRecDepth 10000 in
/-- Exhaustive compact-code certificate.  This checks the 1024 binary codes
without materializing the much larger `Fintype` representation of functions. -/
theorem five_edge_bits_degree_code_check :
    ∀ n : Fin (2 ^ 10), fiveEdgeBitsDegreeCheck (edgeVectorOfCode n) = true := by
  decide

/-- Every labelled ten-bit edge vector is covered by the compact certificate. -/
theorem five_edge_bits_degree_check (e : Fin 10 → Bool) :
    fiveEdgeBitsDegreeCheck e = true := by
  let f : Fin 10 → Fin 2 := fun i => boolToFinTwo (e i)
  let n : Fin (2 ^ 10) := finFunctionFinEquiv f
  have hcheck := five_edge_bits_degree_code_check n
  have hdecode : edgeVectorOfCode n = e := by
    funext i
    simp [edgeVectorOfCode, n, f]
  rw [hdecode] at hcheck
  exact hcheck

/-- The subset-mask proposition used to certify the independence number of
the canonical blow-up. -/
def fiveSubsetBitsProperty (e : Fin 10 → Bool) : Prop :=
  (∑ i, edgeBit (e i)) = 5 →
    ∃ i, e i = true ∧ ∃ j, e j = true ∧ i ≠ j ∧
      (SimpleGraph.cycleGraph 5).Adj
        (finTenEquivProd i).1 (finTenEquivProd j).1

set_option maxRecDepth 10000 in
/-- Transparent compact-code check of all 1024 subset masks. -/
theorem five_subset_bits_code_check :
    ∀ n : Fin (2 ^ 10), fiveSubsetBitsProperty (edgeVectorOfCode n) := by
  dsimp only [fiveSubsetBitsProperty]
  decide

/-- Every labelled ten-bit subset mask is covered by the compact check. -/
theorem five_subset_bits_check (e : Fin 10 → Bool) :
    fiveSubsetBitsProperty e := by
  let f : Fin 10 → Fin 2 := fun i => boolToFinTwo (e i)
  let n : Fin (2 ^ 10) := finFunctionFinEquiv f
  have hcheck := five_subset_bits_code_check n
  have hdecode : edgeVectorOfCode n = e := by
    funext i
    simp [edgeVectorOfCode, n, f]
  rw [hdecode] at hcheck
  exact hcheck

/-- The subset-mask proposition classifying six-vertex covers of the
canonical blow-up. -/
def sixCoverBitsProperty (e : Fin 10 → Bool) : Prop :=
  (∑ i, edgeBit (e i)) = 6 →
    (∀ i j, (SimpleGraph.cycleGraph 5).Adj
      (finTenEquivProd i).1 (finTenEquivProd j).1 →
      e i = true ∨ e j = true) →
    ∃ k : Fin 5, ∀ i,
      e i = true ↔
        (finTenEquivProd i).1 = k ∨
        (finTenEquivProd i).1 = k + 2 ∨
        (finTenEquivProd i).1 = k + 4

set_option maxRecDepth 10000 in
/-- Transparent compact-code classification of all 1024 subset masks. -/
theorem six_cover_bits_code_check :
    ∀ n : Fin (2 ^ 10), sixCoverBitsProperty (edgeVectorOfCode n) := by
  dsimp only [sixCoverBitsProperty]
  decide

/-- Every labelled ten-bit cover mask is covered by the compact check. -/
theorem six_cover_bits_check (e : Fin 10 → Bool) :
    sixCoverBitsProperty e := by
  let f : Fin 10 → Fin 2 := fun i => boolToFinTwo (e i)
  let n : Fin (2 ^ 10) := finFunctionFinEquiv f
  have hcheck := six_cover_bits_code_check n
  have hdecode : edgeVectorOfCode n = e := by
    funext i
    simp [edgeVectorOfCode, n, f]
  rw [hdecode] at hcheck
  exact hcheck

/-- Membership-bit sums are finset cardinalities under the fixed ten-vertex
enumeration. -/
theorem sum_membership_bits_eq_card (S : Finset (Fin 5 × Fin 2)) :
    (∑ i : Fin 10, edgeBit (decide (finTenEquivProd i ∈ S))) = #S := by
  calc
    (∑ i : Fin 10, edgeBit (decide (finTenEquivProd i ∈ S))) =
        ∑ i : Fin 10, if finTenEquivProd i ∈ S then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp [edgeBit]
    _ = ∑ v : Fin 5 × Fin 2, if v ∈ S then 1 else 0 :=
      Equiv.sum_comp finTenEquivProd
        (fun v : Fin 5 × Fin 2 => if v ∈ S then 1 else 0)
    _ = #S := by simp

/-- The canonical blow-up has no independent five-set. -/
theorem balancedC5Blowup_indepSetFree_five :
    balancedC5Blowup.IndepSetFree 5 := by
  intro S hS
  let e : Fin 10 → Bool := fun i => decide (finTenEquivProd i ∈ S)
  have hsum : (∑ i, edgeBit (e i)) = 5 := by
    calc
      (∑ i, edgeBit (e i)) =
          ∑ i : Fin 10, if finTenEquivProd i ∈ S then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        simp [e, edgeBit]
      _ =
          ∑ v : Fin 5 × Fin 2, if v ∈ S then 1 else 0 := by
        exact Equiv.sum_comp finTenEquivProd
          (fun v : Fin 5 × Fin 2 => if v ∈ S then 1 else 0)
      _ = #S := by simp
      _ = 5 := hS.card_eq
  obtain ⟨i, hi, j, hj, hij, hadj⟩ := five_subset_bits_check e hsum
  have hiS : finTenEquivProd i ∈ S := by simpa [e] using hi
  have hjS : finTenEquivProd j ∈ S := by simpa [e] using hj
  have hne : finTenEquivProd i ≠ finTenEquivProd j :=
    fun h => hij (finTenEquivProd.injective h)
  exact hS.isIndepSet hiS hjS hne (show balancedC5Blowup.Adj
    (finTenEquivProd i) (finTenEquivProd j) from hadj)

/-- The canonical balanced blow-up has independence number exactly four. -/
theorem balancedC5Blowup_indepNum : balancedC5Blowup.indepNum = 4 := by
  have hmaximum : balancedC5Blowup.IsMaximumIndepSet balancedC5MaxIndep := by
    refine ⟨balancedC5MaxIndep_isIndepSet, ?_⟩
    intro T hT
    by_contra hnot
    have hfive : 5 ≤ #T := by
      rw [balancedC5MaxIndep_card] at hnot
      omega
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hfive
    have hSind : balancedC5Blowup.IsIndepSet (S : Set (Fin 5 × Fin 2)) := by
      intro x hx y hy hxy
      exact hT (hSsub hx) (hSsub hy) hxy
    exact balancedC5Blowup_indepSetFree_five S ⟨hSind, hScard⟩
  have hcard := balancedC5Blowup.maximumIndepSet_card_eq_indepNum
    balancedC5MaxIndep hmaximum
  simpa [balancedC5MaxIndep_card] using hcard.symm

/-- The six-vertex covers of the canonical blow-up are exactly the five
alternating unions of whole two-vertex fibres. -/
theorem balancedC5Blowup_six_cover_iff
    (S : Finset (Fin 5 × Fin 2)) (hcard : #S = 6) :
    balancedC5Blowup.IsVertexCover (S : Set _) ↔
      ∃ i : Fin 5, S = balancedC5MinCover i := by
  constructor
  · intro hcover
    let e : Fin 10 → Bool := fun i => decide (finTenEquivProd i ∈ S)
    have hsum : (∑ i, edgeBit (e i)) = 6 := by
      simpa [e, hcard] using sum_membership_bits_eq_card S
    have hcoverBits : ∀ i j,
        (SimpleGraph.cycleGraph 5).Adj
          (finTenEquivProd i).1 (finTenEquivProd j).1 →
        e i = true ∨ e j = true := by
      intro i j hij
      have h := hcover (show balancedC5Blowup.Adj
        (finTenEquivProd i) (finTenEquivProd j) from hij)
      rcases h with hi | hj
      · exact Or.inl (by simpa [e] using hi)
      · exact Or.inr (by simpa [e] using hj)
    obtain ⟨k, hk⟩ := six_cover_bits_check e hsum hcoverBits
    refine ⟨k, Finset.ext ?_⟩
    intro v
    let i : Fin 10 := finTenEquivProd.symm v
    have hi := hk i
    have hivi : finTenEquivProd i = v := finTenEquivProd.apply_symm_apply v
    simpa [e, i, hivi, balancedC5MinCover] using hi
  · rintro ⟨i, rfl⟩
    exact balancedC5MinCover_isVertexCover i

/-- Every finite vertex cover of the canonical blow-up has at least six
vertices. -/
theorem six_le_card_of_balancedC5Blowup_vertexCover
    (S : Finset (Fin 5 × Fin 2))
    (hcover : balancedC5Blowup.IsVertexCover (S : Set _)) :
    6 ≤ #S := by
  by_contra hnot
  have hcompIndSet : balancedC5Blowup.IsIndepSet
      ((Sᶜ : Finset (Fin 5 × Fin 2)) : Set _) := by
    have hraw :=
      (SimpleGraph.isIndepSet_compl_iff_isVertexCover (G := balancedC5Blowup)).2
        hcover
    simpa using hraw
  have hcompCard : 5 ≤ #(Sᶜ : Finset (Fin 5 × Fin 2)) := by
    rw [Finset.card_compl]
    have htype : Fintype.card (Fin 5 × Fin 2) = 10 := by decide
    rw [htype]
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcompCard
  have hTind : balancedC5Blowup.IsIndepSet (T : Set _) := by
    intro x hx y hy hxy
    exact hcompIndSet (hTsub hx) (hTsub hy) hxy
  exact balancedC5Blowup_indepSetFree_five T ⟨hTind, hTcard⟩

/-- The vertex-cover number of the canonical blow-up is exactly six. -/
theorem balancedC5Blowup_vertexCoverNum :
    balancedC5Blowup.vertexCoverNum = 6 := by
  have hupper : balancedC5Blowup.vertexCoverNum ≤ (6 : ℕ∞) := by
    have h := (balancedC5MinCover_isVertexCover 0).vertexCoverNum_le
    simpa [balancedC5MinCover_card] using h
  obtain ⟨s, hsnum, hscover⟩ :=
    SimpleGraph.vertexCoverNum_exists balancedC5Blowup
  let hsfinite : s.Finite := Set.toFinite s
  let S : Finset (Fin 5 × Fin 2) := hsfinite.toFinset
  have hScover : balancedC5Blowup.IsVertexCover (S : Set _) := by
    simpa [S, hsfinite] using hscover
  have hSixNat : 6 ≤ #S :=
    six_le_card_of_balancedC5Blowup_vertexCover S hScover
  have hlower : (6 : ℕ∞) ≤ balancedC5Blowup.vertexCoverNum := by
    rw [← hsnum, hsfinite.encard_eq_coe_toFinset_card]
    exact_mod_cast hSixNat
  exact le_antisymm hupper hlower

theorem balancedC5MinCover_inter_card_check :
    ∀ i j : Fin 5, i ≠ j →
      #(balancedC5MinCover i ∩ balancedC5MinCover j) ≤ 4 := by
  decide

/-- Two distinct minimum covers of the canonical blow-up intersect in at
most four vertices. -/
theorem balancedC5Blowup_distinct_min_covers_inter_card_le_four
    (S T : Finset (Fin 5 × Fin 2))
    (hScard : #S = 6) (hScover : balancedC5Blowup.IsVertexCover (S : Set _))
    (hTcard : #T = 6) (hTcover : balancedC5Blowup.IsVertexCover (T : Set _))
    (hne : S ≠ T) : #(S ∩ T) ≤ 4 := by
  obtain ⟨i, hi⟩ := (balancedC5Blowup_six_cover_iff S hScard).mp hScover
  obtain ⟨j, hj⟩ := (balancedC5Blowup_six_cover_iff T hTcard).mp hTcover
  have hij : i ≠ j := by
    intro hij
    apply hne
    rw [hi, hj, hij]
  rw [hi, hj]
  exact balancedC5MinCover_inter_card_check i j hij

/-- Propositional form of the exhaustive five-vertex certificate. -/
theorem five_edge_bits_degree_structure :
    ∀ e : Fin 10 → Bool, fiveEdgeBitsDegreeProperty e := by
  intro e
  dsimp [fiveEdgeBitsDegreeProperty]
  intro htri hsum hedge
  rcases htri with ⟨ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9⟩
  rcases hedge with ⟨he0, he1, he2, he3, he4, he5, he6, he7, he8, he9⟩
  have hcheck := five_edge_bits_degree_check e
  dsimp [fiveEdgeBitsDegreeCheck] at hcheck
  have htriangleOK :
      (!(e 0 && e 1 && e 4) && !(e 0 && e 2 && e 5) &&
      !(e 0 && e 3 && e 6) && !(e 1 && e 2 && e 7) &&
      !(e 1 && e 3 && e 8) && !(e 2 && e 3 && e 9) &&
      !(e 4 && e 5 && e 7) && !(e 4 && e 6 && e 8) &&
      !(e 5 && e 6 && e 9) && !(e 7 && e 8 && e 9)) = true := by
    have hb0 := (bool_not_three_and_eq_true_iff _ _ _).2 ht0
    have hb1 := (bool_not_three_and_eq_true_iff _ _ _).2 ht1
    have hb2 := (bool_not_three_and_eq_true_iff _ _ _).2 ht2
    have hb3 := (bool_not_three_and_eq_true_iff _ _ _).2 ht3
    have hb4 := (bool_not_three_and_eq_true_iff _ _ _).2 ht4
    have hb5 := (bool_not_three_and_eq_true_iff _ _ _).2 ht5
    have hb6 := (bool_not_three_and_eq_true_iff _ _ _).2 ht6
    have hb7 := (bool_not_three_and_eq_true_iff _ _ _).2 ht7
    have hb8 := (bool_not_three_and_eq_true_iff _ _ _).2 ht8
    have hb9 := (bool_not_three_and_eq_true_iff _ _ _).2 ht9
    simpa only [Bool.and_eq_true_iff, and_assoc] using
      (show ((!(e 0 && e 1 && e 4)) = true) ∧
        ((!(e 0 && e 2 && e 5)) = true) ∧
        ((!(e 0 && e 3 && e 6)) = true) ∧
        ((!(e 1 && e 2 && e 7)) = true) ∧
        ((!(e 1 && e 3 && e 8)) = true) ∧
        ((!(e 2 && e 3 && e 9)) = true) ∧
        ((!(e 4 && e 5 && e 7)) = true) ∧
        ((!(e 4 && e 6 && e 8)) = true) ∧
        ((!(e 5 && e 6 && e 9)) = true) ∧
        ((!(e 7 && e 8 && e 9)) = true) from
        ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9⟩)
  have hsumOK : decide
      (edgeBitsDegree e 0 + edgeBitsDegree e 1 + edgeBitsDegree e 2 +
        edgeBitsDegree e 3 + edgeBitsDegree e 4 = 8) = true :=
    decide_eq_true hsum
  have hedgeOK :
      ((!(e 0) || decide (4 ≤ edgeBitsDegree e 0 + edgeBitsDegree e 1)) &&
      (!(e 1) || decide (4 ≤ edgeBitsDegree e 0 + edgeBitsDegree e 2)) &&
      (!(e 2) || decide (4 ≤ edgeBitsDegree e 0 + edgeBitsDegree e 3)) &&
      (!(e 3) || decide (4 ≤ edgeBitsDegree e 0 + edgeBitsDegree e 4)) &&
      (!(e 4) || decide (4 ≤ edgeBitsDegree e 1 + edgeBitsDegree e 2)) &&
      (!(e 5) || decide (4 ≤ edgeBitsDegree e 1 + edgeBitsDegree e 3)) &&
      (!(e 6) || decide (4 ≤ edgeBitsDegree e 1 + edgeBitsDegree e 4)) &&
      (!(e 7) || decide (4 ≤ edgeBitsDegree e 2 + edgeBitsDegree e 3)) &&
      (!(e 8) || decide (4 ≤ edgeBitsDegree e 2 + edgeBitsDegree e 4)) &&
      (!(e 9) || decide (4 ≤ edgeBitsDegree e 3 + edgeBitsDegree e 4))) = true := by
    have hb0 := (bool_edge_condition_eq_true_iff _ _).2 he0
    have hb1 := (bool_edge_condition_eq_true_iff _ _).2 he1
    have hb2 := (bool_edge_condition_eq_true_iff _ _).2 he2
    have hb3 := (bool_edge_condition_eq_true_iff _ _).2 he3
    have hb4 := (bool_edge_condition_eq_true_iff _ _).2 he4
    have hb5 := (bool_edge_condition_eq_true_iff _ _).2 he5
    have hb6 := (bool_edge_condition_eq_true_iff _ _).2 he6
    have hb7 := (bool_edge_condition_eq_true_iff _ _).2 he7
    have hb8 := (bool_edge_condition_eq_true_iff _ _).2 he8
    have hb9 := (bool_edge_condition_eq_true_iff _ _).2 he9
    simpa only [Bool.and_eq_true_iff, and_assoc] using
      (show
        ((!(e 0) || decide (4 ≤ edgeBitsDegree e 0 + edgeBitsDegree e 1)) = true) ∧
        ((!(e 1) || decide (4 ≤ edgeBitsDegree e 0 + edgeBitsDegree e 2)) = true) ∧
        ((!(e 2) || decide (4 ≤ edgeBitsDegree e 0 + edgeBitsDegree e 3)) = true) ∧
        ((!(e 3) || decide (4 ≤ edgeBitsDegree e 0 + edgeBitsDegree e 4)) = true) ∧
        ((!(e 4) || decide (4 ≤ edgeBitsDegree e 1 + edgeBitsDegree e 2)) = true) ∧
        ((!(e 5) || decide (4 ≤ edgeBitsDegree e 1 + edgeBitsDegree e 3)) = true) ∧
        ((!(e 6) || decide (4 ≤ edgeBitsDegree e 1 + edgeBitsDegree e 4)) = true) ∧
        ((!(e 7) || decide (4 ≤ edgeBitsDegree e 2 + edgeBitsDegree e 3)) = true) ∧
        ((!(e 8) || decide (4 ≤ edgeBitsDegree e 2 + edgeBitsDegree e 4)) = true) ∧
        ((!(e 9) || decide (4 ≤ edgeBitsDegree e 3 + edgeBitsDegree e 4)) = true)
        from ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9⟩)
  rw [htriangleOK, hsumOK, hedgeOK] at hcheck
  simpa only [Bool.not_true, Bool.false_or, Bool.or_eq_true_iff, Bool.and_eq_true_iff,
    decide_eq_true_eq, or_assoc, and_assoc] using hcheck

/-- A finite Boolean split of the ten possible adjacencies on five vertices.
Under the equality-case constraints, either there is a degree-four center or
there is an isolate and every other vertex has degree two. -/
theorem fin_five_exterior_degree_structure
    (H : SimpleGraph (Fin 5)) [DecidableRel H.Adj]
    (htriangle : H.CliqueFree 3) (hedges : #H.edgeFinset = 4)
    (hedgeDegree : ∀ ⦃x y⦄, H.Adj x y →
      4 ≤ H.degree x + H.degree y) :
    (∃ c, H.degree c = 4) ∨
      (∃ z, H.degree z = 0 ∧ ∀ x, x ≠ z → H.degree x = 2) := by
  have hsumFn : (∑ x : Fin 5, H.degree x) = 8 := by
    simpa [hedges] using H.sum_degrees_eq_twice_card_edges
  have ht012 : ¬(H.Adj 0 1 ∧ H.Adj 0 2 ∧ H.Adj 1 2) := by
    intro h
    exact htriangle {0, 1, 2} (SimpleGraph.is3Clique_triple_iff.mpr h)
  have ht013 : ¬(H.Adj 0 1 ∧ H.Adj 0 3 ∧ H.Adj 1 3) := by
    intro h
    exact htriangle {0, 1, 3} (SimpleGraph.is3Clique_triple_iff.mpr h)
  have ht014 : ¬(H.Adj 0 1 ∧ H.Adj 0 4 ∧ H.Adj 1 4) := by
    intro h
    exact htriangle {0, 1, 4} (SimpleGraph.is3Clique_triple_iff.mpr h)
  have ht023 : ¬(H.Adj 0 2 ∧ H.Adj 0 3 ∧ H.Adj 2 3) := by
    intro h
    exact htriangle {0, 2, 3} (SimpleGraph.is3Clique_triple_iff.mpr h)
  have ht024 : ¬(H.Adj 0 2 ∧ H.Adj 0 4 ∧ H.Adj 2 4) := by
    intro h
    exact htriangle {0, 2, 4} (SimpleGraph.is3Clique_triple_iff.mpr h)
  have ht034 : ¬(H.Adj 0 3 ∧ H.Adj 0 4 ∧ H.Adj 3 4) := by
    intro h
    exact htriangle {0, 3, 4} (SimpleGraph.is3Clique_triple_iff.mpr h)
  have ht123 : ¬(H.Adj 1 2 ∧ H.Adj 1 3 ∧ H.Adj 2 3) := by
    intro h
    exact htriangle {1, 2, 3} (SimpleGraph.is3Clique_triple_iff.mpr h)
  have ht124 : ¬(H.Adj 1 2 ∧ H.Adj 1 4 ∧ H.Adj 2 4) := by
    intro h
    exact htriangle {1, 2, 4} (SimpleGraph.is3Clique_triple_iff.mpr h)
  have ht134 : ¬(H.Adj 1 3 ∧ H.Adj 1 4 ∧ H.Adj 3 4) := by
    intro h
    exact htriangle {1, 3, 4} (SimpleGraph.is3Clique_triple_iff.mpr h)
  have ht234 : ¬(H.Adj 2 3 ∧ H.Adj 2 4 ∧ H.Adj 3 4) := by
    intro h
    exact htriangle {2, 3, 4} (SimpleGraph.is3Clique_triple_iff.mpr h)
  have he01 : H.Adj 0 1 → 4 ≤ H.degree 0 + H.degree 1 :=
    fun h => hedgeDegree h
  have he02 : H.Adj 0 2 → 4 ≤ H.degree 0 + H.degree 2 :=
    fun h => hedgeDegree h
  have he03 : H.Adj 0 3 → 4 ≤ H.degree 0 + H.degree 3 :=
    fun h => hedgeDegree h
  have he04 : H.Adj 0 4 → 4 ≤ H.degree 0 + H.degree 4 :=
    fun h => hedgeDegree h
  have he12 : H.Adj 1 2 → 4 ≤ H.degree 1 + H.degree 2 :=
    fun h => hedgeDegree h
  have he13 : H.Adj 1 3 → 4 ≤ H.degree 1 + H.degree 3 :=
    fun h => hedgeDegree h
  have he14 : H.Adj 1 4 → 4 ≤ H.degree 1 + H.degree 4 :=
    fun h => hedgeDegree h
  have he23 : H.Adj 2 3 → 4 ≤ H.degree 2 + H.degree 3 :=
    fun h => hedgeDegree h
  have he24 : H.Adj 2 4 → 4 ≤ H.degree 2 + H.degree 4 :=
    fun h => hedgeDegree h
  have he34 : H.Adj 3 4 → 4 ≤ H.degree 3 + H.degree 4 :=
    fun h => hedgeDegree h
  have hd0 := fin_five_degree_zero_formula H
  have hd1 := fin_five_degree_one_formula H
  have hd2 := fin_five_degree_two_formula H
  have hd3 := fin_five_degree_three_formula H
  have hd4 := fin_five_degree_four_formula H
  have hpattern :
      H.degree 0 = 4 ∨ H.degree 1 = 4 ∨ H.degree 2 = 4 ∨
      H.degree 3 = 4 ∨ H.degree 4 = 4 ∨
      (H.degree 0 = 0 ∧ H.degree 1 = 2 ∧ H.degree 2 = 2 ∧
        H.degree 3 = 2 ∧ H.degree 4 = 2) ∨
      (H.degree 1 = 0 ∧ H.degree 0 = 2 ∧ H.degree 2 = 2 ∧
        H.degree 3 = 2 ∧ H.degree 4 = 2) ∨
      (H.degree 2 = 0 ∧ H.degree 0 = 2 ∧ H.degree 1 = 2 ∧
        H.degree 3 = 2 ∧ H.degree 4 = 2) ∨
      (H.degree 3 = 0 ∧ H.degree 0 = 2 ∧ H.degree 1 = 2 ∧
        H.degree 2 = 2 ∧ H.degree 4 = 2) ∨
      (H.degree 4 = 0 ∧ H.degree 0 = 2 ∧ H.degree 1 = 2 ∧
        H.degree 2 = 2 ∧ H.degree 3 = 2) := by
    let eBits : Fin 10 → Bool :=
      ![decide (H.Adj 0 1), decide (H.Adj 0 2),
        decide (H.Adj 0 3), decide (H.Adj 0 4),
        decide (H.Adj 1 2), decide (H.Adj 1 3),
        decide (H.Adj 1 4), decide (H.Adj 2 3),
        decide (H.Adj 2 4), decide (H.Adj 3 4)]
    have hbits := five_edge_bits_degree_structure eBits
    dsimp only [fiveEdgeBitsDegreeProperty] at hbits
    have hd0' : edgeBitsDegree eBits 0 = H.degree 0 := by
      simpa [edgeBitsDegree, eBits, edgeBit] using hd0.symm
    have hd1' : edgeBitsDegree eBits 1 = H.degree 1 := by
      simpa [edgeBitsDegree, eBits, edgeBit] using hd1.symm
    have hd2' : edgeBitsDegree eBits 2 = H.degree 2 := by
      simpa [edgeBitsDegree, eBits, edgeBit] using hd2.symm
    have hd3' : edgeBitsDegree eBits 3 = H.degree 3 := by
      simpa [edgeBitsDegree, eBits, edgeBit] using hd3.symm
    have hd4' : edgeBitsDegree eBits 4 = H.degree 4 := by
      simpa [edgeBitsDegree, eBits, edgeBit] using hd4.symm
    have hdAll : edgeBitsDegree eBits = fun x => H.degree x := by
      funext x
      fin_cases x
      · exact hd0'
      · exact hd1'
      · exact hd2'
      · exact hd3'
      · exact hd4'
    have htriBits :=
      (show
        (¬(eBits 0 = true ∧ eBits 1 = true ∧ eBits 4 = true)) ∧
        (¬(eBits 0 = true ∧ eBits 2 = true ∧ eBits 5 = true)) ∧
        (¬(eBits 0 = true ∧ eBits 3 = true ∧ eBits 6 = true)) ∧
        (¬(eBits 1 = true ∧ eBits 2 = true ∧ eBits 7 = true)) ∧
        (¬(eBits 1 = true ∧ eBits 3 = true ∧ eBits 8 = true)) ∧
        (¬(eBits 2 = true ∧ eBits 3 = true ∧ eBits 9 = true)) ∧
        (¬(eBits 4 = true ∧ eBits 5 = true ∧ eBits 7 = true)) ∧
        (¬(eBits 4 = true ∧ eBits 6 = true ∧ eBits 8 = true)) ∧
        (¬(eBits 5 = true ∧ eBits 6 = true ∧ eBits 9 = true)) ∧
        (¬(eBits 7 = true ∧ eBits 8 = true ∧ eBits 9 = true)) from
        ⟨by simpa [eBits] using ht012, by simpa [eBits] using ht013,
          by simpa [eBits] using ht014, by simpa [eBits] using ht023,
          by simpa [eBits] using ht024, by simpa [eBits] using ht034,
          by simpa [eBits] using ht123, by simpa [eBits] using ht124,
          by simpa [eBits] using ht134, by simpa [eBits] using ht234⟩)
    have hsumBits :
        edgeBitsDegree eBits 0 + edgeBitsDegree eBits 1 + edgeBitsDegree eBits 2 +
          edgeBitsDegree eBits 3 + edgeBitsDegree eBits 4 = 8 := by
      have hsumBitsFn : (∑ x : Fin 5, edgeBitsDegree eBits x) = 8 := by
        calc
          (∑ x : Fin 5, edgeBitsDegree eBits x) = ∑ x : Fin 5, H.degree x := by
            apply Finset.sum_congr rfl
            intro x _
            exact congrFun hdAll x
          _ = 8 := hsumFn
      simpa [Fin.sum_univ_succ, Nat.add_assoc] using hsumBitsFn
    have hedgeBits :=
      (show
        (eBits 0 = true → 4 ≤ edgeBitsDegree eBits 0 + edgeBitsDegree eBits 1) ∧
        (eBits 1 = true → 4 ≤ edgeBitsDegree eBits 0 + edgeBitsDegree eBits 2) ∧
        (eBits 2 = true → 4 ≤ edgeBitsDegree eBits 0 + edgeBitsDegree eBits 3) ∧
        (eBits 3 = true → 4 ≤ edgeBitsDegree eBits 0 + edgeBitsDegree eBits 4) ∧
        (eBits 4 = true → 4 ≤ edgeBitsDegree eBits 1 + edgeBitsDegree eBits 2) ∧
        (eBits 5 = true → 4 ≤ edgeBitsDegree eBits 1 + edgeBitsDegree eBits 3) ∧
        (eBits 6 = true → 4 ≤ edgeBitsDegree eBits 1 + edgeBitsDegree eBits 4) ∧
        (eBits 7 = true → 4 ≤ edgeBitsDegree eBits 2 + edgeBitsDegree eBits 3) ∧
        (eBits 8 = true → 4 ≤ edgeBitsDegree eBits 2 + edgeBitsDegree eBits 4) ∧
        (eBits 9 = true → 4 ≤ edgeBitsDegree eBits 3 + edgeBitsDegree eBits 4) from
        ⟨by simpa [eBits, hdAll] using he01,
          by simpa [eBits, hdAll] using he02,
          by simpa [eBits, hdAll] using he03,
          by simpa [eBits, hdAll] using he04,
          by simpa [eBits, hdAll] using he12,
          by simpa [eBits, hdAll] using he13,
          by simpa [eBits, hdAll] using he14,
          by simpa [eBits, hdAll] using he23,
          by simpa [eBits, hdAll] using he24,
          by simpa [eBits, hdAll] using he34⟩)
    have hpatternBits := hbits htriBits hsumBits hedgeBits
    simpa only [hdAll] using hpatternBits
  rcases hpattern with h0 | h1 | h2 | h3 | h4 | hz0 | hz1 | hz2 | hz3 | hz4
  · exact Or.inl ⟨0, h0⟩
  · exact Or.inl ⟨1, h1⟩
  · exact Or.inl ⟨2, h2⟩
  · exact Or.inl ⟨3, h3⟩
  · exact Or.inl ⟨4, h4⟩
  · rcases hz0 with ⟨hz0, h1, h2, h3, h4⟩
    refine Or.inr ⟨0, hz0, ?_⟩
    intro x hx
    fin_cases x
    · exact (hx rfl).elim
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · rcases hz1 with ⟨hz1, h0, h2, h3, h4⟩
    refine Or.inr ⟨1, hz1, ?_⟩
    intro x hx
    fin_cases x
    · exact h0
    · exact (hx rfl).elim
    · exact h2
    · exact h3
    · exact h4
  · rcases hz2 with ⟨hz2, h0, h1, h3, h4⟩
    refine Or.inr ⟨2, hz2, ?_⟩
    intro x hx
    fin_cases x
    · exact h0
    · exact h1
    · exact (hx rfl).elim
    · exact h3
    · exact h4
  · rcases hz3 with ⟨hz3, h0, h1, h2, h4⟩
    refine Or.inr ⟨3, hz3, ?_⟩
    intro x hx
    fin_cases x
    · exact h0
    · exact h1
    · exact h2
    · exact (hx rfl).elim
    · exact h4
  · rcases hz4 with ⟨hz4, h0, h1, h2, h3⟩
    refine Or.inr ⟨4, hz4, ?_⟩
    intro x hx
    fin_cases x
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact (hx rfl).elim

/-- Relabelled form of `fin_five_exterior_degree_structure` for any finite
five-element vertex type. -/
theorem five_exterior_degree_structure
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hcard : Fintype.card W = 5)
    (htriangle : H.CliqueFree 3) (hedges : #H.edgeFinset = 4)
    (hedgeDegree : ∀ ⦃x y⦄, H.Adj x y →
      4 ≤ H.degree x + H.degree y) :
    (∃ c, H.degree c = 4) ∨
      (∃ z, H.degree z = 0 ∧ ∀ x, x ≠ z → H.degree x = 2) := by
  classical
  letI : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  let e : W ≃ Fin 5 := Fintype.equivFinOfCardEq hcard
  let H5 : SimpleGraph (Fin 5) := H.comap e.symm
  let hiso : H5 ≃g H := SimpleGraph.Iso.comap e.symm H
  have htriangle5 : H5.CliqueFree 3 := by
    exact htriangle.comap hiso.isContained
  have hedges5 : #H5.edgeFinset = 4 := by
    exact hiso.card_edgeFinset_eq.trans hedges
  have hedgeDegree5 : ∀ ⦃x y⦄, H5.Adj x y →
      4 ≤ H5.degree x + H5.degree y := by
    intro x y hxy
    have hsource : H.Adj (e.symm x) (e.symm y) := by
      exact hxy
    have hbound := hedgeDegree hsource
    have hxdeg := hiso.degree_eq x
    have hydeg := hiso.degree_eq y
    change H.degree (e.symm x) = H5.degree x at hxdeg
    change H.degree (e.symm y) = H5.degree y at hydeg
    rw [hxdeg, hydeg] at hbound
    exact hbound
  rcases fin_five_exterior_degree_structure H5 htriangle5 hedges5
      hedgeDegree5 with hcenter | hisolate
  · obtain ⟨c, hc⟩ := hcenter
    refine Or.inl ⟨e.symm c, ?_⟩
    have hdeg := hiso.degree_eq c
    change H.degree (e.symm c) = H5.degree c at hdeg
    exact hdeg.trans hc
  · obtain ⟨z, hz, hrest⟩ := hisolate
    refine Or.inr ⟨e.symm z, ?_, ?_⟩
    · have hdeg := hiso.degree_eq z
      change H.degree (e.symm z) = H5.degree z at hdeg
      exact hdeg.trans hz
    · intro x hx
      have hex : e x ≠ z := by
        intro heq
        apply hx
        simpa using congrArg e.symm heq
      have := hrest (e x) hex
      have hdeg := hiso.degree_eq (e x)
      change H.degree (e.symm (e x)) = H5.degree (e x) at hdeg
      rw [e.symm_apply_apply] at hdeg
      exact hdeg.trans this

/-- At order ten, complementary degree five forces an explicit bipartition. -/
theorem compl_isBipartite_of_degree_eq_five_card_ten
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 3)
    (hcard : Fintype.card V = 10) (w : V)
    (hwdegree : Gᶜ.degree w = 5) :
    Gᶜ.IsBipartite := by
  classical
  let L := Gᶜ
  let A := L.neighborFinset w
  let B := exteriorFinset L w
  let C := L.between (A : Set V) (B : Set V)
  let D : Finset V := insert w B
  have htriangle : L.CliqueFree 3 := by simpa [L] using hfree
  have hAcard : #A = 5 := by
    simpa [A, L, SimpleGraph.card_neighborFinset_eq_degree] using hwdegree
  have hBcard : #B = 4 := by
    have hBraw := card_exteriorFinset L w
    have hwdegreeL : L.degree w = 5 := by simpa [L] using hwdegree
    rw [hcard, hwdegreeL] at hBraw
    simpa [B] using hBraw
  have hwNotA : w ∉ A := by simp [A]
  have hwNotB : w ∉ B := by simp [B, exteriorFinset]
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a haA haB
    have hwa : L.Adj w a := by simpa [A] using haA
    have haExterior : a ≠ w ∧ ¬L.Adj w a := by
      simpa [B, exteriorFinset] using haB
    exact haExterior.2 hwa
  have hdisSet : Disjoint (A : Set V) (B : Set V) :=
    Finset.disjoint_coe.mpr hdis
  have hCbip : C.IsBipartiteWith (A : Set V) (B : Set V) := by
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
        (SimpleGraph.isBipartiteWith_neighborFinset_subset' hCbip hxB)
    have hNySub : Ny ⊆ A := by
      simpa [Ny] using
        (SimpleGraph.isBipartiteWith_neighborFinset_subset' hCbip hyB)
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
  have hDindependent : L.IsIndepSet (D : Set V) := by
    intro x hxD y hyD hxy
    rcases Finset.mem_insert.mp hxD with hxw | hxB
    · subst x
      rcases Finset.mem_insert.mp hyD with hyw | hyB
      · exact (hxy hyw.symm).elim
      · have hyExterior : ¬L.Adj w y := by
          have hyExterior' : y ≠ w ∧ ¬L.Adj w y := by
            simpa [B, exteriorFinset] using hyB
          exact hyExterior'.2
        exact hyExterior
    · rcases Finset.mem_insert.mp hyD with hyw | hyB
      · subst y
        have hxExterior : ¬L.Adj w x := by
          have hxExterior' : x ≠ w ∧ ¬L.Adj w x := by
            simpa [B, exteriorFinset] using hxB
          exact hxExterior'.2
        exact fun hxw => hxExterior hxw.symm
      · exact hBindependent hxB hyB hxy
  have hAD : Disjoint A D := by
    rw [Finset.disjoint_left]
    intro x hxA hxD
    rcases Finset.mem_insert.mp hxD with hxw | hxB
    · exact hwNotA (hxw ▸ hxA)
    · exact (Finset.disjoint_left.mp hdis) hxA hxB
  have hcover : A ∪ D = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hxw : x = w
    · exact Or.inr (by simp [D, hxw])
    · by_cases hxA : x ∈ A
      · exact Or.inl hxA
      · have hnadj : ¬L.Adj w x := by simpa [A] using hxA
        exact Or.inr (by
          rw [Finset.mem_insert]
          exact Or.inr (by
            simp [B, exteriorFinset, hxw, hnadj]))
  have hLbip : L.IsBipartiteWith (A : Set V) (D : Set V) := by
    refine ⟨Finset.disjoint_coe.mpr hAD, ?_⟩
    intro x y hxy
    have hxCover : x ∈ A ∨ x ∈ D := by
      have : x ∈ A ∪ D := by rw [hcover]; simp
      simpa using this
    have hyCover : y ∈ A ∨ y ∈ D := by
      have : y ∈ A ∪ D := by rw [hcover]; simp
      simpa using this
    rcases hxCover with hxA | hxD
    · have hyD : y ∈ D := by
        rcases hyCover with hyA | hyD
        · exact (hAindependent hxA hyA hxy.ne hxy).elim
        · exact hyD
      exact Or.inl ⟨hxA, hyD⟩
    · have hyA : y ∈ A := by
        rcases hyCover with hyA | hyD
        · exact hyA
        · exact (hDindependent hxD hyD hxy.ne hxy).elim
      exact Or.inr ⟨hxD, hyA⟩
  exact hLbip.isBipartite

/-- A nonbipartite order-ten complement has at most twenty edges. -/
theorem card_compl_edges_le_twenty_of_admissible_order_ten_nonbipartite
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 3)
    (hcard : Fintype.card V = 10) (hnotbip : ¬Gᶜ.IsBipartite) :
    #Gᶜ.edgeFinset ≤ 20 := by
  classical
  let L := Gᶜ
  have hleFive : ∀ v, L.degree v ≤ 5 := by
    simpa [L] using
      compl_degree_le_five_of_admissible_indepSetFree_three G hG hfree
  have hleFour : ∀ v, L.degree v ≤ 4 := by
    intro v
    have hvle := hleFive v
    by_contra hnot
    have hvdegree : L.degree v = 5 := by omega
    have hbip := compl_isBipartite_of_degree_eq_five_card_ten
      G hG hfree hcard v (by simpa [L] using hvdegree)
    exact hnotbip hbip
  have hsumUpper : (∑ v, L.degree v) ≤ 4 * Fintype.card V := by
    calc
      (∑ v, L.degree v) ≤ ∑ _v : V, 4 :=
        Finset.sum_le_sum fun v _ => hleFour v
      _ = 4 * Fintype.card V := by simp [Nat.mul_comm]
  rw [L.sum_degrees_eq_twice_card_edges, hcard] at hsumUpper
  simpa [L] using (show #L.edgeFinset ≤ 20 by omega)

/-- Equality in the nonbipartite order-ten edge bound makes the complement
four-regular. -/
theorem compl_degree_eq_four_of_admissible_order_ten_nonbipartite_twenty_edges
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 3)
    (hcard : Fintype.card V = 10) (hnotbip : ¬Gᶜ.IsBipartite)
    (hedges : #Gᶜ.edgeFinset = 20) :
    ∀ v, Gᶜ.degree v = 4 := by
  classical
  let L := Gᶜ
  have hleFive : ∀ v, L.degree v ≤ 5 := by
    simpa [L] using
      compl_degree_le_five_of_admissible_indepSetFree_three G hG hfree
  have hleFour : ∀ v, L.degree v ≤ 4 := by
    intro v
    have hvle := hleFive v
    by_contra hnot
    have hvdegree : L.degree v = 5 := by omega
    have hbip := compl_isBipartite_of_degree_eq_five_card_ten
      G hG hfree hcard v (by simpa [L] using hvdegree)
    exact hnotbip hbip
  have hsumDegrees : (∑ v, L.degree v) = 40 := by
    rw [L.sum_degrees_eq_twice_card_edges]
    simp [L, hedges]
  have hsumFour : (∑ _v : V, 4) = 40 := by
    simp [hcard]
  have hsumEq : (∑ v, L.degree v) = ∑ _v : V, 4 :=
    hsumDegrees.trans hsumFour.symm
  have hall := (Finset.sum_eq_sum_iff_of_le
    (s := Finset.univ) (fun v _ => hleFour v)).mp hsumEq
  intro v
  have := hall v (Finset.mem_univ v)
  simpa [L] using this

/-- Around any vertex in the nonbipartite twenty-edge equality case, the
five-vertex exterior is either a four-leaf star or a four-cycle together with
one isolate, expressed by its intrinsic degree pattern. -/
theorem order_ten_exterior_degree_structure
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 3)
    (hcard : Fintype.card V = 10) (hnotbip : ¬Gᶜ.IsBipartite)
    (hedges : #Gᶜ.edgeFinset = 20) (w : V) :
    let B := exteriorFinset Gᶜ w
    let H := Gᶜ.induce (B : Set V)
    (∃ c, H.degree c = 4) ∨
      (∃ z, H.degree z = 0 ∧ ∀ x, x ≠ z → H.degree x = 2) := by
  classical
  let L := Gᶜ
  let A := L.neighborFinset w
  let B := exteriorFinset L w
  let C := L.between (A : Set V) (B : Set V)
  let H := L.induce (B : Set V)
  let S : Finset V := insert w A
  have hdegree : ∀ v, L.degree v = 4 := by
    simpa [L] using
      compl_degree_eq_four_of_admissible_order_ten_nonbipartite_twenty_edges
        G hG hfree hcard hnotbip hedges
  have htriangle : L.CliqueFree 3 := by simpa [L] using hfree
  have hAcard : #A = 4 := by
    simpa [A, SimpleGraph.card_neighborFinset_eq_degree] using hdegree w
  have hBcard : #B = 5 := by
    have hBraw := card_exteriorFinset L w
    rw [hcard, hdegree w] at hBraw
    simpa [B] using hBraw
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a haA haB
    have hwa : L.Adj w a := by simpa [A] using haA
    have haExterior : a ≠ w ∧ ¬L.Adj w a := by
      simpa [B, exteriorFinset] using haB
    exact haExterior.2 hwa
  have hCbip : C.IsBipartiteWith (A : Set V) (B : Set V) := by
    simpa [C] using
      (SimpleGraph.between_isBipartiteWith (G := L)
        (Finset.disjoint_coe.mpr hdis))
  have hAindependent : L.IsIndepSet (A : Set V) := by
    simpa [A] using
      (SimpleGraph.isIndepSet_neighborSet_of_triangleFree L htriangle w)
  have hinternalBot : neighborhoodInternalGraph L w = ⊥ := by
    ext x y
    simp only [neighborhoodInternalGraph, SimpleGraph.between_adj,
      SimpleGraph.bot_adj, iff_false]
    rintro ⟨hxy, hparts⟩
    rcases hparts with hparts | hparts
    · exact hAindependent hparts.1 hparts.2 hxy.ne hxy
    · exact hAindependent hparts.2 hparts.1 hxy.ne.symm hxy.symm
  have hcrossA (a : V) (haA : a ∈ A) : C.degree a = 3 := by
    have haccount := degree_neighbor_eq_one_add_internal_add_cross
      L w a (by simpa [A] using haA)
    have haccount' : L.degree a = 1 + 0 + C.degree a := by
      simpa [C, A, B, hinternalBot] using haccount
    have hadegree := hdegree a
    omega
  have hsumA : (∑ a ∈ A, C.degree a) = #C.edgeFinset :=
    SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hCbip
  have hCedges : #C.edgeFinset = 12 := by
    rw [← hsumA]
    calc
      (∑ a ∈ A, C.degree a) = ∑ _a ∈ A, 3 :=
        Finset.sum_congr rfl hcrossA
      _ = 12 := by simp [hAcard]
  have hclosed :=
    card_induce_closedNeighborhood_eq_degree_of_triangleFree L htriangle w
  have hclosed' : #(L.induce (S : Set V)).edgeFinset = 4 := by
    simpa [S, A, hdegree w] using hclosed
  have hBcompl : B = Sᶜ := by rfl
  have hpartition := card_edgeFinset_eq_induce_add_between_add_induce_compl L S
  have hcrossGraph : L.between (S : Set V) (B : Set V) = C := by
    simpa [S, A, B, C] using
      between_closedNeighborhood_exterior_eq_between_neighbor_exterior L w
  have hcrossCard :
      #(L.between (S : Set V) (B : Set V)).edgeFinset = #C.edgeFinset :=
    congrArg Finset.card (SimpleGraph.edgeFinset_inj.mpr hcrossGraph)
  rw [← hBcompl, hcrossCard] at hpartition
  have hLedges : #L.edgeFinset = 20 := by simpa [L] using hedges
  have hHedges : #H.edgeFinset = 4 := by
    have hpartition' := hpartition
    rw [hLedges, hclosed', hCedges] at hpartition'
    simpa [H] using (show #(L.induce (B : Set V)).edgeFinset = 4 by omega)
  have hHtriangle : H.CliqueFree 3 := by
    exact (SimpleGraph.cliqueFree_induce_iff (G := L) (B : Set V) 3).2
      htriangle.cliqueFreeOn
  have hHcard : Fintype.card (B : Set V) = 5 := by simpa using hBcard
  have hsplit (b : (B : Set V)) :
      C.degree (b : V) + H.degree b = 4 := by
    have hraw := degree_eq_between_neighbor_exterior_add_induce_exterior L w b
    have hbdegree := hdegree (b : V)
    have hraw' : L.degree (b : V) = C.degree (b : V) + H.degree b := by
      simpa [A, B, C, H] using hraw
    omega
  have hedgeDegree : ∀ ⦃x y⦄, H.Adj x y →
      4 ≤ H.degree x + H.degree y := by
    intro x y hxy
    let Nx := C.neighborFinset (x : V)
    let Ny := C.neighborFinset (y : V)
    have hNxSub : Nx ⊆ A := by
      simpa [Nx] using
        (SimpleGraph.isBipartiteWith_neighborFinset_subset' hCbip x.property)
    have hNySub : Ny ⊆ A := by
      simpa [Ny] using
        (SimpleGraph.isBipartiteWith_neighborFinset_subset' hCbip y.property)
    have hxyL : L.Adj (x : V) (y : V) := hxy
    have hNxNy : Disjoint Nx Ny := by
      rw [Finset.disjoint_left]
      intro a hax hay
      have hxaC : C.Adj (x : V) a := by simpa [Nx] using hax
      have hyaC : C.Adj (y : V) a := by simpa [Ny] using hay
      have haxL : L.Adj a (x : V) :=
        (SimpleGraph.between_adj.mp hxaC).1.symm
      have hayL : L.Adj a (y : V) :=
        (SimpleGraph.between_adj.mp hyaC).1.symm
      have hind :=
        SimpleGraph.isIndepSet_neighborSet_of_triangleFree L htriangle a
      exact hind haxL hayL hxyL.ne hxyL
    have hUnionSub : Nx ∪ Ny ⊆ A := Finset.union_subset hNxSub hNySub
    have hcardLe : #(Nx ∪ Ny) ≤ 4 := by
      have := Finset.card_le_card hUnionSub
      simpa [hAcard] using this
    have hcrossLe : C.degree (x : V) + C.degree (y : V) ≤ 4 := by
      rw [Finset.card_union_of_disjoint hNxNy] at hcardLe
      simpa [Nx, Ny, SimpleGraph.card_neighborFinset_eq_degree] using hcardLe
    have hxsplit := hsplit x
    have hysplit := hsplit y
    omega
  simpa [L, B, H] using
    five_exterior_degree_structure H hHcard hHtriangle hHedges hedgeDegree

/-- Nonbipartiteness rules out the star branch of the exterior split.  Thus
every equality-case exterior is a four-cycle together with one isolate. -/
theorem order_ten_exterior_cycle_degree_structure
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 3)
    (hcard : Fintype.card V = 10) (hnotbip : ¬Gᶜ.IsBipartite)
    (hedges : #Gᶜ.edgeFinset = 20) (w : V) :
    let B := exteriorFinset Gᶜ w
    let H := Gᶜ.induce (B : Set V)
    ∃ z, H.degree z = 0 ∧ ∀ x, x ≠ z → H.degree x = 2 := by
  classical
  let L := Gᶜ
  let A := L.neighborFinset w
  let B := exteriorFinset L w
  let C := L.between (A : Set V) (B : Set V)
  let H := L.induce (B : Set V)
  have hdegree : ∀ v, L.degree v = 4 := by
    simpa [L] using
      compl_degree_eq_four_of_admissible_order_ten_nonbipartite_twenty_edges
        G hG hfree hcard hnotbip hedges
  have htriangle : L.CliqueFree 3 := by simpa [L] using hfree
  have hAcard : #A = 4 := by
    simpa [A, SimpleGraph.card_neighborFinset_eq_degree] using hdegree w
  have hBcard : #B = 5 := by
    have hBraw := card_exteriorFinset L w
    rw [hcard, hdegree w] at hBraw
    simpa [B] using hBraw
  have hBtype : Fintype.card (B : Set V) = 5 := by simpa using hBcard
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a haA haB
    have hwa : L.Adj w a := by simpa [A] using haA
    have haExterior : a ≠ w ∧ ¬L.Adj w a := by
      simpa [B, exteriorFinset] using haB
    exact haExterior.2 hwa
  have hAindependent : L.IsIndepSet (A : Set V) := by
    simpa [A] using
      (SimpleGraph.isIndepSet_neighborSet_of_triangleFree L htriangle w)
  have hHtriangle : H.CliqueFree 3 := by
    exact (SimpleGraph.cliqueFree_induce_iff (G := L) (B : Set V) 3).2
      htriangle.cliqueFreeOn
  rcases order_ten_exterior_degree_structure G hG hfree hcard hnotbip
      hedges w with hcenter | hisolate
  · obtain ⟨c, hc⟩ := hcenter
    have hcUniversal : H.IsUniversal c := by
      apply (H.degree_eq_card_sub_one c).mp
      rw [hBtype]
      simpa using hc
    have hsplitc :=
      degree_eq_between_neighbor_exterior_add_induce_exterior L w c
    have hsplitc' :
        L.degree (c : V) = C.degree (c : V) + H.degree c := by
      simpa [A, B, C, H] using hsplitc
    have hCzero : C.degree (c : V) = 0 := by
      have hcdegree := hdegree (c : V)
      have hc' : (L.induce (B : Set V)).degree c = 4 := by
        simpa [H] using hc
      dsimp [H] at hsplitc'
      omega
    have hCisolated : C.IsIsolated (c : V) :=
      (C.degree_eq_zero (c : V)).mp hCzero
    let X : Finset V := insert w (B.erase (c : V))
    let Y : Finset V := insert (c : V) A
    have hwNotA : w ∉ A := by simp [A]
    have hcNotW : (c : V) ≠ w := by
      have hcB : (c : V) ∈ B := c.property
      change (c : V) ∈ (insert w (L.neighborFinset w))ᶜ at hcB
      have hcExterior : (c : V) ∉ insert w (L.neighborFinset w) :=
        Finset.mem_compl.mp hcB
      intro hcw
      exact hcExterior (Finset.mem_insert.mpr (Or.inl hcw))
    have hXYdis : Disjoint X Y := by
      rw [Finset.disjoint_left]
      intro x hxX hxY
      rcases Finset.mem_insert.mp hxX with hxw | hxB
      · subst x
        rcases Finset.mem_insert.mp hxY with hwc | hwA
        · exact hcNotW hwc.symm
        · exact hwNotA hwA
      · have hxB' : x ∈ B := (Finset.mem_erase.mp hxB).2
        have hxc : x ≠ (c : V) := (Finset.mem_erase.mp hxB).1
        rcases Finset.mem_insert.mp hxY with hxc' | hxA
        · exact hxc hxc'
        · exact (Finset.disjoint_left.mp hdis) hxA hxB'
    have hXYcover : X ∪ Y = Finset.univ := by
      ext x
      simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      by_cases hxw : x = w
      · exact Or.inl (by simp [X, hxw])
      · by_cases hxA : x ∈ A
        · exact Or.inr (by simp [Y, hxA])
        · have hnadj : ¬L.Adj w x := by simpa [A] using hxA
          have hxB : x ∈ B := by
            simp [B, exteriorFinset, hxw, hnadj]
          by_cases hxc : x = (c : V)
          · exact Or.inr (by simp [Y, hxc])
          · exact Or.inl (by simp [X, hxB, hxc])
    have hXindependent : L.IsIndepSet (X : Set V) := by
      intro x hxX y hyX hxy hxyL
      rcases Finset.mem_insert.mp hxX with hxw | hxB
      · subst x
        rcases Finset.mem_insert.mp hyX with hyw | hyB
        · exact (hxy hyw.symm).elim
        · have hyExterior : ¬L.Adj w y := by
            have hyB' : y ∈ B := (Finset.mem_erase.mp hyB).2
            have hyExterior' : y ≠ w ∧ ¬L.Adj w y := by
              simpa [B, exteriorFinset] using hyB'
            exact hyExterior'.2
          exact hyExterior hxyL
      · rcases Finset.mem_insert.mp hyX with hyw | hyB
        · subst y
          have hxB' : x ∈ B := (Finset.mem_erase.mp hxB).2
          have hxExterior : ¬L.Adj w x := by
            have hxExterior' : x ≠ w ∧ ¬L.Adj w x := by
              simpa [B, exteriorFinset] using hxB'
            exact hxExterior'.2
          exact hxExterior hxyL.symm
        · let xb : (B : Set V) := ⟨x, (Finset.mem_erase.mp hxB).2⟩
          let yb : (B : Set V) := ⟨y, (Finset.mem_erase.mp hyB).2⟩
          have hxc : c ≠ xb := by
            intro h
            have : (c : V) = x := congrArg Subtype.val h
            exact (Finset.mem_erase.mp hxB).1 this.symm
          have hyc : c ≠ yb := by
            intro h
            have : (c : V) = y := congrArg Subtype.val h
            exact (Finset.mem_erase.mp hyB).1 this.symm
          have hcx : H.Adj c xb := hcUniversal hxc
          have hcy : H.Adj c yb := hcUniversal hyc
          have hxyH : H.Adj xb yb := by exact hxyL
          have hind :=
            SimpleGraph.isIndepSet_neighborSet_of_triangleFree H hHtriangle c
          exact hind hcx hcy (fun h => hxy (congrArg Subtype.val h)) hxyH
    have hYindependent : L.IsIndepSet (Y : Set V) := by
      intro x hxY y hyY hxy hxyL
      rcases Finset.mem_insert.mp hxY with hxc | hxA
      · subst x
        rcases Finset.mem_insert.mp hyY with hyc | hyA
        · exact (hxy hyc.symm).elim
        · have hcyC : C.Adj (c : V) y := by
            exact ⟨hxyL, Or.inr ⟨c.property, hyA⟩⟩
          exact hCisolated y hcyC
      · rcases Finset.mem_insert.mp hyY with hyc | hyA
        · subst y
          have hxcC : C.Adj (c : V) x := by
            exact ⟨hxyL.symm, Or.inr ⟨c.property, hxA⟩⟩
          exact hCisolated x hxcC
        · exact hAindependent hxA hyA hxy hxyL
    have hbipWith := isBipartiteWith_of_independent_partition
      L X Y hXYdis hXYcover hXindependent hYindependent
    have hbip : L.IsBipartite := hbipWith.isBipartite
    exact (hnotbip (by simpa [L] using hbip)).elim
  · simpa [L, B, H] using hisolate

set_option maxHeartbeats 1000000 in
-- The equality-case reconstruction transports several degree and adjacency
-- identities through induced subgraphs and a ten-vertex partition; the default
-- heartbeat limit is too small for elaborating this proof term.
/-- The nonbipartite twenty-edge equality case is the balanced two-fold
blow-up of the five-cycle. -/
theorem compl_iso_balancedC5Blowup_of_admissible_order_ten_equality
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 3)
    (hcard : Fintype.card V = 10) (hnotbip : ¬Gᶜ.IsBipartite)
    (hedges : #Gᶜ.edgeFinset = 20) :
    Nonempty (Gᶜ ≃g balancedC5Blowup) := by
  classical
  let L := Gᶜ
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let w : V := Classical.arbitrary V
  let A := L.neighborFinset w
  let B := exteriorFinset L w
  let C := L.between (A : Set V) (B : Set V)
  let H := L.induce (B : Set V)
  have hdegree : ∀ v, L.degree v = 4 := by
    simpa [L] using
      compl_degree_eq_four_of_admissible_order_ten_nonbipartite_twenty_edges
        G hG hfree hcard hnotbip hedges
  have htriangle : L.CliqueFree 3 := by simpa [L] using hfree
  have hAcard : #A = 4 := by
    simpa [A, SimpleGraph.card_neighborFinset_eq_degree] using hdegree w
  have hBcard : #B = 5 := by
    have hBraw := card_exteriorFinset L w
    rw [hcard, hdegree w] at hBraw
    simpa [B] using hBraw
  have hBtype : Fintype.card (B : Set V) = 5 := by simpa using hBcard
  have hdisAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a haA haB
    have hwa : L.Adj w a := by simpa [A] using haA
    have haExterior : a ≠ w ∧ ¬L.Adj w a := by
      simpa [B, exteriorFinset] using haB
    exact haExterior.2 hwa
  have hCbip : C.IsBipartiteWith (A : Set V) (B : Set V) := by
    simpa [C] using
      (SimpleGraph.between_isBipartiteWith (G := L)
        (Finset.disjoint_coe.mpr hdisAB))
  have hAindependent : L.IsIndepSet (A : Set V) := by
    simpa [A] using
      (SimpleGraph.isIndepSet_neighborSet_of_triangleFree L htriangle w)
  have hHtriangle : H.CliqueFree 3 := by
    exact (SimpleGraph.cliqueFree_induce_iff (G := L) (B : Set V) 3).2
      htriangle.cliqueFreeOn
  obtain ⟨z, hz, hrest⟩ :=
    order_ten_exterior_cycle_degree_structure G hG hfree hcard hnotbip
      hedges w
  change H.degree z = 0 at hz
  change ∀ x, x ≠ z → H.degree x = 2 at hrest
  have hzIsolated : H.IsIsolated z := (H.degree_eq_zero z).mp hz
  have hBlarge : 1 < #B := by omega
  obtain ⟨xv, hxvB, hxvne⟩ := Finset.exists_mem_ne hBlarge (z : V)
  let x : (B : Set V) := ⟨xv, hxvB⟩
  have hxz : x ≠ z := by
    intro h
    exact hxvne (congrArg Subtype.val h)
  have hxdegree : H.degree x = 2 := hrest x hxz
  let N : Finset (B : Set V) := H.neighborFinset x
  let Q : Finset (B : Set V) := Finset.univ.erase z \ N
  have hNcard : #N = 2 := by
    simpa [N, SimpleGraph.card_neighborFinset_eq_degree] using hxdegree
  have hzNotN : z ∉ N := by
    intro hzN
    have hxzAdj : H.Adj x z := by simpa [N] using hzN
    exact hzIsolated x hxzAdj.symm
  have hNsub : N ⊆ Finset.univ.erase z := by
    intro y hyN
    have hyz : y ≠ z := by
      intro h
      subst y
      exact hzNotN hyN
    simp [hyz]
  have hEraseCard : #(Finset.univ.erase z : Finset (B : Set V)) = 4 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ, hBtype]
  have hQcard : #Q = 2 := by
    change #(Finset.univ.erase z \ N) = 2
    rw [Finset.card_sdiff_of_subset hNsub, hEraseCard, hNcard]
  have hxQ : x ∈ Q := by
    have hxNotN : x ∉ N := by simp [N]
    simp [Q, hxz, hxNotN]
  have hQindependent : H.IsIndepSet (Q : Set (B : Set V)) := by
    intro a haQ b hbQ hab habH
    by_cases hax : a = x
    · subst a
      have hbN : b ∈ N := by simpa [N] using habH
      exact (Finset.mem_sdiff.mp hbQ).2 hbN
    · by_cases hbx : b = x
      · subst b
        have haN : a ∈ N := by simpa [N] using habH.symm
        exact (Finset.mem_sdiff.mp haQ).2 haN
      · have htripleSub : ({x, a, b} : Finset (B : Set V)) ⊆ Q := by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl
          · exact hxQ
          · exact haQ
          · exact hbQ
        have htripleCard : #({x, a, b} : Finset (B : Set V)) = 3 := by
          have hxnot : x ∉ ({a, b} : Finset (B : Set V)) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨Ne.symm hax, Ne.symm hbx⟩
          rw [Finset.card_insert_of_notMem hxnot]
          simp [hab]
        have := Finset.card_le_card htripleSub
        rw [htripleCard, hQcard] at this
        omega
  have hNindependent : H.IsIndepSet (N : Set (B : Set V)) := by
    simpa [N] using
      (SimpleGraph.isIndepSet_neighborSet_of_triangleFree H hHtriangle x)
  have hQNuniv : Q ∪ N = Finset.univ.erase z := by
    exact Finset.sdiff_union_of_subset hNsub
  have hNonzCover (b : (B : Set V)) (hbz : b ≠ z) : b ∈ Q ∨ b ∈ N := by
    have hb : b ∈ Finset.univ.erase z := by simp [hbz]
    rw [← hQNuniv] at hb
    simpa using hb
  have hQNcomplete : ∀ q ∈ Q, ∀ n ∈ N, H.Adj q n := by
    intro q hqQ n hnN
    have hqz : q ≠ z := by
      have := (Finset.mem_sdiff.mp hqQ).1
      exact (Finset.mem_erase.mp this).1
    have hqdegree : H.degree q = 2 := hrest q hqz
    have hneighborSub : H.neighborFinset q ⊆ N := by
      intro y hy
      have hqy : H.Adj q y := by simpa using hy
      have hyz : y ≠ z := by
        intro hyz
        subst y
        exact hzIsolated q hqy.symm
      rcases hNonzCover y hyz with hyQ | hyN
      · exact (hQindependent hqQ hyQ hqy.ne hqy).elim
      · exact hyN
    have hneighborCard : #(H.neighborFinset q) = 2 := by
      simpa [SimpleGraph.card_neighborFinset_eq_degree] using hqdegree
    have hneighborEq : H.neighborFinset q = N := by
      apply Finset.eq_of_subset_of_card_le hneighborSub
      rw [hneighborCard, hNcard]
    have : n ∈ H.neighborFinset q := by simpa [hneighborEq] using hnN
    simpa using this
  have hcrossSub (b : (B : Set V)) : C.neighborFinset (b : V) ⊆ A := by
    simpa using
      (SimpleGraph.isBipartiteWith_neighborFinset_subset' hCbip b.property)
  have hsplit (b : (B : Set V)) :
      C.degree (b : V) + H.degree b = 4 := by
    have hraw := degree_eq_between_neighbor_exterior_add_induce_exterior L w b
    have hraw' : L.degree (b : V) = C.degree (b : V) + H.degree b := by
      simpa [A, B, C, H] using hraw
    have hbdegree := hdegree (b : V)
    omega
  have hcrossCard (b : (B : Set V)) (hbz : b ≠ z) :
      #(C.neighborFinset (b : V)) = 2 := by
    have hbH := hrest b hbz
    have hbsplit := hsplit b
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  have hzCrossCard : #(C.neighborFinset (z : V)) = 4 := by
    have hzsplit := hsplit z
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  have hzCrossEq : C.neighborFinset (z : V) = A := by
    apply Finset.eq_of_subset_of_card_le (hcrossSub z)
    rw [hzCrossCard, hAcard]
  have hcrossDisjoint : ∀ ⦃p q : (B : Set V)⦄, H.Adj p q →
      Disjoint (C.neighborFinset (p : V)) (C.neighborFinset (q : V)) := by
    intro p q hpq
    rw [Finset.disjoint_left]
    intro a hap haq
    have hpaC : C.Adj (p : V) a := by simpa using hap
    have hqaC : C.Adj (q : V) a := by simpa using haq
    have hapL : L.Adj a (p : V) :=
      (SimpleGraph.between_adj.mp hpaC).1.symm
    have haqL : L.Adj a (q : V) :=
      (SimpleGraph.between_adj.mp hqaC).1.symm
    have hpqL : L.Adj (p : V) (q : V) := hpq
    have hind :=
      SimpleGraph.isIndepSet_neighborSet_of_triangleFree L htriangle a
    exact hind hapL haqL hpqL.ne hpqL
  let U : Finset V := C.neighborFinset (x : V)
  let D : Finset V := A \ U
  have hUsub : U ⊆ A := by simpa [U] using hcrossSub x
  have hUcard : #U = 2 := by simpa [U] using hcrossCard x hxz
  have hDcard : #D = 2 := by
    dsimp [D]
    rw [Finset.card_sdiff_of_subset hUsub, hAcard, hUcard]
  have hNcrossEq (n : (B : Set V)) (hnN : n ∈ N) :
      C.neighborFinset (n : V) = D := by
    have hxn : H.Adj x n := by simpa [N] using hnN
    have hnz : n ≠ z := by
      have hnErase := hNsub hnN
      exact (Finset.mem_erase.mp hnErase).1
    have hnCard := hcrossCard n hnz
    have hdisCross := hcrossDisjoint hxn
    simpa [U, D] using
      eq_sdiff_of_subset_card_two_disjoint hAcard hUsub hUcard
        (hcrossSub n) hnCard hdisCross
  have hNnonempty : N.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨n0, hn0N⟩ := hNnonempty
  have hQcrossEq (q : (B : Set V)) (hqQ : q ∈ Q) :
      C.neighborFinset (q : V) = U := by
    have hxn0 : H.Adj x n0 := by simpa [N] using hn0N
    have hqn0 : H.Adj q n0 := hQNcomplete q hqQ n0 hn0N
    have hqz : q ≠ z := by
      have hqErase := (Finset.mem_sdiff.mp hqQ).1
      exact (Finset.mem_erase.mp hqErase).1
    have hn0z : n0 ≠ z := by
      have hn0Erase := hNsub hn0N
      exact (Finset.mem_erase.mp hn0Erase).1
    have hN0card := hcrossCard n0 hn0z
    have hQcardCross := hcrossCard q hqz
    have hUasComp : U = A \ C.neighborFinset (n0 : V) := by
      simpa [U] using
        eq_sdiff_of_subset_card_two_disjoint hAcard
          (hcrossSub n0) hN0card hUsub hUcard
          (hcrossDisjoint hxn0).symm
    have hQasComp : C.neighborFinset (q : V) =
        A \ C.neighborFinset (n0 : V) := by
      exact eq_sdiff_of_subset_card_two_disjoint hAcard
        (hcrossSub n0) hN0card (hcrossSub q) hQcardCross
        (hcrossDisjoint hqn0).symm
    exact hQasComp.trans hUasComp.symm
  let subEmb : (B : Set V) ↪ V := Function.Embedding.subtype _
  let P2 : Finset V := Q.map subEmb
  let P3 : Finset V := N.map subEmb
  have hP2card : #P2 = 2 := by simp [P2, hQcard]
  have hP3card : #P3 = 2 := by simp [P3, hNcard]
  have hP2subB : P2 ⊆ B := by
    intro v hv
    rw [Finset.mem_map] at hv
    obtain ⟨q, hqQ, rfl⟩ := hv
    exact q.property
  have hP3subB : P3 ⊆ B := by
    intro v hv
    rw [Finset.mem_map] at hv
    obtain ⟨n, hnN, rfl⟩ := hv
    exact n.property
  have hzNotP2 : (z : V) ∉ P2 := by
    intro hzP2
    rw [Finset.mem_map] at hzP2
    obtain ⟨q, hqQ, hqz⟩ := hzP2
    have hqErase := (Finset.mem_sdiff.mp hqQ).1
    have hqne := (Finset.mem_erase.mp hqErase).1
    exact hqne (Subtype.ext hqz)
  have hzNotP3 : (z : V) ∉ P3 := by
    intro hzP3
    rw [Finset.mem_map] at hzP3
    obtain ⟨n, hnN, hnz⟩ := hzP3
    have hnErase := hNsub hnN
    have hnne := (Finset.mem_erase.mp hnErase).1
    exact hnne (Subtype.ext hnz)
  have hP2P3dis : Disjoint P2 P3 := by
    rw [Finset.disjoint_left]
    intro v hv2 hv3
    rw [Finset.mem_map] at hv2 hv3
    obtain ⟨q, hqQ, rfl⟩ := hv2
    obtain ⟨n, hnN, hqn⟩ := hv3
    have hqNotN := (Finset.mem_sdiff.mp hqQ).2
    have hnq : n = q := subEmb.injective hqn
    subst n
    exact hqNotN hnN
  have hwz : w ≠ (z : V) := by
    have hzB : (z : V) ∈ B := z.property
    change (z : V) ∈ (insert w (L.neighborFinset w))ᶜ at hzB
    have hzOutside : (z : V) ∉ insert w (L.neighborFinset w) :=
      Finset.mem_compl.mp hzB
    intro hwz
    exact hzOutside (Finset.mem_insert.mpr (Or.inl hwz.symm))
  have hwNotB : w ∉ B := by simp [B, exteriorFinset]
  let P0 : Finset V := {w, (z : V)}
  have hP0card : #P0 = 2 := by simp [P0, hwz]
  have hP0disA : Disjoint P0 A := by
    rw [Finset.disjoint_left]
    intro v hv0 hvA
    have hwNotA : w ∉ A := by simp [A]
    rcases Finset.mem_insert.mp hv0 with hvw | hvz
    · exact hwNotA (hvw ▸ hvA)
    · have hvz' : v = (z : V) := Finset.mem_singleton.mp hvz
      have hzB : (z : V) ∈ B := z.property
      exact (Finset.disjoint_left.mp hdisAB) hvA (hvz' ▸ hzB)
  have hP0disP2 : Disjoint P0 P2 := by
    rw [Finset.disjoint_left]
    intro v hv0 hv2
    rcases Finset.mem_insert.mp hv0 with hvw | hvz
    · exact hwNotB (hvw ▸ hP2subB hv2)
    · have hvz' : v = (z : V) := Finset.mem_singleton.mp hvz
      exact hzNotP2 (hvz' ▸ hv2)
  have hP0disP3 : Disjoint P0 P3 := by
    rw [Finset.disjoint_left]
    intro v hv0 hv3
    rcases Finset.mem_insert.mp hv0 with hvw | hvz
    · exact hwNotB (hvw ▸ hP3subB hv3)
    · have hvz' : v = (z : V) := Finset.mem_singleton.mp hvz
      exact hzNotP3 (hvz' ▸ hv3)
  have hUDdis : Disjoint U D := by
    rw [Finset.disjoint_left]
    intro v hvU hvD
    exact (Finset.mem_sdiff.mp hvD).2 hvU
  have hUP2dis : Disjoint U P2 :=
    hdisAB.mono hUsub hP2subB
  have hUP3dis : Disjoint U P3 :=
    hdisAB.mono hUsub hP3subB
  have hDsub : D ⊆ A := Finset.sdiff_subset
  have hDP2dis : Disjoint D P2 :=
    hdisAB.mono hDsub hP2subB
  have hDP3dis : Disjoint D P3 :=
    hdisAB.mono hDsub hP3subB
  have hP23cover : P2 ∪ P3 = B.erase (z : V) := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hv2 | hv3
      · exact Finset.mem_erase.mpr ⟨fun hvz => hzNotP2 (hvz ▸ hv2), hP2subB hv2⟩
      · exact Finset.mem_erase.mpr ⟨fun hvz => hzNotP3 (hvz ▸ hv3), hP3subB hv3⟩
    · intro hv
      have hvB := (Finset.mem_erase.mp hv).2
      have hvz := (Finset.mem_erase.mp hv).1
      let b : (B : Set V) := ⟨v, hvB⟩
      have hbz : b ≠ z := by
        intro h
        exact hvz (congrArg Subtype.val h)
      rcases hNonzCover b hbz with hbQ | hbN
      · apply Finset.mem_union_left
        exact Finset.mem_map.mpr ⟨b, hbQ, rfl⟩
      · apply Finset.mem_union_right
        exact Finset.mem_map.mpr ⟨b, hbN, rfl⟩
  let P : Fin 5 → Finset V := ![P0, U, P2, P3, D]
  have hPcard : ∀ i, #(P i) = 2 := by
    intro i
    fin_cases i
    · exact hP0card
    · exact hUcard
    · exact hP2card
    · exact hP3card
    · exact hDcard
  have hPcover : ∀ v, ∃ i, v ∈ P i := by
    intro v
    by_cases hvw : v = w
    · exact ⟨0, by simp [P, P0, hvw]⟩
    · by_cases hvA : v ∈ A
      · by_cases hvU : v ∈ U
        · exact ⟨1, by simpa [P] using hvU⟩
        · have hvD : v ∈ D := Finset.mem_sdiff.mpr ⟨hvA, hvU⟩
          exact ⟨4, by simpa [P] using hvD⟩
      · have hvNotAdj : ¬L.Adj w v := by simpa [A] using hvA
        have hvB : v ∈ B := by simp [B, exteriorFinset, hvw, hvNotAdj]
        by_cases hvz : v = (z : V)
        · exact ⟨0, by simp [P, P0, hvz]⟩
        · have hvErase : v ∈ B.erase (z : V) :=
            Finset.mem_erase.mpr ⟨hvz, hvB⟩
          rw [← hP23cover] at hvErase
          rcases Finset.mem_union.mp hvErase with hv2 | hv3
          · exact ⟨2, by simpa [P] using hv2⟩
          · exact ⟨3, by simpa [P] using hv3⟩
  have hP0Udis : Disjoint P0 U :=
    hP0disA.mono (by intro v hv; exact hv) hUsub
  have hP0Ddis : Disjoint P0 D :=
    hP0disA.mono (by intro v hv; exact hv) hDsub
  have hPdis : Pairwise fun i j => Disjoint (P i) (P j) := by
    intro i j hij
    fin_cases i
    · fin_cases j
      · exact (hij rfl).elim
      · simpa [P] using hP0Udis
      · simpa [P] using hP0disP2
      · simpa [P] using hP0disP3
      · simpa [P] using hP0Ddis
    · fin_cases j
      · simpa [P] using hP0Udis.symm
      · exact (hij rfl).elim
      · simpa [P] using hUP2dis
      · simpa [P] using hUP3dis
      · simpa [P] using hUDdis
    · fin_cases j
      · simpa [P] using hP0disP2.symm
      · simpa [P] using hUP2dis.symm
      · exact (hij rfl).elim
      · simpa [P] using hP2P3dis
      · simpa [P] using hDP2dis.symm
    · fin_cases j
      · simpa [P] using hP0disP3.symm
      · simpa [P] using hUP3dis.symm
      · simpa [P] using hP2P3dis.symm
      · exact (hij rfl).elim
      · simpa [P] using hDP3dis.symm
    · fin_cases j
      · simpa [P] using hP0Ddis.symm
      · simpa [P] using hUDdis.symm
      · simpa [P] using hDP2dis
      · simpa [P] using hDP3dis
      · exact (hij rfl).elim
  have hwzNonadj : ¬L.Adj w (z : V) := by
    have hzB : (z : V) ∈ B := z.property
    change (z : V) ∈ (insert w (L.neighborFinset w))ᶜ at hzB
    have hzOutside : (z : V) ∉ insert w (L.neighborFinset w) :=
      Finset.mem_compl.mp hzB
    intro hwzAdj
    apply hzOutside
    exact Finset.mem_insert.mpr (Or.inr (by simpa using hwzAdj))
  have hP0independent : L.IsIndepSet (P0 : Set V) := by
    intro a ha b hb hab habL
    rcases Finset.mem_insert.mp ha with haw | haz
    · subst a
      rcases Finset.mem_insert.mp hb with hbw | hbz
      · exact (hab hbw.symm).elim
      · have hbz' : b = (z : V) := Finset.mem_singleton.mp hbz
        subst b
        exact hwzNonadj habL
    · have haz' : a = (z : V) := Finset.mem_singleton.mp haz
      subst a
      rcases Finset.mem_insert.mp hb with hbw | hbz
      · subst b
        exact hwzNonadj habL.symm
      · have hbz' : b = (z : V) := Finset.mem_singleton.mp hbz
        exact (hab hbz'.symm).elim
  have hUindependent : L.IsIndepSet (U : Set V) := by
    intro a ha b hb hab
    exact hAindependent (hUsub ha) (hUsub hb) hab
  have hDindependent : L.IsIndepSet (D : Set V) := by
    intro a ha b hb hab
    exact hAindependent (hDsub ha) (hDsub hb) hab
  have hP2independent : L.IsIndepSet (P2 : Set V) := by
    intro a ha b hb hab habL
    have ha' : a ∈ P2 := ha
    have hb' : b ∈ P2 := hb
    rw [Finset.mem_map] at ha' hb'
    obtain ⟨qa, hqaQ, rfl⟩ := ha'
    obtain ⟨qb, hqbQ, rfl⟩ := hb'
    have hqab : qa ≠ qb := fun h => hab (congrArg Subtype.val h)
    exact hQindependent hqaQ hqbQ hqab (show H.Adj qa qb from habL)
  have hP3independent : L.IsIndepSet (P3 : Set V) := by
    intro a ha b hb hab habL
    have ha' : a ∈ P3 := ha
    have hb' : b ∈ P3 := hb
    rw [Finset.mem_map] at ha' hb'
    obtain ⟨na, hnaN, rfl⟩ := ha'
    obtain ⟨nb, hnbN, rfl⟩ := hb'
    have hnab : na ≠ nb := fun h => hab (congrArg Subtype.val h)
    exact hNindependent hnaN hnbN hnab (show H.Adj na nb from habL)
  have hP0Uadj : ∀ a ∈ P0, ∀ b ∈ U, L.Adj a b := by
    intro a ha b hb
    rcases Finset.mem_insert.mp ha with haw | haz
    · subst a
      have hbA := hUsub hb
      simpa [A] using hbA
    · have haz' : a = (z : V) := Finset.mem_singleton.mp haz
      subst a
      have hbNeighbor : b ∈ C.neighborFinset (z : V) := by
        rw [hzCrossEq]
        exact hUsub hb
      have hzbC : C.Adj (z : V) b := by simpa using hbNeighbor
      exact (SimpleGraph.between_adj.mp hzbC).1
  have hP0Dadj : ∀ a ∈ P0, ∀ b ∈ D, L.Adj a b := by
    intro a ha b hb
    rcases Finset.mem_insert.mp ha with haw | haz
    · subst a
      have hbA := hDsub hb
      simpa [A] using hbA
    · have haz' : a = (z : V) := Finset.mem_singleton.mp haz
      subst a
      have hbNeighbor : b ∈ C.neighborFinset (z : V) := by
        rw [hzCrossEq]
        exact hDsub hb
      have hzbC : C.Adj (z : V) b := by simpa using hbNeighbor
      exact (SimpleGraph.between_adj.mp hzbC).1
  have hUP2adj : ∀ a ∈ U, ∀ b ∈ P2, L.Adj a b := by
    intro a ha b hb
    rw [Finset.mem_map] at hb
    obtain ⟨q, hqQ, rfl⟩ := hb
    have haNeighbor : a ∈ C.neighborFinset (q : V) := by
      rw [hQcrossEq q hqQ]
      exact ha
    have hqaC : C.Adj (q : V) a := by simpa using haNeighbor
    exact (SimpleGraph.between_adj.mp hqaC).1.symm
  have hP2P3adj : ∀ a ∈ P2, ∀ b ∈ P3, L.Adj a b := by
    intro a ha b hb
    rw [Finset.mem_map] at ha hb
    obtain ⟨q, hqQ, rfl⟩ := ha
    obtain ⟨n, hnN, rfl⟩ := hb
    exact (show L.Adj (q : V) (n : V) from hQNcomplete q hqQ n hnN)
  have hP3Dadj : ∀ a ∈ P3, ∀ b ∈ D, L.Adj a b := by
    intro a ha b hb
    rw [Finset.mem_map] at ha
    obtain ⟨n, hnN, rfl⟩ := ha
    have hbNeighbor : b ∈ C.neighborFinset (n : V) := by
      rw [hNcrossEq n hnN]
      exact hb
    have hnbC : C.Adj (n : V) b := by simpa using hbNeighbor
    exact (SimpleGraph.between_adj.mp hnbC).1
  have hP0P2nonadj : ∀ a ∈ P0, ∀ b ∈ P2, ¬L.Adj a b := by
    intro a ha b hb
    rw [Finset.mem_map] at hb
    obtain ⟨q, hqQ, rfl⟩ := hb
    rcases Finset.mem_insert.mp ha with haw | haz
    · subst a
      have hqExterior : ¬L.Adj w (q : V) := by
        have hqB : (q : V) ∈ B := q.property
        have hqExterior' : (q : V) ≠ w ∧ ¬L.Adj w (q : V) := by
          simpa [B, exteriorFinset] using hqB
        exact hqExterior'.2
      exact hqExterior
    · have haz' : a = (z : V) := Finset.mem_singleton.mp haz
      subst a
      intro hzqL
      exact hzIsolated q (show H.Adj z q from hzqL)
  have hP0P3nonadj : ∀ a ∈ P0, ∀ b ∈ P3, ¬L.Adj a b := by
    intro a ha b hb
    rw [Finset.mem_map] at hb
    obtain ⟨n, hnN, rfl⟩ := hb
    rcases Finset.mem_insert.mp ha with haw | haz
    · subst a
      have hnExterior : ¬L.Adj w (n : V) := by
        have hnB : (n : V) ∈ B := n.property
        have hnExterior' : (n : V) ≠ w ∧ ¬L.Adj w (n : V) := by
          simpa [B, exteriorFinset] using hnB
        exact hnExterior'.2
      exact hnExterior
    · have haz' : a = (z : V) := Finset.mem_singleton.mp haz
      subst a
      intro hznL
      exact hzIsolated n (show H.Adj z n from hznL)
  have hUP3nonadj : ∀ a ∈ U, ∀ b ∈ P3, ¬L.Adj a b := by
    intro a ha b hb habL
    rw [Finset.mem_map] at hb
    obtain ⟨n, hnN, rfl⟩ := hb
    have hnaC : C.Adj (n : V) a :=
      ⟨habL.symm, Or.inr ⟨n.property, hUsub ha⟩⟩
    have haNeighbor : a ∈ C.neighborFinset (n : V) := by simpa using hnaC
    rw [hNcrossEq n hnN] at haNeighbor
    exact (Finset.disjoint_left.mp hUDdis) ha haNeighbor
  have hP2Dnonadj : ∀ a ∈ P2, ∀ b ∈ D, ¬L.Adj a b := by
    intro a ha b hb habL
    rw [Finset.mem_map] at ha
    obtain ⟨q, hqQ, rfl⟩ := ha
    have hqbC : C.Adj (q : V) b :=
      ⟨habL, Or.inr ⟨q.property, hDsub hb⟩⟩
    have hbNeighbor : b ∈ C.neighborFinset (q : V) := by simpa using hqbC
    rw [hQcrossEq q hqQ] at hbNeighbor
    exact (Finset.disjoint_left.mp hUDdis) hbNeighbor hb
  have hnonadjOfIndependent (S : Finset V)
      (hS : L.IsIndepSet (S : Set V)) :
      ∀ a ∈ S, ∀ b ∈ S, ¬L.Adj a b := by
    intro a ha b hb habL
    exact hS ha hb habL.ne habL
  have hP0nonadj := hnonadjOfIndependent P0 hP0independent
  have hUnonadj := hnonadjOfIndependent U hUindependent
  have hP2nonadj := hnonadjOfIndependent P2 hP2independent
  have hP3nonadj := hnonadjOfIndependent P3 hP3independent
  have hDnonadj := hnonadjOfIndependent D hDindependent
  have hUDnonadj : ∀ a ∈ U, ∀ b ∈ D, ¬L.Adj a b := by
    intro a ha b hb habL
    exact hAindependent (hUsub ha) (hDsub hb) habL.ne habL
  have iffTrue : ∀ {p q : Prop}, p → q → (p ↔ q) :=
    fun hp hq => ⟨fun _ => hq, fun _ => hp⟩
  have iffFalse : ∀ {p q : Prop}, (¬p) → (¬q) → (p ↔ q) :=
    fun hp hq => ⟨fun h => (hp h).elim, fun h => (hq h).elim⟩
  have hPadj : ∀ i j x, x ∈ P i → ∀ y, y ∈ P j →
      (L.Adj x y ↔ (SimpleGraph.cycleGraph 5).Adj i j) := by
    intro i j a ha b hb
    fin_cases i
    · fin_cases j
      · have h := hP0nonadj a (by simpa [P] using ha) b (by simpa [P] using hb)
        simpa using h
      · have h := hP0Uadj a (by simpa [P] using ha) b (by simpa [P] using hb)
        exact iffTrue h (by decide)
      · have h := hP0P2nonadj a (by simpa [P] using ha) b (by simpa [P] using hb)
        exact iffFalse h (by decide)
      · have h := hP0P3nonadj a (by simpa [P] using ha) b (by simpa [P] using hb)
        exact iffFalse h (by decide)
      · have h := hP0Dadj a (by simpa [P] using ha) b (by simpa [P] using hb)
        exact iffTrue h (by decide)
    · fin_cases j
      · have h := (hP0Uadj b (by simpa [P] using hb) a (by simpa [P] using ha)).symm
        exact iffTrue h (by decide)
      · have h := hUnonadj a (by simpa [P] using ha) b (by simpa [P] using hb)
        simpa using h
      · have h := hUP2adj a (by simpa [P] using ha) b (by simpa [P] using hb)
        exact iffTrue h (by decide)
      · have h := hUP3nonadj a (by simpa [P] using ha) b (by simpa [P] using hb)
        exact iffFalse h (by decide)
      · have h := hUDnonadj a (by simpa [P] using ha) b (by simpa [P] using hb)
        exact iffFalse h (by decide)
    · fin_cases j
      · have h := hP0P2nonadj b (by simpa [P] using hb) a (by simpa [P] using ha)
        have h' : ¬L.Adj a b := fun hab => h hab.symm
        exact iffFalse h' (by decide)
      · have h := (hUP2adj b (by simpa [P] using hb) a (by simpa [P] using ha)).symm
        exact iffTrue h (by decide)
      · have h := hP2nonadj a (by simpa [P] using ha) b (by simpa [P] using hb)
        simpa using h
      · have h := hP2P3adj a (by simpa [P] using ha) b (by simpa [P] using hb)
        exact iffTrue h (by decide)
      · have h := hP2Dnonadj a (by simpa [P] using ha) b (by simpa [P] using hb)
        exact iffFalse h (by decide)
    · fin_cases j
      · have h := hP0P3nonadj b (by simpa [P] using hb) a (by simpa [P] using ha)
        have h' : ¬L.Adj a b := fun hab => h hab.symm
        exact iffFalse h' (by decide)
      · have h := hUP3nonadj b (by simpa [P] using hb) a (by simpa [P] using ha)
        have h' : ¬L.Adj a b := fun hab => h hab.symm
        exact iffFalse h' (by decide)
      · have h := (hP2P3adj b (by simpa [P] using hb) a (by simpa [P] using ha)).symm
        exact iffTrue h (by decide)
      · have h := hP3nonadj a (by simpa [P] using ha) b (by simpa [P] using hb)
        simpa using h
      · have h := hP3Dadj a (by simpa [P] using ha) b (by simpa [P] using hb)
        exact iffTrue h (by decide)
    · fin_cases j
      · have h := (hP0Dadj b (by simpa [P] using hb) a (by simpa [P] using ha)).symm
        exact iffTrue h (by decide)
      · have h := hUDnonadj b (by simpa [P] using hb) a (by simpa [P] using ha)
        have h' : ¬L.Adj a b := fun hab => h hab.symm
        exact iffFalse h' (by decide)
      · have h := hP2Dnonadj b (by simpa [P] using hb) a (by simpa [P] using ha)
        have h' : ¬L.Adj a b := fun hab => h hab.symm
        exact iffFalse h' (by decide)
      · have h := (hP3Dadj b (by simpa [P] using hb) a (by simpa [P] using ha)).symm
        exact iffTrue h (by decide)
      · have h := hDnonadj a (by simpa [P] using ha) b (by simpa [P] using hb)
        simpa using h
  let iso : L ≃g balancedC5Blowup :=
    isoBalancedC5BlowupOfFiveParts L P hPdis hPcover hPcard hPadj
  exact ⟨by simpa [L] using iso⟩

/-- The equality-case complement inherits vertex-cover number six from the
canonical blow-up. -/
theorem compl_vertexCoverNum_eq_six_of_admissible_order_ten_equality
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hfree : G.IndepSetFree 3)
    (hcard : Fintype.card V = 10) (hnotbip : ¬Gᶜ.IsBipartite)
    (hedges : #Gᶜ.edgeFinset = 20) :
    Gᶜ.vertexCoverNum = 6 := by
  obtain ⟨iso⟩ :=
    compl_iso_balancedC5Blowup_of_admissible_order_ten_equality
      G hG hfree hcard hnotbip hedges
  exact (SimpleGraph.vertexCoverNum_congr iso).trans
    balancedC5Blowup_vertexCoverNum

/-- At nineteen complementary edges, an independent five-set is impossible. -/
theorem compl_indepSetFree_five_of_admissible_order_ten_nineteen_edges
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hcard : Fintype.card V = 10)
    (hedges : #Gᶜ.edgeFinset = 19) :
    Gᶜ.IndepSetFree 5 := by
  classical
  let L := Gᶜ
  intro S hS
  let A : Finset V := S
  let B : Finset V := Aᶜ
  let C := L.between (A : Set V) (B : Set V)
  have hAcard : #A = 5 := by simpa [A] using hS.2
  have hBcard : #B = 5 := by
    dsimp [B]
    rw [Finset.card_compl, hAcard, hcard]
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have hxNot : x ∉ A := by simpa [B] using hxB
    exact hxNot hxA
  have hdisSet : Disjoint (A : Set V) (B : Set V) :=
    Finset.disjoint_coe.mpr hdis
  have hbip : C.IsBipartiteWith (A : Set V) (B : Set V) := by
    simpa [C] using
      (SimpleGraph.between_isBipartiteWith (G := L) hdisSet)
  have hAindependent : L.IsIndepSet (A : Set V) := by
    simpa [A, L] using hS.1
  have hpointLower (x : V) (hxB : x ∈ B) : 4 ≤ C.degree x := by
    have hxA : x ∉ A := fun hx => (Finset.disjoint_left.mp hdis) hx hxB
    have hSix : #(insert x A) = 6 := by
      rw [card_insert_of_notMem hxA, hAcard]
    have hfour :=
      four_le_card_induced_compl_of_admissible_six G hG (insert x A) hSix
    have hfourNat :
        4 ≤ Nat.card (L.induce ((insert x A : Finset V) : Set V)).edgeSet := by
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
      simpa [L] using hfour
    have hexact := card_induce_insert_eq_between_degree_of_independent
      L A B x hxB hdis hAindependent
    rw [hexact] at hfourNat
    simpa [C] using hfourNat
  have hsumLower : 20 ≤ ∑ x ∈ B, C.degree x := by
    have hsum : (∑ _x ∈ B, 4) ≤ ∑ x ∈ B, C.degree x :=
      Finset.sum_le_sum fun x hx => hpointLower x hx
    simpa [hBcard] using hsum
  have hcross : (∑ x ∈ B, C.degree x) = #C.edgeFinset :=
    SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hbip.symm
  have hCle : C ≤ L := SimpleGraph.between_le
  have hedgeSub : C.edgeFinset ⊆ L.edgeFinset :=
    SimpleGraph.edgeFinset_mono hCle
  have hcardLe : #C.edgeFinset ≤ #L.edgeFinset := Finset.card_le_card hedgeSub
  rw [hcross] at hsumLower
  have hLedges : #L.edgeFinset = 19 := by simpa [L] using hedges
  rw [hLedges] at hcardLe
  omega

/-- Across disjoint finite sets, a graph and its complement partition the
possible neighbors of a vertex on the opposite side. -/
theorem degree_between_comm
    {V : Type u} [Fintype V] [DecidableEq V]
    (L : SimpleGraph V) [DecidableRel L.Adj]
    (A B : Finset V) (x : V) :
    (L.between (A : Set V) (B : Set V)).degree x =
      (L.between (B : Set V) (A : Set V)).degree x := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext y
  simp [SimpleGraph.between_adj, and_comm, or_comm]

theorem degree_between_add_compl_between_eq_card
    {V : Type u} [Fintype V] [DecidableEq V]
    (L : SimpleGraph V) [DecidableRel L.Adj]
    (A B : Finset V) (hdis : Disjoint A B) (x : V) (hxA : x ∈ A) :
    (L.between (A : Set V) (B : Set V)).degree x +
        (Lᶜ.between (A : Set V) (B : Set V)).degree x = #B := by
  classical
  let C := L.between (A : Set V) (B : Set V)
  let D := Lᶜ.between (A : Set V) (B : Set V)
  have hdisSet : Disjoint (A : Set V) (B : Set V) :=
    Finset.disjoint_coe.mpr hdis
  have hCbip : C.IsBipartiteWith (A : Set V) (B : Set V) := by
    simpa [C] using
      (SimpleGraph.between_isBipartiteWith (G := L) hdisSet)
  have hDbip : D.IsBipartiteWith (A : Set V) (B : Set V) := by
    simpa [D] using
      (SimpleGraph.between_isBipartiteWith (G := Lᶜ) hdisSet)
  have hCneighbors : C.neighborFinset x = B.filter (L.Adj x) := by
    rw [SimpleGraph.isBipartiteWith_neighborFinset hCbip hxA]
    ext y
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hyB, hxyC⟩
      exact ⟨hyB, (SimpleGraph.between_adj.mp hxyC).1⟩
    · rintro ⟨hyB, hxyL⟩
      exact ⟨hyB, ⟨hxyL, Or.inl ⟨hxA, hyB⟩⟩⟩
  have hDneighbors : D.neighborFinset x = B.filter (fun y => ¬L.Adj x y) := by
    rw [SimpleGraph.isBipartiteWith_neighborFinset hDbip hxA]
    ext y
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hyB, hxyD⟩
      have hxyComp : Lᶜ.Adj x y := (SimpleGraph.between_adj.mp hxyD).1
      exact ⟨hyB, hxyComp.2⟩
    · rintro ⟨hyB, hnxy⟩
      have hxy : x ≠ y := by
        intro h
        subst y
        exact (Finset.disjoint_left.mp hdis) hxA hyB
      exact ⟨hyB, ⟨⟨hxy, hnxy⟩, Or.inl ⟨hxA, hyB⟩⟩⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree, hCneighbors, hDneighbors]
  exact Finset.card_filter_add_card_filter_not (s := B) (L.Adj x)

/-- The bipartite order-ten branch consists of two five-cliques in the
original graph, with a matching of original edges between them. -/
theorem exists_bipartition_order_ten
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Admissible G) (hcard : Fintype.card V = 10)
    (hbip : Gᶜ.IsBipartite) :
    ∃ A B : Finset V,
      #A = 5 ∧ #B = 5 ∧ Disjoint A B ∧ A ∪ B = Finset.univ ∧
      G.IsClique (A : Set V) ∧ G.IsClique (B : Set V) ∧
      (∀ a ∈ A, (G.between (A : Set V) (B : Set V)).degree a ≤ 1) ∧
      (∀ b ∈ B, (G.between (A : Set V) (B : Set V)).degree b ≤ 1) := by
  classical
  let L := Gᶜ
  obtain ⟨c⟩ := hbip
  let A : Finset V := Finset.univ.filter fun v => c v = (0 : Fin 2)
  let B : Finset V := Finset.univ.filter fun v => c v = (1 : Fin 2)
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have hx0 : c x = (0 : Fin 2) := by simpa [A] using hxA
    have hx1 : c x = (1 : Fin 2) := by simpa [B] using hxB
    omega
  have hcover : A ∪ B = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    have hx : c x = (0 : Fin 2) ∨ c x = (1 : Fin 2) := by
      by_cases hzero : c x = (0 : Fin 2)
      · exact Or.inl hzero
      · exact Or.inr (Fin.eq_one_of_ne_zero (c x) hzero)
    simpa [A, B] using hx
  have hAindependent : L.IsIndepSet (A : Set V) := by
    intro x hxA y hyA hxy hxyL
    have hx0 : c x = (0 : Fin 2) := by simpa [A] using hxA
    have hy0 : c y = (0 : Fin 2) := by simpa [A] using hyA
    exact c.valid (by simpa [L] using hxyL) (hx0.trans hy0.symm)
  have hBindependent : L.IsIndepSet (B : Set V) := by
    intro x hxB y hyB hxy hxyL
    have hx1 : c x = (1 : Fin 2) := by simpa [B] using hxB
    have hy1 : c y = (1 : Fin 2) := by simpa [B] using hyB
    exact c.valid (by simpa [L] using hxyL) (hx1.trans hy1.symm)
  have hpartUpper (P : Finset V) (hPind : L.IsIndepSet (P : Set V)) :
      #P ≤ 5 := by
    by_contra hnot
    have hlarge : 6 ≤ #P := by omega
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hlarge
    have hSind : L.IsIndepSet (S : Set V) := by
      intro x hx y hy hxy
      exact hPind (hSsub hx) (hSsub hy) hxy
    have hfour :=
      four_le_card_induced_compl_of_admissible_six G hG S hScard
    have hzero := card_induce_eq_zero_of_independent L S hSind
    change 4 ≤ #(L.induce (S : Set V)).edgeFinset at hfour
    omega
  have hAle : #A ≤ 5 := hpartUpper A hAindependent
  have hBle : #B ≤ 5 := hpartUpper B hBindependent
  have hsum : #A + #B = 10 := by
    rw [← Finset.card_union_of_disjoint hdis, hcover, Finset.card_univ, hcard]
  have hAcard : #A = 5 := by omega
  have hBcard : #B = 5 := by omega
  have hAclique : G.IsClique (A : Set V) := by
    simpa [L] using hAindependent
  have hBclique : G.IsClique (B : Set V) := by
    simpa [L] using hBindependent
  let C := L.between (A : Set V) (B : Set V)
  let D := G.between (A : Set V) (B : Set V)
  have hcrossA (a : V) (haA : a ∈ A) : 4 ≤ C.degree a := by
    have haB : a ∉ B := fun haB => (Finset.disjoint_left.mp hdis) haA haB
    have hSix : #(insert a B) = 6 := by
      rw [card_insert_of_notMem haB, hBcard]
    have hfour :=
      four_le_card_induced_compl_of_admissible_six G hG (insert a B) hSix
    have hfourNat :
        4 ≤ Nat.card (L.induce ((insert a B : Finset V) : Set V)).edgeSet := by
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
      simpa [L] using hfour
    have hexact := card_induce_insert_eq_between_degree_of_independent
      L B A a haA hdis.symm hBindependent
    rw [hexact] at hfourNat
    have hdegreeEq :
        (L.between (B : Set V) (A : Set V)).degree a = C.degree a := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree,
        ← SimpleGraph.card_neighborFinset_eq_degree]
      congr 1
      ext y
      simp [C, SimpleGraph.between_adj, and_comm, or_comm]
    rw [hdegreeEq] at hfourNat
    exact hfourNat
  have hcrossB (b : V) (hbB : b ∈ B) : 4 ≤ C.degree b := by
    have hbA : b ∉ A := fun hbA => (Finset.disjoint_left.mp hdis) hbA hbB
    have hSix : #(insert b A) = 6 := by
      rw [card_insert_of_notMem hbA, hAcard]
    have hfour :=
      four_le_card_induced_compl_of_admissible_six G hG (insert b A) hSix
    have hfourNat :
        4 ≤ Nat.card (L.induce ((insert b A : Finset V) : Set V)).edgeSet := by
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
      simpa [L] using hfour
    have hexact := card_induce_insert_eq_between_degree_of_independent
      L A B b hbB hdis hAindependent
    rw [hexact] at hfourNat
    simpa [C] using hfourNat
  have hmatchA : ∀ a ∈ A, D.degree a ≤ 1 := by
    intro a haA
    have hpartition := degree_between_add_compl_between_eq_card
      G A B hdis a haA
    have hlower := hcrossA a haA
    have hpartition' : D.degree a + C.degree a = 5 := by
      simpa [C, D, L, hBcard] using hpartition
    omega
  have hmatchB : ∀ b ∈ B, D.degree b ≤ 1 := by
    intro b hbB
    have hpartition := degree_between_add_compl_between_eq_card
      G B A hdis.symm b hbB
    have hlower := hcrossB b hbB
    have hDdegree := degree_between_comm G A B b
    have hCdegree := degree_between_comm Gᶜ A B b
    have hpartition' : D.degree b + C.degree b = 5 := by
      have hraw := hpartition
      rw [← hDdegree, ← hCdegree, hAcard] at hraw
      simpa [C, D, L] using hraw
    omega
  refine ⟨A, B, hAcard, hBcard, hdis, hcover, hAclique, hBclique, ?_, ?_⟩
  · simpa [D] using hmatchA
  · simpa [D] using hmatchB

end Erdos617
