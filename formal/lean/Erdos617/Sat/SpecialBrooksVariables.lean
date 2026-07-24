/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.Sat.SpecialBrooksBridge
public import Erdos617.Sat.UnaryCounter
public import Erdos617.Sat.Lexicographic
public import Mathlib.Tactic.Sat.FromLRAT

/-!
# Exact variable semantics for the special-Brooks CNFs

The lists in this file mirror the allocation order common to the E038,
E042, E043, and E045 generators:

* 325 lexicographically ordered graph-edge variables;
* 3,510 full unary degree-counter variables; and
* five prefix-equality variables per requested exterior-row comparison.

The definitions are transparent.  A later generated bridge proves each
reduced input clause against these semantics inside the Lean kernel.
-/

@[expose] public section

open Finset
open Mathlib.Tactic.Sat

namespace Erdos617

/-- Semantic name of a SAT variable.  Natural-number fields deliberately
match the integer labels used by the external generators. -/
inductive R5VariableName where
  | edge (left right : ℕ)
  | degreeCounter (vertex prefixLength threshold : ℕ)
  | lexPrefix (leftExterior rightExterior position : ℕ)
  deriving DecidableEq, Repr

/-- The 325 edge names, in Python `itertools.combinations(range(26), 2)`
order. -/
def r5EdgeVariableNames : List R5VariableName :=
  (List.range 26).flatMap fun left =>
    (List.range (25 - left)).map fun offset =>
      .edge left (left + offset + 1)

/-- The 3,510 names allocated by the 26 exact-degree-five unary counters. -/
def r5DegreeCounterVariableNames : List R5VariableName :=
  (List.range 26).flatMap fun vertex =>
    (List.range 25).flatMap fun position =>
      (List.range (min (position + 1) 6)).map fun threshold =>
        .degreeCounter vertex (position + 1) (threshold + 1)

/-- All branch-independent variable names. -/
def r5BaseVariableNames : List R5VariableName :=
  r5EdgeVariableNames ++ r5DegreeCounterVariableNames

/-- Prefix-equality names for an ordered list of exterior-row comparisons. -/
def r5LexVariableNames (comparisons : List (ℕ × ℕ)) :
    List R5VariableName :=
  comparisons.flatMap fun comparison =>
    (List.range 5).map fun position =>
      .lexPrefix comparison.1 comparison.2 position

/-- Complete variable allocation for a requested exterior sorting quotient. -/
def r5VariableNames (comparisons : List (ℕ × ℕ)) :
    List R5VariableName :=
  r5BaseVariableNames ++ r5LexVariableNames comparisons

/-- The 19 consecutive comparisons used by E038, E042, and E043. -/
def r5FullExteriorComparisons : List (ℕ × ℕ) :=
  (List.range 19).map fun offset => (offset + 6, offset + 7)

/-- The 17 within-class comparisons used by E045. -/
def r5ZeroAnchorComparisons : List (ℕ × ℕ) :=
  ((List.range 4).map fun offset => (offset + 7, offset + 8)) ++
  ((List.range 13).map fun offset => (offset + 12, offset + 13))

@[simp]
theorem length_r5EdgeVariableNames :
    r5EdgeVariableNames.length = 325 := by
  set_option maxRecDepth 100000 in decide

@[simp]
theorem length_r5DegreeCounterVariableNames :
    r5DegreeCounterVariableNames.length = 3510 := by
  set_option maxRecDepth 100000 in decide

@[simp]
theorem length_r5BaseVariableNames :
    r5BaseVariableNames.length = 3835 := by
  set_option maxRecDepth 100000 in decide

@[simp]
theorem length_r5FullExteriorComparisons :
    r5FullExteriorComparisons.length = 19 := by
  decide

@[simp]
theorem length_r5ZeroAnchorComparisons :
    r5ZeroAnchorComparisons.length = 17 := by
  decide

@[simp]
theorem length_r5VariableNames_full :
    (r5VariableNames r5FullExteriorComparisons).length = 3930 := by
  set_option maxRecDepth 100000 in decide

@[simp]
theorem length_r5VariableNames_zeroAnchor :
    (r5VariableNames r5ZeroAnchorComparisons).length = 3920 := by
  set_option maxRecDepth 100000 in decide

/-- Incident-edge proposition at the generator's zero-based position within
the 25 vertices other than `vertex`. -/
def r5IncidentProp (G : SimpleGraph (Fin 26)) (vertex position : ℕ) : Prop :=
  if hv : vertex < 26 then
    if hp : position < 25 then
      G.Adj ⟨vertex, hv⟩ (Fin.succAbove ⟨vertex, hv⟩ ⟨position, hp⟩)
    else False
  else False

instance instDecidableR5IncidentProp
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (vertex position : ℕ) : Decidable (r5IncidentProp G vertex position) := by
  unfold r5IncidentProp
  infer_instance

/-- One bit of an exterior vertex's adjacency row into fixed neighbors
`1, ..., 5`. -/
def r5ExteriorPatternBit
    (G : SimpleGraph (Fin 26)) (exterior position : ℕ) : Prop :=
  if he : exterior < 26 then
    if hp : position < 5 then
      G.Adj ⟨position + 1, by omega⟩ ⟨exterior, he⟩
    else False
  else False

instance instDecidableR5ExteriorPatternBit
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (exterior position : ℕ) :
    Decidable (r5ExteriorPatternBit G exterior position) := by
  unfold r5ExteriorPatternBit
  infer_instance

/-- Interpretation of every variable name as a proposition about `G`. -/
def r5InterpretVariable (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] :
    R5VariableName → Prop
  | .edge left right =>
      if hl : left < 26 then
        if hr : right < 26 then G.Adj ⟨left, hl⟩ ⟨right, hr⟩ else False
      else False
  | .degreeCounter vertex prefixLength threshold =>
      unaryCounter (r5IncidentProp G vertex) prefixLength threshold
  | .lexPrefix left right position =>
      propPrefixEqual
        (r5ExteriorPatternBit G left)
        (r5ExteriorPatternBit G right)
        (position + 1)

/-- Exact graph-derived valuation for one comparison scheme. -/
def r5Valuation (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (comparisons : List (ℕ × ℕ)) : Sat.Valuation :=
  Sat.Valuation.mk <|
    (r5VariableNames comparisons).map (r5InterpretVariable G)

/-- Lookup principle for Mathlib's recursively represented SAT valuation. -/
theorem valuationMk_iff_of_getElem?_eq
    {propositions : List Prop} {index : ℕ} {p : Prop}
    (hlookup : propositions[index]? = some p) :
    Sat.Valuation.mk propositions index ↔ p := by
  induction propositions generalizing index p with
  | nil =>
      simp at hlookup
  | cons head tail ih =>
      cases index with
      | zero =>
          have hp : head = p := Option.some.inj hlookup
          subst p
          rfl
      | succ index =>
          exact ih hlookup

/-- A checked name lookup exposes the corresponding graph proposition in the
exact SAT valuation. -/
theorem r5Valuation_iff_of_name_lookup
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (comparisons : List (ℕ × ℕ)) {index : ℕ} {name : R5VariableName}
    (hlookup : (r5VariableNames comparisons)[index]? = some name) :
    r5Valuation G comparisons index ↔ r5InterpretVariable G name := by
  apply valuationMk_iff_of_getElem?_eq
  simpa using congrArg (Option.map (r5InterpretVariable G)) hlookup

/-- The 25 incident propositions enumerate the graph's actual neighbors of a
vertex exactly once. -/
theorem prefixTrueCount_r5IncidentProp_twentyFive
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (v : Fin 26) :
    prefixTrueCount (r5IncidentProp G v) 25 = G.degree v := by
  classical
  calc
    prefixTrueCount (r5IncidentProp G v) 25 =
        ∑ i ∈ Finset.range 25,
          if r5IncidentProp G v i then 1 else 0 := by
      simp [prefixTrueCount]
    _ = ∑ i : Fin 25,
          if G.Adj v (v.succAbove i) then 1 else 0 := by
      rw [Finset.sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      simp [r5IncidentProp, i.isLt]
    _ = ∑ w : Fin 26, if G.Adj v w then 1 else 0 := by
      rw [Fin.sum_univ_succAbove (fun w : Fin 26 =>
        if G.Adj v w then 1 else 0) v]
      simp
    _ = ∑ w : Fin 26,
          if w ∈ G.neighborFinset v then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro w hw
      by_cases hadj : G.Adj v w
      · simp [hadj, G.mem_neighborFinset]
      · simp [hadj, G.mem_neighborFinset]
    _ = #(G.neighborFinset v) := by
      have hsum := Finset.sum_boole (R := ℕ)
        (fun w => w ∈ G.neighborFinset v) Finset.univ
      rw [Finset.filter_mem_eq_of_subset (Finset.subset_univ _)] at hsum
      exact hsum
    _ = G.degree v := G.card_neighborFinset_eq_degree v

/-- Exact degree five supplies both terminal units of every degree counter. -/
theorem r5DegreeCounterTerminal
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ v, G.degree v = 5) (v : Fin 26) :
    unaryCounter (r5IncidentProp G v) 25 5 ∧
      ¬unaryCounter (r5IncidentProp G v) 25 6 := by
  apply unaryCounter_terminal_of_count_eq
  rw [prefixTrueCount_r5IncidentProp_twentyFive, hregular]

end Erdos617
