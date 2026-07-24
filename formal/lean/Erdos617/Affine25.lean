/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The affine-plane lower construction at `r = 5`

The point set is `Fin 5 × Fin 5`.  Slopes `0,1,2,3` receive their own
colours.  Every vertical edge and every remaining (slope `4`) edge receives
colour `4`.  The finite direction arithmetic below is checked by Lean's
kernel evaluator (`decide` only).  The global six-set claim
is then the ordinary pigeonhole argument on the five parallel lines in a
fixed direction.
-/

@[expose] public section

open Finset

namespace Erdos617

abbrev AffinePoint := Fin 5 × Fin 5

/-- Whether the line through `p,q` has the indicated finite slope. -/
abbrev HasSlope (m : Fin 5) (p q : AffinePoint) : Prop :=
  q.2 - p.2 = m * (q.1 - p.1)

/-- Slopes `0,1,2,3` are separate; vertical and slope `4` are merged. -/
abbrev affineRawColor (p q : AffinePoint) : Fin 5 :=
  if HasSlope 0 p q then 0
  else if HasSlope 1 p q then 1
  else if HasSlope 2 p q then 2
  else if HasSlope 3 p q then 3
  else 4

/-- Coordinate indexing the five parallel lines belonging to colour `c`. -/
abbrev lineCoordinate (c : Fin 5) (p : AffinePoint) : Fin 5 :=
  if c = 0 then p.2
  else if c = 1 then p.2 - p.1
  else if c = 2 then p.2 - 2 * p.1
  else if c = 3 then p.2 - 3 * p.1
  else p.1

/-- Reversing an edge does not change its colour.  This is a closed check of
all `25²` ordered point pairs in the five-element modular arithmetic. -/
theorem affineRawColor_comm : ∀ p q : AffinePoint,
    affineRawColor q p = affineRawColor p q := by
  decide

/-- Two distinct points on one of the five parallel lines indexed by `c`
span an edge of colour `c`.  This closed kernel computation covers all
`5 · 25²` choices and, in particular, validates the merged colour `4` case. -/
theorem affineRawColor_of_lineCoordinate_eq : ∀ c : Fin 5, ∀ p q : AffinePoint,
    p ≠ q → lineCoordinate c p = lineCoordinate c q → affineRawColor p q = c := by
  decide

/-- The affine edge colouring on its natural point type. -/
def affineColoring : EdgeColoring AffinePoint (Fin 5) :=
  SimpleGraph.EdgeLabeling.mk (fun p q _ => affineRawColor p q)
    (fun p q _ => affineRawColor_comm p q)

@[simp]
theorem affineColoring_get (p q : AffinePoint) (h : p ≠ q) :
    affineColoring.get p q h = affineRawColor p q := by
  rfl

theorem card_affinePoint : Fintype.card AffinePoint = 25 := by
  decide

/-- Every six affine points see every one of the five colours. -/
theorem affineColoring_isCounterexample : IsCounterexample 6 affineColoring := by
  intro S hS c
  have hlt : #(univ : Finset (Fin 5)) < #S := by
    simp [hS]
  obtain ⟨p, hp, q, hq, hpq, hline⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := S)
      (t := (univ : Finset (Fin 5))) hlt
      (f := lineCoordinate c) (by intro x hx; simp)
  exact ⟨p, hp, q, hq, hpq,
    affineRawColor_of_lineCoordinate_eq c p q hpq hline⟩

/-- The standard row-major equivalence between `Fin 25` and affine points. -/
def fin25EquivAffinePoint : Fin 25 ≃ AffinePoint :=
  (finProdFinEquiv : AffinePoint ≃ Fin (5 * 5)).symm

/-- The same affine colouring, now on the exact project vertex type `Fin 25`. -/
def affine25Coloring : EdgeColoring (Fin 25) (Fin 5) :=
  pullbackEquiv affineColoring fin25EquivAffinePoint

/-- The exact `Fin 25` colouring is a counterexample to the corresponding
upper statement; equivalently, it establishes the sharp lower bound `> 25`. -/
theorem affine25Coloring_isCounterexample :
    IsCounterexample 6 affine25Coloring := by
  exact affineColoring_isCounterexample.pullbackEquiv fin25EquivAffinePoint

theorem not_upperStatement_fin25 : ¬UpperStatement (Fin 25) (Fin 5) 6 := by
  intro h
  obtain ⟨S, hS, c, hc⟩ := h affine25Coloring
  exact hc (affine25Coloring_isCounterexample S hS c)

end Erdos617
