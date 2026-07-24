/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Mathlib

/-!
# Correctness facts for the E058 lexicographic sorting encoding

The exterior-row quotient introduces one prefix-equality variable at every
bit position.  These definitions and lemmas are the semantic content of all
clauses emitted by `CNF.lexicographic_leq`.
-/

@[expose] public section

namespace Erdos617

/-- The first `i` entries of two proposition-valued rows agree. -/
def propPrefixEqual (left right : ℕ → Prop) (i : ℕ) : Prop :=
  ∀ j, j < i → (left j ↔ right j)

/-- Lexicographic nondecreasing order on the first `n` Boolean positions,
with `False < True`. -/
def propLexicographicLE (left right : ℕ → Prop) (n : ℕ) : Prop :=
  ∀ i, i < n → propPrefixEqual left right i → left i → right i

@[simp]
theorem propPrefixEqual_zero (left right : ℕ → Prop) :
    propPrefixEqual left right 0 := by
  intro j hj
  omega

theorem propPrefixEqual_succ_iff (left right : ℕ → Prop) (i : ℕ) :
    propPrefixEqual left right (i + 1) ↔
      propPrefixEqual left right i ∧ (left i ↔ right i) := by
  constructor
  · intro h
    refine ⟨fun j hj => h j (by omega), h i (by omega)⟩
  · rintro ⟨hprefix, hi⟩ j hj
    by_cases hji : j = i
    · simpa [hji] using hi
    · exact hprefix j (by omega)

/-- A current prefix-equality variable implies the previous one. -/
theorem propPrefixEqual_previous (left right : ℕ → Prop) {i : ℕ}
    (h : propPrefixEqual left right (i + 1)) :
    propPrefixEqual left right i :=
  (propPrefixEqual_succ_iff left right i).mp h |>.1

/-- A current prefix-equality variable implies `left → right` at the current
position. -/
theorem propPrefixEqual_current_forward (left right : ℕ → Prop) {i : ℕ}
    (h : propPrefixEqual left right (i + 1)) (hl : left i) :
    right i :=
  ((propPrefixEqual_succ_iff left right i).mp h).2.mp hl

/-- A current prefix-equality variable implies `right → left` at the current
position. -/
theorem propPrefixEqual_current_reverse (left right : ℕ → Prop) {i : ℕ}
    (h : propPrefixEqual left right (i + 1)) (hr : right i) :
    left i :=
  ((propPrefixEqual_succ_iff left right i).mp h).2.mpr hr

/-- Equal false bits extend a prefix equality. -/
theorem propPrefixEqual_succ_of_both_false (left right : ℕ → Prop) {i : ℕ}
    (hprefix : propPrefixEqual left right i)
    (hl : ¬left i) (hr : ¬right i) :
    propPrefixEqual left right (i + 1) := by
  rw [propPrefixEqual_succ_iff]
  exact ⟨hprefix, iff_of_false hl hr⟩

/-- Equal true bits extend a prefix equality. -/
theorem propPrefixEqual_succ_of_both_true (left right : ℕ → Prop) {i : ℕ}
    (hprefix : propPrefixEqual left right i)
    (hl : left i) (hr : right i) :
    propPrefixEqual left right (i + 1) := by
  rw [propPrefixEqual_succ_iff]
  exact ⟨hprefix, iff_of_true hl hr⟩

/-- The lexicographic-order clause at a position whose previous prefix is
equal. -/
theorem propLexicographicLE_at (left right : ℕ → Prop) {n i : ℕ}
    (hlex : propLexicographicLE left right n) (hi : i < n)
    (hprefix : propPrefixEqual left right i) (hl : left i) :
    right i :=
  hlex i hi hprefix hl

/-- The first-position order clause, where the empty prefix is definitionally
equal. -/
theorem propLexicographicLE_zero (left right : ℕ → Prop) {n : ℕ}
    (hlex : propLexicographicLE left right n) (hn : 0 < n)
    (hl : left 0) :
    right 0 :=
  hlex 0 hn (propPrefixEqual_zero left right) hl

end Erdos617
