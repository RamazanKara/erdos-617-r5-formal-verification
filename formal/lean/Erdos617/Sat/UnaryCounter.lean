/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Mathlib

/-!
# Correctness facts for the E058 unary cardinality encoding

The Python CNF generators use the same full unary dynamic-programming
counter.  `unaryCounter p i k` says that at least `k` of the first `i`
propositions are true.  The lemmas below are the semantic content of every
counter clause emitted by `CNF.exactly_k` and `CNF.at_most_k`.
-/

@[expose] public section

open Finset

namespace Erdos617

/-- Number of true propositions among indices `0, ..., i-1`. -/
def prefixTrueCount (p : ℕ → Prop) [DecidablePred p] (i : ℕ) : ℕ :=
  #(Finset.range i |>.filter p)

/-- Unary counter proposition: at least `k` of the first `i` inputs hold. -/
def unaryCounter (p : ℕ → Prop) [DecidablePred p] (i k : ℕ) : Prop :=
  k ≤ prefixTrueCount p i

theorem prefixTrueCount_succ (p : ℕ → Prop) [DecidablePred p] (i : ℕ) :
    prefixTrueCount p (i + 1) =
      prefixTrueCount p i + if p i then 1 else 0 := by
  by_cases hi : p i
  · simp [prefixTrueCount, Finset.range_add_one, Finset.filter_insert, hi]
  · simp [prefixTrueCount, Finset.range_add_one, Finset.filter_insert, hi]

theorem prefixTrueCount_le (p : ℕ → Prop) [DecidablePred p] (i : ℕ) :
    prefixTrueCount p i ≤ i := by
  simpa [prefixTrueCount] using
    Finset.card_le_card (Finset.filter_subset p (Finset.range i))

/-- A previously reached threshold remains reached after one more input. -/
theorem unaryCounter_of_previous (p : ℕ → Prop) [DecidablePred p]
    {i k : ℕ} (h : unaryCounter p i k) :
    unaryCounter p (i + 1) k := by
  by_cases hi : p i <;>
    simp [unaryCounter, prefixTrueCount_succ, hi] at h ⊢ <;> omega

/-- Reaching threshold one comes either from the previous prefix or from the
new input. -/
theorem unaryCounter_one_elim (p : ℕ → Prop) [DecidablePred p]
    {i : ℕ} (h : unaryCounter p (i + 1) 1) :
    unaryCounter p i 1 ∨ p i := by
  by_cases hi : p i
  · exact Or.inr hi
  · left
    have hcount : 1 ≤ prefixTrueCount p i := by
      simpa only [unaryCounter, prefixTrueCount_succ, if_neg hi,
        Nat.add_zero] using h
    exact hcount

/-- A true input reaches threshold one. -/
theorem unaryCounter_one_of_input (p : ℕ → Prop) [DecidablePred p]
    {i : ℕ} (h : p i) :
    unaryCounter p (i + 1) 1 := by
  simp [unaryCounter, prefixTrueCount_succ, h]

/-- Reaching a positive successor threshold comes either from the same
threshold in the previous prefix or the preceding threshold there. -/
theorem unaryCounter_succ_elim_previous (p : ℕ → Prop) [DecidablePred p]
    {i k : ℕ} (h : unaryCounter p (i + 1) (k + 1)) :
    unaryCounter p i (k + 1) ∨ unaryCounter p i k := by
  by_cases hi : p i
  · right
    simp [unaryCounter, prefixTrueCount_succ, hi] at h ⊢
    omega
  · left
    simpa [unaryCounter, prefixTrueCount_succ, hi] using h

/-- If a successor threshold was not already reached, its last input must be
true. -/
theorem unaryCounter_succ_elim_input (p : ℕ → Prop) [DecidablePred p]
    {i k : ℕ} (h : unaryCounter p (i + 1) (k + 1))
    (hnot : ¬unaryCounter p i (k + 1)) :
    p i := by
  by_contra hi
  exact hnot (by
    simpa [unaryCounter, prefixTrueCount_succ, hi] using h)

/-- The previous threshold together with a true new input reaches the next
threshold. -/
theorem unaryCounter_succ_of_previous_of_input
    (p : ℕ → Prop) [DecidablePred p] {i k : ℕ}
    (hprevious : unaryCounter p i k) (hinput : p i) :
    unaryCounter p (i + 1) (k + 1) := by
  simp [unaryCounter, prefixTrueCount_succ, hinput] at hprevious ⊢
  omega

/-- A prefix of length `i` cannot reach threshold `i+1`. -/
theorem not_unaryCounter_succ_self (p : ℕ → Prop) [DecidablePred p]
    (i : ℕ) :
    ¬unaryCounter p i (i + 1) := by
  intro h
  exact (Nat.not_succ_le_self i)
    (h.trans (prefixTrueCount_le p i))

/-- At the first possible occurrence of threshold `i+1`, the preceding
threshold must already hold. -/
theorem unaryCounter_diagonal_elim_previous
    (p : ℕ → Prop) [DecidablePred p] {i : ℕ}
    (h : unaryCounter p (i + 1) (i + 1)) :
    unaryCounter p i i := by
  rcases unaryCounter_succ_elim_previous p h with hbad | hgood
  · exact False.elim (not_unaryCounter_succ_self p i hbad)
  · exact hgood

/-- At the first possible occurrence of threshold `i+1`, the new input must
be true. -/
theorem unaryCounter_diagonal_elim_input
    (p : ℕ → Prop) [DecidablePred p] {i : ℕ}
    (h : unaryCounter p (i + 1) (i + 1)) :
    p i :=
  unaryCounter_succ_elim_input p h (not_unaryCounter_succ_self p i)

/-- Exact-count terminal units for a unary counter. -/
theorem unaryCounter_terminal_of_count_eq
    (p : ℕ → Prop) [DecidablePred p] {i k : ℕ}
    (hcount : prefixTrueCount p i = k) :
    unaryCounter p i k ∧ ¬unaryCounter p i (k + 1) := by
  simp [unaryCounter, hcount]

end Erdos617
