/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.Sat.ZeroAnchorOrbitCertificate

/-!
# Finite predicate-preserving relabelings

The E043 bridge must move a prescribed subset of a finite vertex class onto
the graph's actual subset of the same size while leaving every vertex outside
that class fixed.  These definitions isolate that elementary permutation
construction.
-/

@[expose] public section

open Finset Fintype

namespace Erdos617

/-- A permutation carrying the target predicate class onto the source
predicate class. -/
noncomputable def r5PredicateTransportPerm
    {α : Type*} [Fintype α] [DecidableEq α]
    (target source : α → Prop)
    [DecidablePred target] [DecidablePred source]
    (hcard :
      Fintype.card {value // target value} =
        Fintype.card {value // source value}) :
    Equiv.Perm α := by
  let yesEquiv :
      {value // target value} ≃ {value // source value} :=
    Fintype.equivOfCardEq hcard
  have hcardNo :
      Fintype.card {value // ¬target value} =
        Fintype.card {value // ¬source value} := by
    rw [Fintype.card_subtype_compl,
      Fintype.card_subtype_compl, hcard]
  let noEquiv :
      {value // ¬target value} ≃ {value // ¬source value} :=
    Fintype.equivOfCardEq hcardNo
  exact (Equiv.sumCompl target).symm |>.trans
    ((yesEquiv.sumCongr noEquiv).trans
      (Equiv.sumCompl source))

theorem r5PredicateTransportPerm_mem_iff
    {α : Type*} [Fintype α] [DecidableEq α]
    (target source : α → Prop)
    [DecidablePred target] [DecidablePred source]
    (hcard :
      Fintype.card {value // target value} =
        Fintype.card {value // source value})
    (value : α) :
    source (r5PredicateTransportPerm target source hcard value) ↔
      target value := by
  classical
  have hcardNo :
      Fintype.card {value // ¬target value} =
        Fintype.card {value // ¬source value} := by
    rw [Fintype.card_subtype_compl,
      Fintype.card_subtype_compl, hcard]
  by_cases htarget : target value
  · have happly :
        r5PredicateTransportPerm target source hcard value =
          (Fintype.equivOfCardEq hcard
            ⟨value, htarget⟩).val := by
      simp only [r5PredicateTransportPerm, Equiv.trans_apply,
        Equiv.sumCompl_symm_apply_of_pos htarget,
        Equiv.sumCongr_apply, Sum.map_inl,
        Equiv.sumCompl_apply_inl]
    rw [happly]
    constructor
    · intro _
      exact htarget
    · intro _
      exact ((Fintype.equivOfCardEq hcard)
        ⟨value, htarget⟩).property
  · have happly :
        r5PredicateTransportPerm target source hcard value =
          (Fintype.equivOfCardEq hcardNo
            ⟨value, htarget⟩).val := by
      simp only [r5PredicateTransportPerm, Equiv.trans_apply,
        Equiv.sumCompl_symm_apply_of_neg htarget,
        Equiv.sumCongr_apply, Sum.map_inr,
        Equiv.sumCompl_apply_inr]
    rw [happly]
    constructor
    · intro hsource
      exact False.elim
        (((Fintype.equivOfCardEq hcardNo)
          ⟨value, htarget⟩).property hsource)
    · intro htarget'
      exact False.elim (htarget htarget')

/-- Extend a predicate transport on one vertex class by the identity on its
complement. -/
noncomputable def r5BlockPredicateTransportPerm
    {α : Type*} [Fintype α] [DecidableEq α]
    (block : α → Prop) [DecidablePred block]
    (target source : {value // block value} → Prop)
    [DecidablePred target] [DecidablePred source]
    (hcard :
      Fintype.card {value // target value} =
        Fintype.card {value // source value}) :
    Equiv.Perm α :=
  (r5PredicateTransportPerm target source hcard).subtypeCongr
    (Equiv.refl {value // ¬block value})

@[simp]
theorem r5BlockPredicateTransportPerm_apply_outside
    {α : Type*} [Fintype α] [DecidableEq α]
    (block : α → Prop) [DecidablePred block]
    (target source : {value // block value} → Prop)
    [DecidablePred target] [DecidablePred source]
    (hcard :
      Fintype.card {value // target value} =
        Fintype.card {value // source value})
    (value : α) (hvalue : ¬block value) :
    r5BlockPredicateTransportPerm
        block target source hcard value =
      value := by
  simp [r5BlockPredicateTransportPerm, hvalue]

theorem r5BlockPredicateTransportPerm_apply_inside
    {α : Type*} [Fintype α] [DecidableEq α]
    (block : α → Prop) [DecidablePred block]
    (target source : {value // block value} → Prop)
    [DecidablePred target] [DecidablePred source]
    (hcard :
      Fintype.card {value // target value} =
        Fintype.card {value // source value})
    (value : α) (hvalue : block value) :
    r5BlockPredicateTransportPerm
        block target source hcard value =
      r5PredicateTransportPerm
        target source hcard ⟨value, hvalue⟩ := by
  simp [r5BlockPredicateTransportPerm, hvalue]

/-- The nested subtype cardinal used by predicate transport is the cardinal
of the corresponding filtered ambient finset. -/
theorem r5CardNestedSubtype_eq_filter_univ
    {α : Type*} [Fintype α]
    (block source : α → Prop)
    [DecidablePred block] [DecidablePred source] :
    Fintype.card
        ({value : {ambient : α // block ambient} //
          source value}) =
      #(Finset.univ.filter fun value =>
        block value ∧ source value) := by
  classical
  let selected : Finset α :=
    Finset.univ.filter fun value =>
      block value ∧ source value
  let equivalence :
      {value : {ambient : α // block ambient} //
          source value} ≃
        {value : α // value ∈ selected} := {
    toFun := fun value =>
      ⟨value.1.1, by
        change value.1.1 ∈
          Finset.univ.filter fun ambient =>
            block ambient ∧ source ambient
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, value.1.2, value.2⟩⟩
    invFun := fun value =>
      ⟨⟨value.1, by
          have hvalue : value.1 ∈
              Finset.univ.filter fun ambient =>
                block ambient ∧ source ambient := by
            exact value.2
          exact (Finset.mem_filter.mp hvalue).2.1⟩,
        by
          have hvalue : value.1 ∈
              Finset.univ.filter fun ambient =>
                block ambient ∧ source ambient := by
            exact value.2
          exact (Finset.mem_filter.mp hvalue).2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }
  calc
    Fintype.card
        ({value : {ambient : α // block ambient} //
          source value}) =
        Fintype.card {value : α // value ∈ selected} :=
      Fintype.card_congr equivalence
    _ = #selected := Fintype.card_coe selected
    _ = #(Finset.univ.filter fun value =>
          block value ∧ source value) := rfl

end Erdos617
