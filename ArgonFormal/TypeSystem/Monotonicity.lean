/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.TypeSystem.NarrowEnv
import ArgonFormal.Reasoning.Fixpoint

/-!
# Monotonicity of Narrowing Through Fixpoint Computation

Proves that narrowing environments are preserved through each step of the
stratified fixpoint computation. The key results:

1. Every `MonotoneRule` application is inflationary (state goes up)
2. Folding inflationary operations preserves the ordering
3. Iterating an inflationary operation preserves the ordering
4. Therefore, narrowings established at any point persist through the fixpoint

These results are about the STATE, not about the typing judgment. They establish
that the fixpoint computation is inflationary, which combined with the
upward-closure of narrowing predicates (`holds_mono`) gives soundness.
-/

variable {C A : Type} [DecidableEq C] [DecidableEq A] [Fintype C] [Fintype A]

/-! ## Inflationarity of Individual Rules -/

omit [Fintype C] [Fintype A] in
/-- A `MonotoneRule` application is inflationary: `s ≤ r.apply s`.

Cat1 rules only add IS values to CAN positions (by `only_adds_is`) and leave
other positions unchanged (by `axis_local`). Both changes are ≥ in the
information ordering. -/
theorem MonotoneRule.inflationary (r : MonotoneRule C A) (s : State C A) :
    s ≤ r.apply s := by
  intro c' a'
  by_cases ha : a' = r.axis
  · subst ha
    by_cases hcan : s c' r.axis = .can
    · exact (le_of_eq hcan).trans (MetaValue.can_le _)
    · exact le_of_eq (r.only_adds_is s c' hcan).symm
  · exact le_of_eq (r.axis_local s c' a' ha).symm

/-! ## Inflationary Folds -/

/-- Folding inflationary operations over a list is inflationary.

If each step `f a b` satisfies `a ≤ f a b`, then the entire fold
produces a result ≥ the initial value. -/
theorem foldl_inflationary {α : Type*} {β : Type*} [Preorder α]
    {f : α → β → α} (h : ∀ (a : α) (b : β), a ≤ f a b)
    (l : List β) (init : α) :
    init ≤ l.foldl f init := by
  induction l generalizing init with
  | nil => exact le_refl init
  | cons b l' ih =>
    simp only [List.foldl]
    exact le_trans (h init b) (ih (f init b))

omit [Fintype C] [Fintype A] in
/-- Composing monotone rules is inflationary: `s ≤ composeMonotone rules s`. -/
theorem composeMonotone_inflationary (rules : List (MonotoneRule C A)) (s : State C A) :
    s ≤ composeMonotone rules s := by
  exact foldl_inflationary (fun s r => MonotoneRule.inflationary r s) rules s

/-! ## Inflationary Iteration -/

/-- Iterating an inflationary function preserves the ordering:
`x ≤ Nat.iterate f n x`. -/
theorem iterate_inflationary {α : Type*} [Preorder α]
    {f : α → α} (h : ∀ (a : α), a ≤ f a) :
    ∀ (n : Nat) (x : α), x ≤ Nat.iterate f n x := by
  intro n
  induction n with
  | zero => intro x; exact le_refl x
  | succ n ih =>
    intro x
    exact le_trans (h x) (ih (f x))

/-- `cat1Fixpoint` is inflationary: `s ≤ cat1Fixpoint rules s`. -/
theorem cat1Fixpoint_inflationary (rules : List (MonotoneRule C A)) (s : State C A) :
    s ≤ cat1Fixpoint rules s := by
  unfold cat1Fixpoint iterateToFixpoint
  simp only
  exact iterate_inflationary (composeMonotone_inflationary rules) _ s

/-! ## Narrowing Preservation Through Cat1 -/

omit [Fintype C] [Fintype A] in
/-- Narrowing is preserved through a single Cat1 rule application. -/
theorem narrowing_preserved_cat1_step (r : MonotoneRule C A) (env : NarrowEnv C A)
    (s : State C A) (h : env.satisfiedBy s) :
    env.satisfiedBy (r.apply s) :=
  env.satisfiedBy_mono (MonotoneRule.inflationary r s) h

/-- Narrowing is preserved through the Cat1 fixpoint computation. -/
theorem narrowing_preserved_cat1_fixpoint (rules : List (MonotoneRule C A))
    (env : NarrowEnv C A) (s : State C A) (h : env.satisfiedBy s) :
    env.satisfiedBy (cat1Fixpoint rules s) :=
  env.satisfiedBy_mono (cat1Fixpoint_inflationary rules s) h
