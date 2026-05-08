/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.Reasoning.Fixpoint

/-!
# Theorem 5: CAN Stability

## Statement

If a meta-property assignment is CAN at the end of the stratified fixpoint, then:

1. No existing rule (Cat1 or Cat2) can resolve it.
2. Any consistent extension of the rule set (adding more rules that respect acyclicity)
   can resolve it to at most one of IS or NOT.
3. An extension that would assign both IS and NOT to the same (concept, axis) pair
   is inconsistent — detectable by constraint checking.

This justifies treating CAN as `is unknown` at the language level: it represents
genuine indeterminacy given the current rules, not incomplete computation.

## Proof Strategy

Part 1 follows from the fixpoint property (stability, Theorem 1.3).
Part 2 follows from the least fixpoint property: any extension produces a state ≥ the
current fixpoint in the information ordering. Since IS and NOT are incomparable,
a state can be extended to have one or the other but not both.
Part 3 follows from the fact that IS and NOT are incomparable in the information
ordering — assigning both violates the partial order.
-/

variable {C A : Type} [DecidableEq C] [DecidableEq A] [Fintype C] [Fintype A]

/-- A state is consistent if no (concept, axis) pair is assigned both IS and NOT.
(In our representation, this is automatic since each pair maps to exactly one MetaValue.
But we state it explicitly for extensions that might try to merge two states.) -/
def State.consistent (s : State C A) : Prop :=
  ∀ c a, ¬(s c a = .is ∧ s c a = .not)

/-- Every state in our representation is automatically consistent. -/
theorem State.always_consistent (s : State C A) : s.consistent := by
  intro c a ⟨h1, h2⟩
  rw [h1] at h2
  exact MetaValue.noConfusion h2

/-- **Theorem 5.1: CAN means no rule resolves it.**
If the fixpoint assigns CAN to (c, a), then no Cat1 or Cat2 rule changes it. -/
theorem can_means_unresolvable (rs : StratifiedRuleSet C A)
    (axisSorted : List A)
    (c : C) (a : A)
    (h_stable_cat1 : ∀ a', ∀ r ∈ rs.cat1 a',
      r.apply (stratifiedFixpoint rs axisSorted State.initial) =
      stratifiedFixpoint rs axisSorted State.initial)
    (h_stable_cat2 : ∀ a', ∀ r ∈ rs.cat2 a',
      r.apply (stratifiedFixpoint rs axisSorted State.initial) =
      stratifiedFixpoint rs axisSorted State.initial) :
    (stratifiedFixpoint rs axisSorted State.initial) c a = .can →
    -- No Cat1 rule changes it
    (∀ r ∈ rs.cat1 a,
      (r.apply (stratifiedFixpoint rs axisSorted State.initial)) c a = .can) ∧
    -- No Cat2 rule changes it
    (∀ r ∈ rs.cat2 a,
      (r.apply (stratifiedFixpoint rs axisSorted State.initial)) c a = .can) := by
  intro h_can
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · -- By stability, r.apply result = result
    have := h_stable_cat1 a r hr
    simp only [this]
    exact h_can
  · have := h_stable_cat2 a r hr
    simp only [this]
    exact h_can

/-- **Theorem 5.2: Extensions are monotone.**
Adding more rules (while maintaining acyclicity) produces a fixpoint that is
≥ the original in the information ordering.

Intuition: more rules can only resolve CAN values — they can't change IS to NOT
or NOT to IS, because rules are monotone (Cat1 only adds IS, Cat2 only adds NOT)
and determined values are never overwritten.

## Hypothesis shape

- **Cat1**: set inclusion suffices. `cat1Fixpoint` reaches a least fixpoint, and
  the LFP characterization (`iterate_le_of_fixpoint_above`) makes the result
  insensitive to the order of rules in the list.
- **Cat2**: requires `List.Sublist` rather than set inclusion. NAF rule
  application is order-dependent (concrete counterexamples exist where
  reordering produces incomparable states), so arbitrary set-extension is not
  monotone. The Sublist hypothesis is the natural notion of "rule set
  extension": new rules are inserted at any position while existing rules
  retain their relative order. This matches the practical case — rule sets
  are extended by adding rules, not by reordering.

## Proof

Direct application of `stratifiedFixpoint_extension` (proved in
`ArgonFormal.Reasoning.Fixpoint`) at `s = t = State.initial`. -/
theorem extension_monotone
    (rs₁ rs₂ : StratifiedRuleSet C A)
    (axisSorted : List A)
    (h_cat1 : ∀ a, ∀ r ∈ rs₁.cat1 a, r ∈ rs₂.cat1 a)
    (h_cat2 : ∀ a, (rs₁.cat2 a).Sublist (rs₂.cat2 a)) :
    stratifiedFixpoint rs₁ axisSorted State.initial ≤
    stratifiedFixpoint rs₂ axisSorted State.initial :=
  stratifiedFixpoint_extension rs₁ rs₂ axisSorted h_cat1 h_cat2
    State.initial State.initial (le_refl _)

/-- **Theorem 5.3: Consistent extensions resolve CAN to at most one of IS or NOT.**
If (c, a) = CAN in the original fixpoint, an extension can make it IS or NOT
but not both (since IS and NOT are incomparable). -/
theorem can_resolves_uniquely
    (c : C) (a : A)
    (s_orig : State C A)
    (h_can : s_orig c a = .can)
    -- Two consistent extensions that both refine s_orig
    (s_ext1 s_ext2 : State C A)
    (h_ext1 : s_orig ≤ s_ext1)
    (h_ext2 : s_orig ≤ s_ext2) :
    -- If ext1 says IS and ext2 says NOT, they're incompatible (no common refinement)
    s_ext1 c a = .is → s_ext2 c a = .not →
    ¬∃ s_merged : State C A, s_ext1 ≤ s_merged ∧ s_ext2 ≤ s_merged := by
  intro h_is h_not ⟨s_merged, h_m1, h_m2⟩
  -- s_merged must have (c, a) ≥ IS (from ext1) and ≥ NOT (from ext2)
  have h1 := h_m1 c a
  have h2 := h_m2 c a
  rw [h_is] at h1
  rw [h_not] at h2
  -- IS ≤ s_merged c a means s_merged c a = IS (IS is maximal in its branch)
  cases h1 with
  | inl h => exact MetaValue.noConfusion h  -- IS ≠ CAN
  | inr h =>
    -- h : MetaValue.is = s_merged c a, so s_merged c a = IS
    cases h2 with
    | inl h' => exact MetaValue.noConfusion h'  -- NOT ≠ CAN
    | inr h' =>
      -- h : IS = s_merged c a, h' : NOT = s_merged c a — contradiction
      rw [← h] at h'
      exact MetaValue.noConfusion h'
