/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.Reasoning.Fixpoint

/-!
# Theorem 3: Constraint Check Well-Definedness

## Statement

Category 3 rules (constraint checks) reading the completed stratified fixpoint
produce a deterministic set of diagnostics, independent of:
- The order of axis processing within topological equivalence classes
- The order of rule application within a stratum
- The order of constraint check evaluation

## Proof

This follows directly from Theorem 1.2 (uniqueness of the fixpoint):
1. The input state is unique (Theorem 1.2)
2. Constraint checks are pure functions from state to diagnostic set
3. Pure functions of a unique input produce unique output
-/

variable {C A : Type} [DecidableEq C] [DecidableEq A] [Fintype C] [Fintype A]

/-- Evaluate all constraint checks against a state, collecting diagnostics. -/
def evaluateConstraints (checks : List (ConstraintCheck C A)) (s : State C A) : Finset Diagnostic :=
  checks.foldl (fun acc check => acc ∪ check.check s) ∅

/-- **Theorem 3: Constraint Check Well-Definedness.**

Given a stratified rule set, the set of diagnostics produced by evaluating all
Category 3 rules against the stratified fixpoint is deterministic — it does not
depend on the topological sort order used to compute the fixpoint. -/
theorem constraint_checks_deterministic (rs : StratifiedRuleSet C A)
    (sort1 sort2 : List A)
    (hvalid1 : IsTopoSort rs.strat sort1)
    (hvalid2 : IsTopoSort rs.strat sort2) :
    evaluateConstraints rs.cat3 (stratifiedFixpoint rs sort1 State.initial) =
    evaluateConstraints rs.cat3 (stratifiedFixpoint rs sort2 State.initial) := by
  -- The fixpoints are equal by Theorem 1.2
  have h := stratified_fixpoint_unique rs sort1 sort2 hvalid1 hvalid2
  rw [h]

/-- Constraint checks commute: evaluating in any order gives the same diagnostic set.

Each check produces an independent `Finset` of diagnostics, and `Finset.union`
is commutative and associative. The proof rides on `List.Perm.foldl_eq` —
provided a `RightCommutative` witness for our `acc ∪ c.check s` operation. -/
theorem constraint_checks_commute (checks : List (ConstraintCheck C A))
    (s : State C A) (perm : List (ConstraintCheck C A))
    (hperm : perm.Perm checks) :
    evaluateConstraints checks s = evaluateConstraints perm s := by
  -- The function `fun acc c => acc ∪ c.check s` is right-commutative because
  -- `(acc ∪ c₁.check s) ∪ c₂.check s = (acc ∪ c₂.check s) ∪ c₁.check s`
  -- by `Finset.union_right_comm`. Apply `Perm.foldl_eq'` with this hypothesis
  -- as an explicit argument; foldl is invariant under permutation of the
  -- list when the operator right-commutes.
  unfold evaluateConstraints
  refine List.Perm.foldl_eq'
    (f := fun acc (c : ConstraintCheck C A) => acc ∪ c.check s)
    hperm.symm ?_ ∅
  intro c₁ _ c₂ _ acc
  show (acc ∪ c₁.check s) ∪ c₂.check s = (acc ∪ c₂.check s) ∪ c₁.check s
  rw [Finset.union_right_comm]
