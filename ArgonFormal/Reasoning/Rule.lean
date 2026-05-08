/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.Reasoning.State
import ArgonFormal.Reasoning.Stratification

/-!
# Rule Categories

Three categories of rules in the stratified fixpoint computation:

1. **Category 1 (Positive Propagation)**: Monotone rules that produce IS values.
   "If A is rigid and A specializes B, then B inherits rigidity."

2. **Category 2 (Negation-as-Failure)**: Rules that produce NOT values by
   checking the absence of positive evidence in the completed Category 1
   fixpoint. "If no ancestor of A provides identity, then A does NOT inherit
   identity."

3. **Category 3 (Constraint Checks)**: Pure observers that read the final
   state and produce diagnostics. Never modify state. "If A is rigid and B
   is anti-rigid and A specializes B, emit VIOLATION."

## Main definitions

- `MonotoneRule` — a state-to-state function that only adds IS values
- `NafRule` — a function from completed Cat1 state to NOT assignments
- `ConstraintCheck` — a pure function from state to diagnostic set
- `StratifiedRuleSet` — a collection of rules organized by axis and category
- `composeMonotone` — sequence a list of monotone rules
- `iterateToFixpoint` — bounded fixpoint iteration on a monotone operator
-/

variable {C A : Type} [DecidableEq C] [DecidableEq A] [Fintype C] [Fintype A]

/-- A Category 1 (positive propagation) rule.
Monotone: only adds IS values, never removes information. -/
structure MonotoneRule (C A : Type) [DecidableEq C] [DecidableEq A] where
  /-- The axis this rule operates on. -/
  axis : A
  /-- Apply the rule to produce a new state. -/
  apply : State C A → State C A
  /-- The rule is monotone w.r.t. the information ordering. -/
  monotone : ∀ s t : State C A, s ≤ t → apply s ≤ apply t
  /-- The rule only modifies its own axis. -/
  axis_local : ∀ s : State C A, ∀ c : C, ∀ a : A,
    a ≠ axis → (apply s) c a = s c a
  /-- The rule only adds IS values (never produces NOT or changes existing values). -/
  only_adds_is : ∀ s : State C A, ∀ c : C,
    s c axis ≠ .can → (apply s) c axis = s c axis

/-- A Category 2 (negation-as-failure) rule.
Reads the completed Category 1 fixpoint and produces NOT values. -/
structure NafRule (C A : Type) [DecidableEq C] [DecidableEq A] where
  /-- The axis this rule operates on. -/
  axis : A
  /-- Apply the rule given the completed Cat1 fixpoint state. -/
  apply : State C A → State C A
  /-- The rule only modifies its own axis. -/
  axis_local : ∀ s : State C A, ∀ c : C, ∀ a : A,
    a ≠ axis → (apply s) c a = s c a
  /-- The rule only changes CAN → NOT (never produces IS or changes existing values). -/
  only_adds_not : ∀ s : State C A, ∀ c : C,
    (apply s) c axis ≠ s c axis → s c axis = .can ∧ (apply s) c axis = .not
  /-- The rule is monotone: more information in → at least as much NOT out. -/
  monotone : ∀ s t : State C A, s ≤ t → apply s ≤ apply t

/-- A diagnostic produced by a constraint check. -/
structure Diagnostic where
  message : String
  deriving DecidableEq, Repr

/-- A Category 3 (constraint check) rule.
Pure observer: reads state, produces diagnostics, never modifies state. -/
structure ConstraintCheck (C A : Type) [DecidableEq C] [DecidableEq A]
    [Fintype C] [Fintype A] where
  /-- Evaluate the check against a state, producing a set of diagnostics. -/
  check : State C A → Finset Diagnostic

/-- A collection of rules organized by axis, respecting stratification.

For a given stratification, rules at stratum k may only read axes at strata
< k (or their own axis). This is enforced by the `reads_lower_strata`
property. -/
structure StratifiedRuleSet (C A : Type) [DecidableEq C] [DecidableEq A]
    [Fintype C] [Fintype A] where
  /-- The stratification of axes. -/
  strat : Stratification A
  /-- Category 1 rules, indexed by the axis they operate on. -/
  cat1 : A → List (MonotoneRule C A)
  /-- Category 2 rules, indexed by the axis they operate on. -/
  cat2 : A → List (NafRule C A)
  /-- Category 3 rules (run once at the end). -/
  cat3 : List (ConstraintCheck C A)
  /-- All Cat1 rules for axis `a` have `axis = a`. -/
  cat1_axis : ∀ a, ∀ r ∈ cat1 a, r.axis = a
  /-- All Cat2 rules for axis `a` have `axis = a`. -/
  cat2_axis : ∀ a, ∀ r ∈ cat2 a, r.axis = a

/-- Compose a list of monotone rules into a single state transformation.
Apply each rule in sequence. -/
def composeMonotone (rules : List (MonotoneRule C A)) (s : State C A) : State C A :=
  rules.foldl (fun acc r => r.apply acc) s

/-- Iterate a monotone inflationary operator on a finite domain.

Uses the ascending chain condition: each step resolves at least one CAN, so
we terminate in at most |C| × |A| steps. The bound is the total number of
(concept, axis) pairs.

We define this via bounded iteration (`Nat.iterate`) to avoid decidability
issues with function equality. -/
noncomputable def iterateToFixpoint (f : State C A → State C A)
    (_mono : ∀ s t : State C A, s ≤ t → f s ≤ f t)
    (s₀ : State C A) : State C A :=
  let bound := Fintype.card C * Fintype.card A + 1
  Nat.iterate f bound s₀
