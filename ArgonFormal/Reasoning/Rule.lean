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

variable {C A : Type} [DecidableEq C] [DecidableEq A] in
/-- The frame property for a rule's `apply` function: the value written on
the rule's own `axis` at concept `c` depends only on (1) cells at axes in
`read_axes` (the trigger axes — strictly lower strata) and (2) the
input value at the same cell `(c, axis)`.

This is the natural read-locality condition for stratified Datalog
rules:
- `read_axes` excludes the rule's own `axis`. Cross-axis trigger reads
  are confined to strictly-lower strata.
- The own-axis dependency is per-cell: the rule's write at `(c, axis)`
  depends on the input value at `(c, axis)` (so `only_adds_is` /
  `only_adds_not` can fire conditionally on `.can`), but doesn't depend
  on axis-`axis` values at *other* concepts `c'`.

Combined with `axis_local` (the rule writes nothing outside `axis`) and
`only_adds_is` / `only_adds_not` (CAN-only writes), this captures the
full read/write boundary: outputs are read-determined on `axis` and
input-passing-through everywhere else. The strict form supports the
post-cat2 / post-suffix preservation arguments needed for
`stratified_fixpoint_stable`. -/
def FrameLocal (read_axes : Finset A) (axis : A) (apply : State C A → State C A) : Prop :=
  ∀ s t : State C A,
    (∀ c : C, ∀ b : A, b ∈ read_axes → s c b = t c b) →
    ∀ c : C, s c axis = t c axis →
    (apply s) c axis = (apply t) c axis

/-- A Category 1 (positive propagation) rule.
Monotone: only adds IS values, never removes information.

A rule has both a write-locality property (`axis_local`: only modifies its
own `axis`) and a read-locality property (`frame_local`: depends only on
cells in `read_axes`). Together these capture the read/write boundary that
exists structurally at the Argon source level (a rule's trigger pattern
names its read-set; its conclusion atom names its write-target). -/
structure MonotoneRule (C A : Type) [DecidableEq C] [DecidableEq A] where
  /-- The axis this rule operates on (writes to). -/
  axis : A
  /-- The axes this rule may read from. Includes `axis` (rules read existing
  values on their own axis to decide whether to fire). -/
  read_axes : Finset A
  /-- Apply the rule to produce a new state. -/
  apply : State C A → State C A
  /-- The rule is monotone w.r.t. the information ordering. -/
  monotone : ∀ s t : State C A, s ≤ t → apply s ≤ apply t
  /-- The rule only modifies its own axis (write-locality). -/
  axis_local : ∀ s : State C A, ∀ c : C, ∀ a : A,
    a ≠ axis → (apply s) c a = s c a
  /-- The rule only adds IS values (never produces NOT or changes existing values). -/
  only_adds_is : ∀ s : State C A, ∀ c : C,
    s c axis ≠ .can → (apply s) c axis = s c axis
  /-- The rule's write on its own `axis` depends only on cells at axes
  in `read_axes` (read-locality). -/
  frame_local : FrameLocal read_axes axis apply

/-- A Category 2 (negation-as-failure) rule.
Reads the completed Category 1 fixpoint and produces NOT values. -/
structure NafRule (C A : Type) [DecidableEq C] [DecidableEq A] where
  /-- The axis this rule operates on (writes to). -/
  axis : A
  /-- The axes this rule may read from. Includes `axis` (NAF reads its own
  axis to check for `.can` before flipping to `.not`). -/
  read_axes : Finset A
  /-- Apply the rule given the completed Cat1 fixpoint state. -/
  apply : State C A → State C A
  /-- The rule only modifies its own axis (write-locality). -/
  axis_local : ∀ s : State C A, ∀ c : C, ∀ a : A,
    a ≠ axis → (apply s) c a = s c a
  /-- The rule only changes CAN → NOT (never produces IS or changes existing values). -/
  only_adds_not : ∀ s : State C A, ∀ c : C,
    (apply s) c axis ≠ s c axis → s c axis = .can ∧ (apply s) c axis = .not
  /-- The rule is monotone: more information in → at least as much NOT out. -/
  monotone : ∀ s t : State C A, s ≤ t → apply s ≤ apply t
  /-- The rule's write on its own `axis` depends only on cells at axes
  in `read_axes` (read-locality). -/
  frame_local : FrameLocal read_axes axis apply

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

The stratification consistency invariants tie each rule's declared
`read_axes` (the trigger axes) to the stratification. **Strict
stratification** for both categories: a rule at axis `a` may read
trigger inputs only at axes strictly below `strat a`. Own-axis
inspection happens per-cell via `only_adds_is` / `only_adds_not` and
the per-cell `frame_local` formulation, not via `read_axes`.

This is the form of stratification required by per-axis processing:
- When `processStratum` runs axis `a` then axis `b` at the same stratum,
  the result must be invariant under swapping. Strict stratification
  makes `a`'s rules independent of `b`'s state and vice versa.
- For `stratified_fixpoint_stable`, cat1 rules at axis `a` must remain
  fixpoints even after later stages (cat2 at axis `a`, then later
  strata) modify the state. Strict stratification keeps the trigger
  inputs frozen across these stages.

For mutually-recursive same-stratum axes, the design move is either to
combine them into one super-axis with a joint fixpoint, or to put them
at distinct strata. Argon's compiler enforces this at stratification
time.

These invariants are the structural conditions of stratified Datalog
(Apt-Blair-Walker 1988). -/
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
  /-- Cat1 rules at axis `a` have trigger reads strictly below `strat a`. -/
  cat1_strat_consistent : ∀ a, ∀ r ∈ cat1 a, ∀ b ∈ r.read_axes,
    strat.strat b < strat.strat a
  /-- Cat2 rules at axis `a` have trigger reads strictly below `strat a`. -/
  cat2_strat_consistent : ∀ a, ∀ r ∈ cat2 a, ∀ b ∈ r.read_axes,
    strat.strat b < strat.strat a

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

/-! ## Inflationarity of rules

Both `MonotoneRule` and `NafRule` are inflationary in the information
ordering: applying a rule never decreases the state. This follows from
the structural fields (`only_adds_is` / `only_adds_not`) plus the
partial-order definition's `.can`-as-bottom property. -/

/-- Every `MonotoneRule` is inflationary: `s ≤ r.apply s`. Determined cells
unchanged (by `only_adds_is`); CAN cells potentially become IS, which is
≥ in the information ordering (`.can` is bottom). -/
theorem MonotoneRule.inflationary (r : MonotoneRule C A) (s : State C A) :
    s ≤ r.apply s := by
  intro c a
  by_cases hax : a = r.axis
  · -- On the rule's own axis. Either CAN (becomes anything ≥ .can) or
    -- determined (unchanged by only_adds_is).
    by_cases hcan : s c a = .can
    · -- .can ≤ anything.
      rw [hcan]; exact MetaValue.can_le _
    · -- Determined; rule preserves.
      rw [hax] at hcan ⊢
      rw [r.only_adds_is s c hcan]
  · -- Off the rule's axis; rule preserves by axis_local.
    rw [r.axis_local s c a hax]

/-- Every `NafRule` is inflationary: `s ≤ r.apply s`. Same shape as
`MonotoneRule.inflationary` but uses `only_adds_not`: a NAF rule may
flip CAN → NOT, which is ≥ in the information ordering. -/
theorem NafRule.inflationary (r : NafRule C A) (s : State C A) :
    s ≤ r.apply s := by
  intro c a
  by_cases hax : a = r.axis
  · by_cases h_eq : (r.apply s) c a = s c a
    · -- Unchanged.
      rw [h_eq]
    · -- Changed; by only_adds_not, was CAN, now NOT.
      rw [hax] at h_eq
      have h_eq' : (r.apply s) c r.axis ≠ s c r.axis := h_eq
      obtain ⟨hcan, _⟩ := r.only_adds_not s c h_eq'
      rw [hax]
      rw [hcan]; exact MetaValue.can_le _
  · rw [r.axis_local s c a hax]

/-- `composeMonotone` is inflationary: folding over monotone rules from
state `s` produces a state ≥ `s`. -/
theorem composeMonotone_inflationary (rules : List (MonotoneRule C A))
    (s : State C A) : s ≤ composeMonotone rules s := by
  induction rules generalizing s with
  | nil => exact le_refl s
  | cons r rs ih =>
    -- composeMonotone (r :: rs) s = composeMonotone rs (r.apply s).
    -- s ≤ r.apply s (inflation) ≤ composeMonotone rs (r.apply s) (IH).
    simp only [composeMonotone, List.foldl]
    exact le_trans (r.inflationary s) (ih (r.apply s))

