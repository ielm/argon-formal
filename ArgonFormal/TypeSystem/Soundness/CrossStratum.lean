/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.TypeSystem.Monotonicity
import ArgonFormal.Reasoning.Fixpoint

/-!
# Cross-Stratum Preservation

Proves that Cat2 (negation-as-failure) rules and handler resolution preserve
narrowings established during Cat1 (positive propagation).

## Key Results

1. `NafRule.inflationary`: Every NafRule application is inflationary (CAN→NOT is ≥)
2. `cat2Apply_inflationary`: Folding NafRules is inflationary
3. `processStratum_inflationary`: Processing a full stratum is inflationary
4. `narrowing_preserved_cross_stratum`: Narrowings survive across strata
5. `handler_resolution_preserves`: CAN→IS resolution preserves narrowings

## Why Cross-Stratum Is Not a Separate Concern

The initial analysis suggested that "Cat2 invalidating Cat1 narrowings" might be
a distinct concern. It is not. Both Cat1 (CAN→IS) and Cat2 (CAN→NOT) are
inflationary — they only add information. Since all narrowing predicates are
upward-closed, inflationarity alone guarantees preservation.

The apparent concern dissolves because IS and NOT are incomparable in the
information ordering: Cat2 adding NOT values never touches IS values, and
vice versa. But we don't even need this fact — inflationarity is sufficient.
-/

variable {C A : Type} [DecidableEq C] [DecidableEq A] [Fintype C] [Fintype A]

/-! ## NafRule Inflationarity -/

omit [Fintype C] [Fintype A] in
/-- A `NafRule` application is inflationary: `s ≤ r.apply s`.

Cat2 rules only change CAN→NOT (by `only_adds_not`) and leave other
positions unchanged (by `axis_local`). CAN ≤ NOT in the information ordering,
so every change is an increase. -/
theorem NafRule.inflationary (r : NafRule C A) (s : State C A) :
    s ≤ r.apply s := by
  intro c' a'
  by_cases ha : a' = r.axis
  · subst ha
    by_cases heq : (r.apply s) c' r.axis = s c' r.axis
    · exact le_of_eq heq.symm
    · obtain ⟨hcan, _⟩ := r.only_adds_not s c' heq
      exact (le_of_eq hcan).trans (MetaValue.can_le _)
  · exact le_of_eq (r.axis_local s c' a' ha).symm

omit [Fintype C] [Fintype A] in
/-- `cat2Apply` is inflationary: `s ≤ cat2Apply rules s`. -/
theorem cat2Apply_inflationary (rules : List (NafRule C A)) (s : State C A) :
    s ≤ cat2Apply rules s := by
  exact foldl_inflationary (fun s r => NafRule.inflationary r s) rules s

/-! ## Full Stratum and Fixpoint Inflationarity -/

/-- Processing a single stratum is inflationary: `s ≤ processStratum rs a s`. -/
theorem processStratum_inflationary (rs : StratifiedRuleSet C A) (a : A) (s : State C A) :
    s ≤ processStratum rs a s := by
  unfold processStratum
  exact le_trans (cat1Fixpoint_inflationary (rs.cat1 a) s)
                 (cat2Apply_inflationary (rs.cat2 a) (cat1Fixpoint (rs.cat1 a) s))

/-- The full stratified fixpoint is inflationary: `s₀ ≤ stratifiedFixpoint rs axisSorted s₀`. -/
theorem stratifiedFixpoint_inflationary (rs : StratifiedRuleSet C A)
    (axisSorted : List A) (s₀ : State C A) :
    s₀ ≤ stratifiedFixpoint rs axisSorted s₀ := by
  exact foldl_inflationary (fun s a => processStratum_inflationary rs a s) axisSorted s₀

/-! ## Cross-Stratum Narrowing Preservation -/

omit [Fintype C] [Fintype A] in
/-- Narrowing is preserved through Cat2 application.
Established as a special case of inflationarity + upward-closure. -/
theorem narrowing_preserved_cat2 (rules : List (NafRule C A))
    (env : NarrowEnv C A) (s : State C A) (h : env.satisfiedBy s) :
    env.satisfiedBy (cat2Apply rules s) :=
  env.satisfiedBy_mono (cat2Apply_inflationary rules s) h

/-- Narrowing is preserved through a full stratum (Cat1 fixpoint + Cat2). -/
theorem narrowing_preserved_stratum (rs : StratifiedRuleSet C A) (a : A)
    (env : NarrowEnv C A) (s : State C A) (h : env.satisfiedBy s) :
    env.satisfiedBy (processStratum rs a s) :=
  env.satisfiedBy_mono (processStratum_inflationary rs a s) h

/-- Narrowing is preserved through the full stratified fixpoint computation.
If `env` is satisfied at `s₀`, it is satisfied at the fixpoint. -/
theorem narrowing_preserved_cross_stratum (rs : StratifiedRuleSet C A)
    (axisSorted : List A) (env : NarrowEnv C A) (s₀ : State C A)
    (h : env.satisfiedBy s₀) :
    env.satisfiedBy (stratifiedFixpoint rs axisSorted s₀) :=
  env.satisfiedBy_mono (stratifiedFixpoint_inflationary rs axisSorted s₀) h

/-! ## Handler Resolution -/

/-- CAN→IS handler resolution preserves narrowings.

When an algebraic effect handler resolves a CAN value to IS (e.g., a package
handler determines that a concept is rigid), this is an information increase.
All existing narrowings are preserved. -/
theorem handler_resolution_preserves (env : NarrowEnv C A) (s : State C A) (c : C) (a : A)
    (hcan : s c a = .can) (h : env.satisfiedBy s) :
    env.satisfiedBy (s.refine c a .is) :=
  env.satisfiedBy_mono (State.refine_le (by decide) hcan) h

/-- CAN→NOT handler resolution also preserves narrowings.
A handler that determines absence is equally safe. -/
theorem handler_resolution_not_preserves (env : NarrowEnv C A) (s : State C A) (c : C) (a : A)
    (hcan : s c a = .can) (h : env.satisfiedBy s) :
    env.satisfiedBy (s.refine c a .not) :=
  env.satisfiedBy_mono (State.refine_le (by decide) hcan) h
