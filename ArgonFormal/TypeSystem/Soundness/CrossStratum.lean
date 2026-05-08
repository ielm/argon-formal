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

/-! ## Cross-Stratum Narrowing Preservation

Inflationarity lemmas for `NafRule`, `cat2Apply`, `processStratum`, and
`stratifiedFixpoint` live in `ArgonFormal.Reasoning` (the layer where the
operations are defined); imported transitively here. -/

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
