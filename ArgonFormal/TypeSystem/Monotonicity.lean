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

/-! ## Narrowing Preservation Through Cat1

Inflationarity lemmas for `MonotoneRule`, `composeMonotone`, and
`cat1Fixpoint` live in `ArgonFormal.Reasoning` (the layer where the
operations are defined); imported transitively here. -/

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
