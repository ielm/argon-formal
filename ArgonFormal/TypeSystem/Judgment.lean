/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.TypeSystem.NarrowEnv

/-!
# Narrowing Judgment

Connects program-level narrowing (checking predicates in if-branches) to
state-level satisfaction. This is intentionally minimal: it covers the
narrowing-relevant control flow without modeling Argon's full expression language.

The key insight: within a narrowing scope, the state is either unchanged
(immutability assumption) or increases monotonically (fixpoint computation).
In either case, `NarrowPred.holds_mono` guarantees that established
narrowings remain valid.
-/

variable {C A : Type} [DecidableEq C] [DecidableEq A] [Fintype C] [Fintype A]

/-! ## Narrowing Step Soundness -/

omit [Fintype C] [Fintype A] in
/-- **Narrowing step soundness.**
If the environment is satisfied by `s` and predicate `p` holds in `s`,
then extending the environment with `p` produces a satisfied environment.

This is the formal model of: "after checking `x.field is not unknown`,
the environment gains `isDetermined(x, field)` and all subsequent uses
within the scope see this refinement." -/
theorem narrow_step_sound (env : NarrowEnv C A) (p : NarrowPred C A) (s : State C A)
    (henv : env.satisfiedBy s) (hp : p.holds s) :
    (env.extend p).satisfiedBy s :=
  env.extend_satisfiedBy p s henv hp

/-! ## Scope Validity -/

omit [Fintype C] [Fintype A] in
/-- **Scope validity.**
If narrowing is established at state `s₀` and the state evolves to `s₁ ≥ s₀`
(via fixpoint computation), the narrowing remains valid at `s₁`.

This theorem captures the core safety property: within any scope where the
state only increases (monotonic fixpoint, handler resolution, etc.),
narrowings cannot be invalidated.

Combines with `narrow_step_sound`: first establish the narrowing, then
this theorem guarantees it persists through all subsequent state changes
within the scope. -/
theorem scope_valid (env : NarrowEnv C A) {s₀ s₁ : State C A}
    (hle : s₀ ≤ s₁) (h : env.satisfiedBy s₀) :
    env.satisfiedBy s₁ :=
  env.satisfiedBy_mono hle h

/-! ## Branch Semantics

At an if-else branch on predicate `p`:
- **True branch:** environment extends with `p` (by `narrow_step_sound`)
- **False branch:** environment extends with the negation of `p` (if expressible)
- **Merge point:** only predicates from the base environment (before the branch) survive

The base environment is always valid at the merge because it was valid before
the branch and the state didn't change (immutability within a scope).

This conservative merge (discarding branch-specific narrowings at the join point)
is sound by construction: the base environment's satisfaction is preserved by
`scope_valid`. A more precise analysis could keep predicates that hold in both
branches (intersection), but this is not needed for the core soundness result. -/
