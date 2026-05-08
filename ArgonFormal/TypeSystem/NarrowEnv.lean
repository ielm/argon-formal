/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.TypeSystem.NarrowPred

/-!
# Narrowing Environments

A narrowing environment collects predicates known to hold at a program point.
The key property is monotonicity: if an environment is satisfied at state `s`
and `s ≤ t`, the environment is satisfied at `t`.
-/

/-- A narrowing environment: predicates known to hold at the current program point.

In Argon's occurrence typing, after checking `x.field is not unknown` in an
if-branch, the environment extends with `isDetermined(x, field)` for all
subsequent uses within that branch. -/
structure NarrowEnv (C A : Type) where
  preds : List (NarrowPred C A)

namespace NarrowEnv

variable {C A : Type} [DecidableEq C] [DecidableEq A] [Fintype C] [Fintype A]

/-- The empty environment: no predicates known. -/
def empty : NarrowEnv C A := ⟨[]⟩

/-- An environment is satisfied by a state if all its predicates hold. -/
def satisfiedBy (env : NarrowEnv C A) (s : State C A) : Prop :=
  ∀ p ∈ env.preds, p.holds s

/-- Extend an environment with an additional predicate. -/
def extend (env : NarrowEnv C A) (p : NarrowPred C A) : NarrowEnv C A :=
  ⟨p :: env.preds⟩

omit [Fintype C] [Fintype A] in
/-- The empty environment is satisfied by any state. -/
theorem empty_satisfiedBy (s : State C A) : (empty : NarrowEnv C A).satisfiedBy s := by
  intro p hp
  simp [empty] at hp

omit [Fintype C] [Fintype A] in
/-- **Monotonicity of environment satisfaction.**
If `env` is satisfied at `s` and `s ≤ t`, then `env` is satisfied at `t`.

This lifts `NarrowPred.holds_mono` from individual predicates to environments. -/
theorem satisfiedBy_mono (env : NarrowEnv C A) {s t : State C A}
    (hle : s ≤ t) (h : env.satisfiedBy s) : env.satisfiedBy t := by
  intro p hp
  exact NarrowPred.holds_mono p hle (h p hp)

omit [Fintype C] [Fintype A] in
/-- Extending with a predicate that holds preserves satisfaction. -/
theorem extend_satisfiedBy (env : NarrowEnv C A) (p : NarrowPred C A) (s : State C A)
    (henv : env.satisfiedBy s) (hp : p.holds s) :
    (env.extend p).satisfiedBy s := by
  intro q hq
  simp only [extend, List.mem_cons] at hq
  rcases hq with rfl | hmem
  · exact hp
  · exact henv q hmem

end NarrowEnv
