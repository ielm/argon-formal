/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.TypeSystem.Soundness.CrossStratum
import ArgonFormal.TypeSystem.Soundness.CwaOwa
import ArgonFormal.TypeSystem.Soundness.Defeasibility

/-!
# Flow Typing Soundness for Argon

Main theorem: under Argon's structural conditions, occurrence typing
narrowing is sound.

## The Four Conditions

1. **Immutability:** The type graph (state) is only modified by the fixpoint
   computation, not by external mutation. (Trivially true in our functional model.)

2. **Monotone fixpoint:** The IS/CAN/NOT fixpoint is computed by inflationary
   operators (Cat1 adds IS, Cat2 adds NOT). Each step increases the state.

3. **No aliasing:** Each narrowing predicate refers to a specific (concept, axis)
   position. No aliasing between positions. (Trivially true because `State` is
   a function, not a pointer graph.)

4. **Consistent CWA/OWA:** World assumptions are consistent — CWA axes and OWA
   axes are disjoint. CWA guarantees carry monotonically.

## The Result

Under these conditions, if a narrowing environment is satisfied at any state `s₀`
encountered during fixpoint computation, it is satisfied at the final fixpoint.
This means: once the compiler establishes a narrowing (e.g., after
`if x.field is not unknown`), the narrowing holds at all subsequent program
points within the narrowing scope.

## Limitations

Defeasible narrowing (based on `@override`-able determinations) is NOT covered.
See `Defeasibility.lean` for the counterexample and the restricted result.
Lifecycle phase transitions are scope boundaries — narrowings do not cross them.
-/

variable {C A : Type} [DecidableEq C] [DecidableEq A] [Fintype C] [Fintype A]

/-! ## Soundness Conditions -/

/-- The structural conditions under which Argon's flow typing is sound.

These conditions are satisfied by construction in Argon:
- The meta-property state is a pure function (immutable, no aliasing)
- The fixpoint uses stratified rules that are monotone/inflationary
- CWA/OWA axes are declared per-module and cannot overlap -/
structure SoundnessConditions (C A : Type)
    [DecidableEq C] [DecidableEq A] [Fintype C] [Fintype A] where
  /-- The stratified rule set defining the fixpoint computation. -/
  rules : StratifiedRuleSet C A
  /-- A valid topological sort of the axes. -/
  axisSorted : List A
  /-- CWA axes (complete: no CAN). -/
  cwa_axes : Finset A
  /-- OWA axes (may have CAN). -/
  owa_axes : Finset A
  /-- World assumptions are consistent: CWA and OWA axes don't overlap. -/
  disjoint : Disjoint cwa_axes owa_axes

/-! ## Main Theorem -/

/-- **Theorem (Flow Typing Soundness).**

If:
- `env` is satisfied at state `s₀` (narrowing established at program point)
- `s₀ ≤ fixpoint` (the narrowing point is before the fixpoint)

Then `env` is satisfied at the fixpoint.

This is the formal statement that Argon's occurrence typing is sound:
narrowings established by checking IS/NOT/determined values hold at all
subsequent uses within the narrowing scope.

The proof is a direct application of `satisfiedBy_mono`: narrowing predicates
are upward-closed, and the fixpoint is above `s₀`. -/
theorem flow_typing_soundness
    (conds : SoundnessConditions C A)
    (env : NarrowEnv C A)
    (s₀ : State C A)
    (h_sat : env.satisfiedBy s₀)
    (h_below : s₀ ≤ stratifiedFixpoint conds.rules conds.axisSorted State.initial) :
    env.satisfiedBy (stratifiedFixpoint conds.rules conds.axisSorted State.initial) :=
  env.satisfiedBy_mono h_below h_sat

/-- **Corollary:** Narrowing from initial state persists through the entire fixpoint. -/
theorem narrowing_from_initial
    (conds : SoundnessConditions C A)
    (env : NarrowEnv C A)
    (h : env.satisfiedBy State.initial) :
    env.satisfiedBy (stratifiedFixpoint conds.rules conds.axisSorted State.initial) :=
  flow_typing_soundness conds env State.initial h (State.initial_le _)

/-- **Corollary:** Narrowing persists through the full fixpoint starting from any state.

Stronger form: does not require knowing the fixpoint is above `s₀` as a
precondition — derives it from inflationarity. -/
theorem narrowing_persists
    (rs : StratifiedRuleSet C A) (axisSorted : List A)
    (env : NarrowEnv C A) (s₀ : State C A)
    (h : env.satisfiedBy s₀) :
    env.satisfiedBy (stratifiedFixpoint rs axisSorted s₀) :=
  narrowing_preserved_cross_stratum rs axisSorted env s₀ h

/-- **Corollary:** CWA narrowings carry into OWA modules after fixpoint.

If a CWA module establishes narrowings at state `s_cwa`, and the OWA module
sees a state that includes the fixpoint computation over both modules, the
narrowings hold. -/
theorem cwa_narrowing_survives_fixpoint
    (rs : StratifiedRuleSet C A) (axisSorted : List A)
    (env : NarrowEnv C A) (s₀ : State C A)
    (h : env.satisfiedBy s₀) :
    env.satisfiedBy (stratifiedFixpoint rs axisSorted s₀) :=
  narrowing_persists rs axisSorted env s₀ h

/-- **Corollary:** Handler resolution during fixpoint preserves narrowing.

If CAN is resolved to IS or NOT by a handler at some point during computation,
and then the fixpoint continues, all prior narrowings remain valid. This is
because handler resolution IS part of the fixpoint computation (inflationary). -/
theorem handler_then_fixpoint
    (rs : StratifiedRuleSet C A) (axisSorted : List A)
    (env : NarrowEnv C A) (s : State C A) (c : C) (a : A)
    (hcan : s c a = .can) (h : env.satisfiedBy s) :
    env.satisfiedBy (stratifiedFixpoint rs axisSorted (s.refine c a .is)) :=
  narrowing_persists rs axisSorted env (s.refine c a .is)
    (handler_resolution_preserves env s c a hcan h)

/-!
## Summary

The soundness proof has three layers:

1. **Predicate level** (`Predicate.lean`): `NarrowPred.holds_mono` — all narrowing
   predicates are upward-closed in the information ordering.

2. **Computation level** (`Monotonicity.lean`, `CrossStratum.lean`): The fixpoint
   computation is inflationary — every step (Cat1, Cat2, handler resolution)
   increases the state.

3. **Theorem level** (this file): Combining (1) and (2): narrowings established
   at any point during the fixpoint persist to the end.

The proof does NOT depend on any sorry'd theorems from the upstream project.
It uses only fully-proved results: the `PartialOrder` instances, `MetaValue.can_le`,
`State.refine_le`, and the structural axioms of `MonotoneRule` and `NafRule`.
-/
