/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.TypeSystem.NarrowEnv

/-!
# Defeasibility and Narrowing Scope Boundaries

Defeasible rules (`@default`/`@override`) and lifecycle phase transitions can
create non-monotone state changes that BREAK narrowing soundness. This file:

1. Constructs a counterexample showing defeasible narrowing is unsound in general
2. Proves the restricted result: narrowing based on non-defeasible (strict) rules is sound
3. Documents lifecycle transitions as scope boundaries

## Design Implications for Argon

The compiler should either:
- (a) Restrict narrowing to non-defeasible determinations
- (b) Re-check narrowings after the defeasible fixpoint completes
- (c) Mark defeasible narrowings as provisional (like TypeScript's type assertions)

Option (a) is simplest and captures the common case. Options (b) and (c) are
more permissive but add complexity.
-/

variable {C A : Type} [DecidableEq C] [DecidableEq A] [Fintype C] [Fintype A]

/-! ## Override Model -/

/-- Apply a defeasible override: unconditionally set (c, a) to `v`.

Unlike `State.refine` (which only modifies CAN positions), overrides can
change IS→NOT or NOT→IS. This models `@override` rules in Argon's
defeasible reasoning. -/
def applyOverride (s : State C A) (c : C) (a : A) (v : MetaValue) : State C A :=
  fun c' a' => if c' = c ∧ a' = a then v else s c' a'

/-! ## Counterexample: Override Breaks Narrowing -/

/-- **Counterexample.** Overrides can invalidate narrowings.

Scenario: A narrowing established when `state(c, a) = IS` is invalidated by
an override that changes the position to NOT. This demonstrates that defeasible
reasoning (where `@override` rules can flip determinations) is fundamentally
incompatible with unrestricted narrowing.

We use `Unit` for both concept and axis types — a single-position state
suffices for the counterexample. -/
theorem override_breaks_narrowing :
    ∃ (s : State Unit Unit) (env : NarrowEnv Unit Unit),
      env.satisfiedBy s ∧
      ¬ env.satisfiedBy (applyOverride s () () .not) := by
  -- State: the single position has value IS
  refine ⟨fun _ _ => .is, ⟨[NarrowPred.isIs () ()]⟩, ?_, ?_⟩
  · -- env is satisfied: isIs holds because state is IS
    intro p hp; simp at hp; subst hp; rfl
  · -- After override to NOT, env is NOT satisfied
    intro h
    simp [NarrowEnv.satisfiedBy, NarrowPred.holds, applyOverride] at h

/-! ## Phase Transitions as Scope Boundaries -/

/-- **Phase transition counterexample.** Lifecycle transitions create states
that are incomparable in the information ordering.

When a contract transitions from Pending to Active, the state changes from
`(phase_pending = IS)` to `(phase_pending = NOT, phase_active = IS)`.
This is NOT monotone — IS→NOT is a decrease on that axis.

We model this with two axes (representing two phase flags). -/
theorem phase_transition_breaks_narrowing :
    ∃ (s_before s_after : State Unit Bool) (env : NarrowEnv Unit Bool),
      env.satisfiedBy s_before ∧
      ¬ env.satisfiedBy s_after ∧
      ¬ (s_before ≤ s_after) := by
  -- Before: phase_pending (true) = IS, phase_active (false) = CAN
  let s_before : State Unit Bool := fun _ a => if a then .is else .can
  -- After: phase_pending (true) = NOT, phase_active (false) = IS
  let s_after : State Unit Bool := fun _ a => if a then .not else .is
  refine ⟨s_before, s_after, ⟨[NarrowPred.isIs () true]⟩, ?_, ?_, ?_⟩
  · -- env satisfied before: isIs((), true) holds because s_before () true = .is
    intro p hp; simp at hp; subst hp
    show s_before () true = .is
    simp [s_before]
  · -- env NOT satisfied after: s_after () true = .not ≠ .is
    intro h
    simp [NarrowEnv.satisfiedBy, NarrowPred.holds, s_after] at h
  · -- States are incomparable: s_before () true = .is but s_after () true = .not
    intro hle
    have h := hle () true
    simp [s_before, s_after] at h
    exact MetaValue.is_not_le_not h

/-! ## Restricted Soundness: Non-Defeasible Narrowing -/

omit [Fintype C] [Fintype A] in
/-- **Restricted soundness.** Narrowing based on a state that is below
the final state (non-defeasible lower bound) is sound.

If `s_strict` is the fixpoint of only non-defeasible rules, and `s_full`
is the fixpoint of all rules (including defeasible), then `s_strict ≤ s_full`
(non-defeasible conclusions are a subset). Narrowings established at `s_strict`
hold at `s_full`.

This is the formal justification for option (a): restrict narrowing to
non-defeasible determinations. The strict fixpoint provides a sound lower
bound that defeasible overrides cannot invalidate. -/
theorem strict_narrowing_sound
    (s_strict s_full : State C A)
    (hle : s_strict ≤ s_full)
    (env : NarrowEnv C A)
    (h : env.satisfiedBy s_strict) :
    env.satisfiedBy s_full :=
  env.satisfiedBy_mono hle h

/-!
## Summary of Scope Boundaries

Narrowing scope must end at:

1. **Defeasible override points:** When `@override` rules fire, they can flip
   IS↔NOT. The compiler must discard narrowings based on the overridden value.

2. **Lifecycle phase transitions:** When an entity changes phase (Pending → Active),
   phase-dependent narrowings from the old phase are invalidated. The compiler
   starts a fresh narrowing scope after the transition.

3. **Cross-fixpoint boundaries:** If the fixpoint is recomputed (e.g., after
   adding new rules from a late-bound package), narrowings from the old fixpoint
   may not hold in the new one.

Within each scope (between boundaries), the computation is inflationary and
narrowing is sound by `NarrowPred.holds_mono`.
-/
