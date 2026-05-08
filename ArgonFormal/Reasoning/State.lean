/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import ArgonFormal.Foundation.MetaValue

/-!
# Assignment State

The meta-property calculus's working state: a function from (concept, axis)
pairs to `MetaValue`. The state evolves through stratified fixpoint
computation; theorems about that evolution live in
`ArgonFormal.Reasoning.Fixpoint`.

## Main definitions

- `State C A` — the assignment type. `C → A → MetaValue` for finite `C`, `A`.
- `State.initial` — bottom element (everything `CAN`).
- `State.refine` — single-position update (only adds information).
- The pointwise information ordering on states (lifted from `MetaValue`).
-/

/-- Assignment state: maps each (concept, axis) pair to a `MetaValue`.
Concepts `C` and axes `A` are finite types with decidable equality. -/
def State (C A : Type) [DecidableEq C] [DecidableEq A] := C → A → MetaValue

namespace State

variable {C A : Type} [DecidableEq C] [DecidableEq A] [Fintype C] [Fintype A]

/-- The initial state: everything is CAN (indeterminate). -/
def initial : State C A := fun _ _ => .can

/-- Pointwise information ordering on states. -/
instance : PartialOrder (State C A) where
  le s t := ∀ c a, s c a ≤ t c a
  le_refl s c a := le_refl (s c a)
  le_trans s t u hst htu c a := le_trans (hst c a) (htu c a)
  le_antisymm s t hst hts := by
    funext c a
    exact le_antisymm (hst c a) (hts c a)

/-- The initial state is bottom. -/
theorem initial_le (s : State C A) : initial ≤ s :=
  fun _ _ => MetaValue.can_le _

/-- A state is more informative when it has fewer CAN values. -/
def numCan (s : State C A) : Nat :=
  (Finset.univ (α := C × A)).filter (fun p => s p.1 p.2 = .can) |>.card

/-- A state update: set (c, a) to v, if currently CAN. Only adds information. -/
def refine (s : State C A) (c : C) (a : A) (v : MetaValue) : State C A :=
  fun c' a' =>
    if c' = c ∧ a' = a then
      match s c a with
      | .can => v
      | other => other  -- don't overwrite determined values
    else
      s c' a'

/-- Refining a CAN position is an information increase. -/
theorem refine_le {s : State C A} {c : C} {a : A} {v : MetaValue}
    (_ : v ≠ .can) (hcan : s c a = .can) :
    s ≤ s.refine c a v := by
  intro c' a'
  simp only [refine]
  split
  · case _ heq =>
    obtain ⟨hc, ha⟩ := heq
    subst hc; subst ha
    rw [hcan]
    exact MetaValue.can_le v
  · case _ _ => exact le_refl _

end State
