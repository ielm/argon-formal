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

/-! ## numCan comparison under the information ordering

`numCan` measures how much "still-undetermined" content a state carries.
Information increase decreases `numCan`; *strict* increase decreases it
strictly. These two facts power the ascending-chain-condition argument
that drives `monotone_inflationary_fixpoint_finite` in
`ArgonFormal.Reasoning.Fixpoint`. -/

/-- Information increase shrinks the CAN-set: every CAN cell of `t` is also
a CAN cell of `s` whenever `s ≤ t`. -/
private theorem canSet_subset_of_le {s t : State C A} (hle : s ≤ t) :
    (Finset.univ (α := C × A)).filter (fun p => t p.1 p.2 = .can) ⊆
    (Finset.univ (α := C × A)).filter (fun p => s p.1 p.2 = .can) := by
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  -- hp : t p.1 p.2 = .can; need: s p.1 p.2 = .can
  -- From hle: s p.1 p.2 ≤ t p.1 p.2 = .can; partial order forces equality.
  have h := hle p.1 p.2
  rw [hp] at h
  rcases h with h | h
  · exact h
  · exact h

/-- Information increase doesn't increase `numCan`. -/
theorem numCan_le_of_le {s t : State C A} (hle : s ≤ t) : numCan t ≤ numCan s := by
  unfold numCan
  exact Finset.card_le_card (canSet_subset_of_le hle)

/-- *Strict* information increase strictly decreases `numCan`.

The crux of the ascending-chain-condition argument: from `s ≤ t` plus
`s ≠ t`, the partial-order definition forces some cell `(c, a)` with
`s c a = .can` and `t c a ≠ .can`. That cell is in `s`'s CAN-set but not
in `t`'s, witnessing the strict subset. -/
theorem numCan_lt_of_lt_ne {s t : State C A} (hle : s ≤ t) (hne : s ≠ t) :
    numCan t < numCan s := by
  unfold numCan
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (canSet_subset_of_le hle)]
  -- Goal: ∃ p ∈ filter on s, p ∉ filter on t
  -- From s ≠ t, ∃ c a, s c a ≠ t c a; combined with s ≤ t, forces s c a = .can.
  have h_diff : ∃ c a, s c a ≠ t c a := by
    by_contra hall
    push_neg at hall
    apply hne
    funext c a
    exact hall c a
  obtain ⟨c, a, hca⟩ := h_diff
  refine ⟨(c, a), ?_, ?_⟩
  · -- (c, a) ∈ filter on s (i.e., s c a = .can)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h_le_ca := hle c a
    rcases h_le_ca with h_can | h_eq
    · exact h_can
    · exact absurd h_eq hca
  · -- (c, a) ∉ filter on t (i.e., t c a ≠ .can)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro h_t_can
    -- If t c a = .can, then since s c a ≤ t c a = .can, s c a = .can too,
    -- contradicting hca (s c a ≠ t c a) since both would equal .can.
    apply hca
    have h_le_ca := hle c a
    rw [h_t_can] at h_le_ca
    rcases h_le_ca with h_s_can | h_s_eq
    · rw [h_s_can, h_t_can]
    · rw [h_s_eq, h_t_can]

end State
