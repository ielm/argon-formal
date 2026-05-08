/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.Foundation.LatticeContext

/-!
# Per-Standpoint Consistency Policy Soundness

Each standpoint in Argon declares a *consistency policy* that controls how
within-standpoint inconsistencies are handled at append time:

- **`strict`** (default): a write that would create an inconsistent pair `(T, F)`
  for the same fact at the same valid-time is **rejected**. The standpoint
  remains internally consistent — every cell stays in the K3 fragment.
  Sharpe's standard mode: legal/tax/financial sources cannot append conflicting
  facts under the same standpoint; conflicts must arise across standpoints.

- **`paraconsistent`**: all writes are accepted. Inconsistencies persist as
  `both`-valued cells; queries surface them via the FDE projection. Useful
  for systems that explicitly model multi-source-within-one-standpoint
  scenarios (e.g., a global KG mirror with no source-priority resolution).

This file abstracts a single fact-cell as a `Truth4` value, models append as
information-join, and proves the two soundness theorems:

1. **Strict soundness:** if a write succeeds under the strict policy, the
   resulting state is in the K3 fragment.
2. **Paraconsistent soundness:** all writes succeed; the result correctly
   summarizes the appended evidence in FDE.

Cross-standpoint disagreement is **always** preserved regardless of policy
because it manifests at federation join time, not at within-standpoint append
time. See `Federation.lean` for that side.
-/

namespace Truth4

/-! ## Consistency policy -/

/-- A policy controlling within-standpoint append-time consistency. -/
inductive ConsistencyPolicy where
  /-- Reject writes that would create an inconsistent pair within the standpoint.
  Default for production systems. -/
  | strict : ConsistencyPolicy
  /-- Accept all writes; inconsistencies persist as `both`. -/
  | paraconsistent : ConsistencyPolicy
  deriving DecidableEq, Repr

/-! ## Append operation -/

/-- Append `newEvidence` to a cell holding `current` under the given policy.
Returns `none` if the policy rejects the append. -/
def append (policy : ConsistencyPolicy) (current : Truth4) (newEvidence : Truth4) :
    Option Truth4 :=
  let result := infoJoin current newEvidence
  match policy with
  | .strict =>
    if result.inK3 then some result else none
  | .paraconsistent =>
    some result

/-! ## Strict soundness -/

/-- **Strict soundness.** If a strict-policy append succeeds, the resulting
state is in the K3 fragment. -/
theorem append_strict_inK3 (current newEvidence : Truth4) (result : Truth4)
    (h_succ : append .strict current newEvidence = some result) :
    result.inK3 := by
  unfold append at h_succ
  simp only at h_succ
  by_cases h_inK3 : (infoJoin current newEvidence).inK3
  · rw [if_pos h_inK3] at h_succ
    have h_eq : infoJoin current newEvidence = result := Option.some.inj h_succ
    rw [← h_eq]; exact h_inK3
  · rw [if_neg h_inK3] at h_succ
    exact absurd h_succ (by simp)

/-- **Strict rejection iff conflict.** A strict-policy append fails *exactly*
when the joined value would be `both`. -/
theorem append_strict_fails_iff (current newEvidence : Truth4) :
    append .strict current newEvidence = none ↔ infoJoin current newEvidence = .both := by
  unfold append
  simp only
  by_cases h_inK3 : (infoJoin current newEvidence).inK3
  · rw [if_pos h_inK3]
    constructor
    · intro h; exact absurd h (by simp)
    · intro h_both
      rw [h_both] at h_inK3
      simp [inK3, isConsistent] at h_inK3
  · rw [if_neg h_inK3]
    constructor
    · intro _
      -- ¬ inK3 means the value is `both` (the only inconsistent value).
      cases h : infoJoin current newEvidence
      all_goals simp_all [inK3, isConsistent]
    · intro _; rfl

/-- Strict append succeeds when the join is K3-consistent. -/
theorem append_strict_inK3_succeeds (current newEvidence : Truth4)
    (h_inK3 : (infoJoin current newEvidence).inK3) :
    append .strict current newEvidence = some (infoJoin current newEvidence) := by
  unfold append
  simp only
  rw [if_pos h_inK3]

/-! ## Paraconsistent soundness -/

/-- **Paraconsistent totality.** Paraconsistent appends always succeed. -/
theorem append_paraconsistent_total (current newEvidence : Truth4) :
    append .paraconsistent current newEvidence = some (infoJoin current newEvidence) := rfl

/-- **Paraconsistent both-iff-disagreement.** A paraconsistent append produces
a `both` cell *exactly* when the existing or new evidence is `both`, or when
they directly disagree (one `is`, the other `not`). -/
theorem append_paraconsistent_eq_both_iff (current newEvidence : Truth4) :
    append .paraconsistent current newEvidence = some .both ↔
    current = .both ∨ newEvidence = .both ∨
    (current = .is ∧ newEvidence = .not) ∨ (current = .not ∧ newEvidence = .is) := by
  unfold append
  simp only [Option.some.injEq]
  cases current <;> cases newEvidence <;> simp [infoJoin]

/-! ## Bridging strict ↔ paraconsistent -/

/-- The two policies agree on K3-preserving evidence. They diverge only when
the join produces `both`. -/
theorem append_strict_paraconsistent_agree
    (current newEvidence result : Truth4)
    (h_para : append .paraconsistent current newEvidence = some result)
    (h_inK3 : result.inK3) :
    append .strict current newEvidence = some result := by
  rw [append_paraconsistent_total] at h_para
  have h_eq : infoJoin current newEvidence = result := Option.some.inj h_para
  rw [← h_eq] at h_inK3
  rw [← h_eq]
  exact append_strict_inK3_succeeds current newEvidence h_inK3

/-! ## Multi-source append: folding evidence into a single cell

We model a sequence of evidence appends as a `foldl` of `append .strict` (or
`.paraconsistent`) over the option monad. The headline theorem: a successful
strict-fold result is always in K3. -/

/-- A strict-fold step: stay `none` if previously rejected; otherwise try to
append the next evidence. -/
def strictStep (acc : Option Truth4) (e : Truth4) : Option Truth4 :=
  match acc with
  | none => none
  | some a => append .strict a e

/-- A `none` accumulator stays `none` through the strict-fold: rejection is
absorbing. -/
theorem strictStep_none_absorbing (es : List Truth4) :
    es.foldl strictStep none = none := by
  induction es with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- **Strict-fold preserves K3.** If we run a strict-fold starting from a K3
value, every step's accumulator stays in K3 (whenever it stays `some`). -/
theorem strictFold_preserves_inK3 (es : List Truth4) (start : Truth4) (result : Truth4)
    (h_start : start.inK3)
    (h_succ : es.foldl strictStep (some start) = some result) :
    result.inK3 := by
  induction es generalizing start with
  | nil =>
    simp only [List.foldl_nil] at h_succ
    have h_eq : start = result := Option.some.inj h_succ
    rw [← h_eq]; exact h_start
  | cons e es ih =>
    simp only [List.foldl_cons, strictStep] at h_succ
    cases h_step : append .strict start e with
    | none =>
      rw [h_step] at h_succ
      rw [strictStep_none_absorbing] at h_succ
      exact absurd h_succ (by simp)
    | some new =>
      rw [h_step] at h_succ
      have h_new_inK3 : new.inK3 := append_strict_inK3 _ _ _ h_step
      exact ih new h_new_inK3 h_succ

/-- **Strict-fold initial-K3 corollary.** Starting from `.can` (which is in K3),
any successful strict-fold result is in K3. This is the standpoint-level
invariant: a strict standpoint never accumulates a `both`-valued cell. -/
theorem strictFold_from_can_inK3 (es : List Truth4) (result : Truth4)
    (h_succ : es.foldl strictStep (some .can) = some result) :
    result.inK3 :=
  strictFold_preserves_inK3 es .can result (by simp [inK3, isConsistent]) h_succ

end Truth4
