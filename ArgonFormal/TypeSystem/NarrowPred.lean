/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.Foundation.MetaValue
import ArgonFormal.Reasoning.State
import ArgonFormal.Reasoning.Stratification

/-!
# Narrowing Predicates for Occurrence Typing

Defines the predicates used in Argon's flow typing (occurrence typing) and
proves they are upward-closed in the information ordering on states.

## Key Result

`NarrowPred.holds_mono`: Every narrowing predicate is upward-closed. If a predicate
holds at state `s` and `s ≤ t` (more information), the predicate holds at `t`.

This is the foundation of flow typing soundness: once a narrowing predicate is
established, it cannot be invalidated by gaining more information.
-/

/-!
## Helper: Determined values are maximal

`MetaValue.determined_le_eq` lives in `ArgonFormal.Foundation.MetaValue`
(the K3 substrate); imported transitively here.
-/

/-! ## Narrowing Predicates -/

/-- A narrowing predicate: a proposition about a specific (concept, axis) position
in the meta-property state. These correspond to guards in Argon:
`x.field is not unknown`, `classify(x) is determined`, etc.

Only determined-value predicates are included. CAN-based predicates are
downward-closed (not upward-closed) and are never generated as positive
narrowings in Argon's occurrence typing. -/
inductive NarrowPred (C A : Type) where
  /-- The position has value IS (determined present).
  Corresponds to: `classify(x) is IS` or a field known to be present. -/
  | isIs (c : C) (a : A) : NarrowPred C A
  /-- The position has value NOT (determined absent).
  Corresponds to: `classify(x) is NOT` or a field known to be absent. -/
  | isNot (c : C) (a : A) : NarrowPred C A
  /-- The position is determined (IS or NOT, not CAN).
  Corresponds to: `x.field is not unknown` or `classify(x) is not ambiguous`. -/
  | isDetermined (c : C) (a : A) : NarrowPred C A

namespace NarrowPred

variable {C A : Type} [DecidableEq C] [DecidableEq A] [Fintype C] [Fintype A]

/-- Semantics: whether a narrowing predicate holds in a given state. -/
def holds : NarrowPred C A → State C A → Prop
  | isIs c a, s => s c a = .is
  | isNot c a, s => s c a = .not
  | isDetermined c a, s => s c a ≠ .can

omit [Fintype C] [Fintype A] in
/-- **Core lemma:** All narrowing predicates are upward-closed in the information ordering.
If `p` holds at state `s` and `s ≤ t`, then `p` holds at `t`.

Proof: Each predicate asserts a determined value (IS, NOT, or "not CAN") at a position.
Determined values are maximal in the `MetaValue` ordering — they cannot increase further.
Since `s ≤ t` means each position is ≤ pointwise, a determined position in `s` must have
the same value in `t`. -/
theorem holds_mono (p : NarrowPred C A) {s t : State C A}
    (hle : s ≤ t) (h : p.holds s) : p.holds t := by
  cases p with
  | isIs c a =>
    show t c a = .is
    have heq := MetaValue.determined_le_eq (by rw [h]; decide) (hle c a)
    rw [← heq]; exact h
  | isNot c a =>
    show t c a = .not
    have heq := MetaValue.determined_le_eq (by rw [h]; decide) (hle c a)
    rw [← heq]; exact h
  | isDetermined c a =>
    show t c a ≠ .can
    have heq := MetaValue.determined_le_eq h (hle c a)
    rw [← heq]; exact h

end NarrowPred
