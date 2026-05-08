/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Order.Defs.PartialOrder

/-!
# K3 — Kleene Strong Three-Valued Type

The three-valued type Argon uses for refinement membership and the meta-property
calculus's IS/CAN/NOT state. K3 is Kleene's strong three-valued logic
(Kleene 1952), realized as the consistent fragment of the four-valued FDE
bilattice (`ArgonFormal.Foundation.Truth4`) under the Pietz-Rivieccio
"Exactly True" designation. See [RFD-0036](../../../rfd/0036-aft-grounded-truth-value-semantics.md).

This file defines the `MetaValue` inductive type, the information ordering,
and the basic incomparability lemmas. The type is shared across every
`ArgonFormal.Reasoning`, `ArgonFormal.TypeSystem`, and `ArgonFormal.Standpoint`
file that consumes K3 values.

## Naming

`MetaValue` is the name the Argon compiler uses internally (the engine
vocabulary: `is`, `not`, `can` rather than the abstract `T`, `F`, `U` of
the K3 literature). The choice is deliberate — IS/CAN/NOT match the
meta-property calculus's epistemic readings.
-/

/-- Three-valued meta-property assignment.

`is` means the concept definitely has this meta-property value.
`not` means the concept definitely does not.
`can` means indeterminate — not yet resolved. -/
inductive MetaValue where
  | is  : MetaValue
  | not : MetaValue
  | can : MetaValue
  deriving DecidableEq, Repr, Inhabited

namespace MetaValue

/-- CAN is the "no information" value — the default before any rule fires. -/
instance : Inhabited MetaValue where
  default := .can

/-- A `MetaValue` is determined (not CAN). -/
def isDetermined : MetaValue → Prop
  | .is  => True
  | .not => True
  | .can => False

instance : DecidablePred isDetermined := fun v =>
  match v with
  | .is  => .isTrue trivial
  | .not => .isTrue trivial
  | .can => .isFalse (fun h => h)

end MetaValue

/-- The information ordering on `MetaValue`.

`CAN ≤ IS`, `CAN ≤ NOT`; `IS` and `NOT` are incomparable. This is the flat
information ordering where `CAN` means "no information." It is a partial
order but NOT a lattice (`IS ⊔ NOT` is undefined). -/
instance : PartialOrder MetaValue where
  le a b := a = .can ∨ a = b
  le_refl a := Or.inr rfl
  le_trans a b c hab hbc := by
    cases hab with
    | inl ha => exact Or.inl ha
    | inr hab => rw [hab]; exact hbc
  le_antisymm a b hab hba := by
    cases hab with
    | inl ha => subst ha; cases hba with
      | inl hb => exact hb.symm
      | inr hba => exact hba.symm
    | inr hab => exact hab

/-- CAN is the bottom element. -/
theorem MetaValue.can_le (v : MetaValue) : MetaValue.can ≤ v :=
  Or.inl rfl

/-- IS is not ≤ NOT. -/
theorem MetaValue.is_not_le_not : ¬(MetaValue.is ≤ MetaValue.not) := by
  intro h
  cases h with
  | inl h => exact MetaValue.noConfusion h
  | inr h => exact MetaValue.noConfusion h

/-- NOT is not ≤ IS. -/
theorem MetaValue.not_not_le_is : ¬(MetaValue.not ≤ MetaValue.is) := by
  intro h
  cases h with
  | inl h => exact MetaValue.noConfusion h
  | inr h => exact MetaValue.noConfusion h

/-- Non-CAN values are maximal in the information ordering: if `a ≤ b`
and `a ≠ .can`, then `a = b`.

This captures the essential property of the IS/CAN/NOT ordering: CAN is
the only value that can "increase" to something else. Once a value is IS
or NOT, it is fixed — gaining information cannot change it. -/
theorem MetaValue.determined_le_eq {a b : MetaValue}
    (hne : a ≠ .can) (hle : a ≤ b) : a = b := by
  cases hle with
  | inl hcan => exact absurd hcan hne
  | inr heq => exact heq
