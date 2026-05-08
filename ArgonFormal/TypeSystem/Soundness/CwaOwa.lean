/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.TypeSystem.NarrowEnv

/-!
# CWA/OWA Boundary Preservation

Proves that narrowings established under CWA (Closed World Assumption) carry
monotonically into OWA (Open World Assumption) contexts.

## Background

In Argon, modules can declare CWA or OWA per-field. Under CWA, missing values
are assumed absent (no CAN values). Under OWA, CAN is permitted.

When a CWA module passes a value to an OWA module, the CWA guarantee that
`field is not unknown` carries across. The OWA module can use this for narrowing
without re-proving it.

## Key Results

1. CWA completeness (no CAN on covered axes) is preserved under information increase
2. Narrowings from CWA contexts hold in OWA extensions
-/

variable {C A : Type} [DecidableEq C] [DecidableEq A] [Fintype C] [Fintype A]

/-! ## CWA Completeness -/

/-- A state satisfies CWA for a set of axes: no CAN values on those axes. -/
def State.isCwa (s : State C A) (axes : Finset A) : Prop :=
  ∀ (c : C) (a : A), a ∈ axes → s c a ≠ .can

omit [Fintype C] [Fintype A] in
/-- CWA completeness is preserved under information increase.

If `s` has no CAN values on the covered axes and `s ≤ t`, then `t` has no
CAN values either. This is because IS and NOT are maximal in the information
ordering — they can only stay the same, never revert to CAN.

Formally: IS ≤ x implies x = IS, and NOT ≤ x implies x = NOT. So
if s(c,a) ≠ CAN, then t(c,a) = s(c,a) ≠ CAN. -/
theorem State.isCwa_mono {s t : State C A} {axes : Finset A}
    (hle : s ≤ t) (h : s.isCwa axes) : t.isCwa axes := by
  intro c a ha
  have h_ne := h c a ha
  have h_eq := MetaValue.determined_le_eq h_ne (hle c a)
  rw [← h_eq]; exact h_ne

/-! ## Cross-Module Narrowing Preservation -/

omit [Fintype C] [Fintype A] in
/-- Narrowings established under CWA carry into OWA contexts.

When a CWA module checks `x.field is not unknown` and narrows `x`, this
narrowing remains valid when `x` is passed to an OWA module — because
the OWA module's state can only have MORE information (it includes the
CWA module's conclusions plus its own). -/
theorem cwa_narrowing_into_owa (env : NarrowEnv C A) {s_cwa s_owa : State C A}
    (hle : s_cwa ≤ s_owa) (h : env.satisfiedBy s_cwa) :
    env.satisfiedBy s_owa :=
  env.satisfiedBy_mono hle h

omit [Fintype C] [Fintype A] in
/-- If a state is CWA-complete on a set of axes, then `isDetermined` narrowings
for those axes are trivially satisfied. -/
theorem isCwa_implies_determined (s : State C A) (axes : Finset A)
    (hcwa : s.isCwa axes) (c : C) (a : A) (ha : a ∈ axes) :
    (NarrowPred.isDetermined c a : NarrowPred C A).holds s :=
  hcwa c a ha
