/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.Decidability.Domain2.Theories

/-!
# Theorem 2: Domain 2 Decidability

The fragment QF-LIA + GNFO + counting over instances is decidable.

This is thin by design — the real content is in the axioms (`Theories.lean`)
and their external justification. This file provides the theorem statement
that downstream files (cross-domain, complexity) can import.

## Main results

- `d2Decidable` — **Theorem 2**: Domain 2 evaluation is decidable
-/

/-- **Theorem 2: Domain 2 Decidability (Instance Checking).**

For any Domain 2 predicate `φ`, checking satisfaction is decidable.
By appeal to the combined decidability axiom, which rests on:
- Presburger arithmetic for QF-LIA (NP-complete)
- Bárány et al. 2015 for GNFO (2-EXPTIME-complete)
- Ge & de Moura 2009 for the EPR + QF-LIA combination -/
noncomputable def d2Decidable (φ : D2Pred) : Decidable (d2Sat φ) :=
  d2CombinedDecidable φ
