/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.Decidability.Fragment

/-!
# Domain 2: External Decidability Results

Domain 2 predicates evaluate over instance populations at reasoning time.
Their decidability relies on external results that we axiomatize rather
than mechanize:

- **QF-LIA** (quantifier-free linear integer arithmetic): decidable, NP-complete.
  Standard result from Presburger arithmetic.
- **GNFO** (guarded negation first-order logic): decidable, 2-EXPTIME-complete.
  Bárány, ten Cate & Segoufin (2015).
- **Theory combination**: QF-LIA + GNFO is decidable via reduction to
  EPR + QF-LIA, which Z3's MBQI decides. Ge & de Moura (2009).

These axioms are clearly marked with citations. We use `axiom` rather than
`sorry` because these are externally justified mathematical facts.

## Main axioms

- `d2Sat` — satisfaction relation for Domain 2 predicates
- `d2Decidable` — decidability of the combined fragment
-/

/-- Satisfaction relation for Domain 2 predicates.
    Axiomatized — we do not formalize the instance model. -/
axiom d2Sat : D2Pred → Prop

/-- **QF-LIA decidability.**
    Quantifier-free Presburger arithmetic is decidable (NP-complete).
    Standard result; mechanized in multiple proof assistants. -/
axiom qfliaDecidable : ∀ (φ : D2Pred), φ = .qflia → Decidable (d2Sat φ)

/-- **GNFO decidability.**
    Guarded Negation First-Order Logic is decidable (2-EXPTIME-complete).
    Reference: Bárány, ten Cate & Segoufin, "Guarded Negation" (2015). -/
axiom gnfoDecidable : ∀ (φ : D2Pred), φ = .gnfo → Decidable (d2Sat φ)

/-- **Combined fragment decidability.**
    The combination QF-LIA + GNFO + finite enumeration equality is decidable.

    Justification: Argon's Domain 2 fragment reduces to EPR + QF-LIA, which is
    decidable via MBQI (Ge & de Moura, "Complete Instantiation for Quantified
    Formulas in SMT", 2009). GNFO constraints over the finite type graph
    reduce to EPR because the type graph is finite.

    Nelson-Oppen theory combination (1979) handles the shared equality
    between QF-LIA and the finite domain theory. Both theories are
    stably infinite and support equality, so the combination is decidable. -/
axiom d2CombinedDecidable : ∀ (φ : D2Pred), Decidable (d2Sat φ)
