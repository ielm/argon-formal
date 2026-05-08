/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.Decidability.CrossDomain.Staging
import ArgonFormal.Decidability.Domain2.Decidability

/-!
# Theorem 3: Cross-Domain Decidability

Predicates mixing Domain 1 (type graph) and Domain 2 (instance) atoms
are decidable. The proof:

1. Domain 1 atoms are evaluated first at elaboration time (Theorem 1).
2. Their truth values become constants in the staged predicate.
3. The residual is a pure Domain 2 predicate (or ground Boolean).
4. Domain 2 predicates are decidable (Theorem 2).
5. Constants don't increase complexity.

## Main results

- `mixedDecidable` — **Theorem 3**: mixed predicate evaluation is decidable
-/

/-- Decidability of staged results. -/
noncomputable def stagedDecidable : (s : Staged) → Decidable (stagedEval s)
  | .ground b => decEq b true
  | .residual q => d2Decidable q
  | .andS s₁ s₂ => by
    haveI := stagedDecidable s₁
    haveI := stagedDecidable s₂
    exact instDecidableAnd
  | .orS s₁ s₂ => by
    haveI := stagedDecidable s₁
    haveI := stagedDecidable s₂
    exact instDecidableOr
  | .notS s => by
    haveI := stagedDecidable s
    exact instDecidableNot

/-- **Theorem 3: Cross-Domain Decidability.**

For any mixed predicate `φ` combining Domain 1 and Domain 2 atoms,
checking whether `φ` holds is decidable.

The two domains are evaluated at different times (elaboration vs reasoning),
so they don't interact during checking. Domain 1 atoms become ground
constants via Theorem 1; the residual Domain 2 predicate is decidable
via Theorem 2. -/
noncomputable def mixedDecidable {C A : Type} [Fintype C] [DecidableEq C]
    [Fintype A] [DecidableEq A]
    (G : TypeGraph C A) (c : C) (φ : MixedPred C A) :
    Decidable (mixedEval G c φ) :=
  -- Use staging to reduce to a Staged value, then decide that. The staging
  -- lemma gives `mixedEval G c φ ↔ stagedEval (stage G c φ)`, so decidability
  -- transfers via `decidable_of_iff`.
  haveI : Decidable (stagedEval (stage G c φ)) := stagedDecidable (stage G c φ)
  decidable_of_iff (stagedEval (stage G c φ)) (stage_correct G c φ).symm
