/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.Decidability.Domain1.Decidability
import ArgonFormal.Decidability.Domain2.Theories

/-!
# Cross-Domain Staging

The staging semantics for mixed predicates: Domain 1 atoms are evaluated first
(at elaboration time) and replaced with truth value constants, yielding a pure
Domain 2 predicate (or a ground Boolean).

This is the key to Theorem 3: the two domains don't interact during checking
because they are evaluated at different times.

## Main definitions

- `MixedEval` — evaluation of mixed predicates
- `stage` — replace Domain 1 atoms with their truth values
- `stage_correct` — staging preserves semantics
-/

/-- Evaluation of mixed predicates.

Domain 1 atoms are evaluated against the type graph at focus concept `c`.
Domain 2 atoms appeal to `d2Sat`. -/
noncomputable def mixedEval {C A : Type} [Fintype C] [DecidableEq C]
    [Fintype A] [DecidableEq A]
    (G : TypeGraph C A) (c : C) : MixedPred C A → Prop
  | .d1 p     => d1Eval G c p
  | .d2 q     => d2Sat q
  | .andP p q => mixedEval G c p ∧ mixedEval G c q
  | .orP p q  => mixedEval G c p ∨ mixedEval G c q
  | .notP p   => ¬ mixedEval G c p

/-- The result of staging: either a ground Boolean or a residual D2 predicate. -/
inductive Staged where
  /-- Domain 1 atom fully evaluated to a ground truth value. -/
  | ground : Bool → Staged
  /-- Domain 2 atom preserved for reasoning-time evaluation. -/
  | residual : D2Pred → Staged
  /-- Conjunction of staged results. -/
  | andS : Staged → Staged → Staged
  /-- Disjunction of staged results. -/
  | orS : Staged → Staged → Staged
  /-- Negation of a staged result. -/
  | notS : Staged → Staged

/-- Evaluate a staged result. -/
noncomputable def stagedEval : Staged → Prop
  | .ground b    => b = true
  | .residual q  => d2Sat q
  | .andS s₁ s₂ => stagedEval s₁ ∧ stagedEval s₂
  | .orS s₁ s₂  => stagedEval s₁ ∨ stagedEval s₂
  | .notS s      => ¬ stagedEval s

/-- Stage a mixed predicate: evaluate Domain 1 atoms using Theorem 1,
    replace with Boolean constants. Domain 2 atoms pass through unchanged. -/
noncomputable def stage {C A : Type} [Fintype C] [DecidableEq C]
    [Fintype A] [DecidableEq A]
    (G : TypeGraph C A) (c : C) : MixedPred C A → Staged
  | .d1 p     =>
    -- Use Theorem 1 to evaluate the D1 predicate to a Boolean
    match d1Decidable G c p with
    | .isTrue _  => .ground true
    | .isFalse _ => .ground false
  | .d2 q     => .residual q
  | .andP p q => .andS (stage G c p) (stage G c q)
  | .orP p q  => .orS (stage G c p) (stage G c q)
  | .notP p   => .notS (stage G c p)

/-- **Staging Lemma:** Staging preserves semantics.

The truth value of a mixed predicate equals the truth value of its
staged form. Domain 1 atoms are correctly replaced by their ground
truth values; Domain 2 atoms are unchanged. -/
theorem stage_correct {C A : Type} [Fintype C] [DecidableEq C]
    [Fintype A] [DecidableEq A]
    (G : TypeGraph C A) (c : C) (φ : MixedPred C A) :
    mixedEval G c φ ↔ stagedEval (stage G c φ) := by
  induction φ with
  | d1 p =>
    -- mixedEval = d1Eval; stage uses d1Decidable to ground the result.
    simp only [mixedEval, stage]
    cases d1Decidable G c p with
    | isTrue h  =>
      -- stage produces `.ground true`; stagedEval = (true = true).
      show d1Eval G c p ↔ stagedEval (.ground true)
      constructor
      · intro _; show (true : Bool) = true; rfl
      · intro _; exact h
    | isFalse h =>
      -- stage produces `.ground false`; stagedEval = (false = true) which is False.
      show d1Eval G c p ↔ stagedEval (.ground false)
      constructor
      · intro hp; exact absurd hp h
      · intro hf
        -- hf : stagedEval (.ground false) = (false = true), absurd.
        exact absurd hf Bool.false_ne_true
  | d2 q =>
    -- Both sides reduce to d2Sat q.
    simp only [mixedEval, stage, stagedEval]
  | andP p q ihp ihq =>
    -- Inductive: meet on both sides.
    simp only [mixedEval, stage, stagedEval]
    exact and_congr ihp ihq
  | orP p q ihp ihq =>
    -- Inductive: join on both sides.
    simp only [mixedEval, stage, stagedEval]
    exact or_congr ihp ihq
  | notP p ihp =>
    -- Inductive: negation on both sides.
    simp only [mixedEval, stage, stagedEval]
    exact not_congr ihp
