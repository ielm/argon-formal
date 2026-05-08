/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.Decidability.Fragment
import Mathlib.Logic.Relation

/-!
# Domain 1 Evaluation Semantics

Defines the evaluation function for Domain 1 predicates over a finite type graph.
The evaluator is a `Prop`-valued function — decidability is proved separately in
`Domain1/Decidability.lean`.

## Main definitions

- `d1Eval` — evaluate a Domain 1 predicate against a type graph and focus concept
-/

open Relation in
/-- Evaluate a Domain 1 predicate against a type graph.

The "focus concept" `c : C` is the concept that quantifiers (`forallC`, `existsC`)
iterate over. For non-quantified predicates, the focus is unused — the relevant
concept is embedded in the predicate itself (e.g., `metaEq c' a v` carries `c'`).

**Structural recursion:** Every recursive call passes a strict subterm of the
predicate. The quantifier cases (`forallC`, `existsC`, `hasAnc`, `hasDesc`,
`countGeq`) change the focus concept but recurse on a smaller predicate. -/
noncomputable def d1Eval {C A : Type} [Fintype C] [DecidableEq C]
    [Fintype A] [DecidableEq A]
    (G : TypeGraph C A) (c : C) : D1Pred C A → Prop
  | .metaEq c' a v  => G.metaProp c' a = v
  | .isDet c' a     => (G.metaProp c' a).isDetermined
  | .hasAnc c' sub  => ∃ c'' : C, TransGen G.specializes c' c'' ∧ d1Eval G c'' sub
  | .hasDesc c' sub => ∃ c'' : C, TransGen (flip G.specializes) c' c'' ∧ d1Eval G c'' sub
  | .countGeq sub n => ∃ S : Finset C, n ≤ S.card ∧ ∀ c' ∈ S, d1Eval G c' sub
  | .forallC sub    => ∀ c' : C, d1Eval G c' sub
  | .existsC sub    => ∃ c' : C, d1Eval G c' sub
  | .andP p q       => d1Eval G c p ∧ d1Eval G c q
  | .orP p q        => d1Eval G c p ∨ d1Eval G c q
  | .notP p         => ¬ d1Eval G c p
  | .tt             => True
  | .ff             => False
