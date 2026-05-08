/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.Decidability.Domain1.Eval
import ArgonFormal.Decidability.Domain1.TC
import Mathlib.Data.Fintype.Powerset

/-!
# Theorem 1: Domain 1 Decidability

For any Domain 1 predicate φ over a finite type graph G = (V, E, μ),
checking G ⊨ φ is decidable.

## Proof strategy

By recursion on the predicate AST. Each case reduces to decidability
on finite types, which Lean 4 + Mathlib provides:

- Equality: `DecidableEq MetaValue`
- Determinacy: `DecidablePred MetaValue.isDetermined`
- TC reachability: `transGenDecidable` (from `TC.lean`)
- Bounded quantification: Lean's `Fintype.decidableForallFintype`
- Counting: decidable existential over `Finset C` (which is `Fintype`)
- Boolean connectives: `instDecidableAnd` / `instDecidableOr` / `instDecidableNot`

## Main results

- `d1Decidable` — **Theorem 1**: Domain 1 evaluation is decidable
-/

/-- **Theorem 1: Domain 1 Decidability (Finite Model Checking).**

For any Domain 1 predicate `φ` and finite type graph `G`, checking whether
`φ` holds at focus concept `c` is decidable. The proof is by structural
recursion on `φ`, reducing each case to decidability on finite types.

This is the central mechanized result: over a finite type graph, the entire
Domain 1 predicate fragment (meta-property checks, transitive closure,
counting, bounded quantification) is decidable. -/
noncomputable def d1Decidable {C A : Type} [Fintype C] [DecidableEq C]
    [Fintype A] [DecidableEq A]
    (G : TypeGraph C A) (c : C) : (φ : D1Pred C A) → Decidable (d1Eval G c φ)
  | .metaEq c' a v =>
    -- G.metaProp c' a = v — decidable equality on MetaValue
    decEq (G.metaProp c' a) v
  | .isDet c' a =>
    -- (G.metaProp c' a).isDetermined — decidable predicate
    MetaValue.instDecidablePredIsDetermined (G.metaProp c' a)
  | .hasAnc c' sub => by
    -- ∃ c'' : C, TransGen G.specializes c' c'' ∧ d1Eval G c'' sub
    -- TransGen is decidable (TC.lean), d1Eval is decidable by recursion
    haveI : ∀ c'', Decidable (d1Eval G c'' sub) := fun c'' => d1Decidable G c'' sub
    exact Fintype.decidableExistsFintype
  | .hasDesc c' sub => by
    -- ∃ c'' : C, TransGen (flip G.specializes) c' c'' ∧ d1Eval G c'' sub
    haveI : DecidableRel (flip G.specializes) := fun a b => G.specializes_dec b a
    haveI : ∀ c'', Decidable (d1Eval G c'' sub) := fun c'' => d1Decidable G c'' sub
    exact Fintype.decidableExistsFintype
  | .countGeq sub n => by
    -- ∃ S : Finset C, n ≤ S.card ∧ ∀ c' ∈ S, d1Eval G c' sub
    -- By recursion, d1Eval is decidable for each c'
    haveI : ∀ c', Decidable (d1Eval G c' sub) := fun c' => d1Decidable G c' sub
    -- Finset C is Fintype when C is Fintype, and the inner predicate is decidable
    exact Fintype.decidableExistsFintype
  | .forallC sub => by
    -- ∀ c' : C, d1Eval G c' sub — finite universal
    haveI : ∀ c', Decidable (d1Eval G c' sub) := fun c' => d1Decidable G c' sub
    exact Fintype.decidableForallFintype
  | .existsC sub => by
    -- ∃ c' : C, d1Eval G c' sub — finite existential
    haveI : ∀ c', Decidable (d1Eval G c' sub) := fun c' => d1Decidable G c' sub
    exact Fintype.decidableExistsFintype
  | .andP p q => by
    haveI := d1Decidable G c p
    haveI := d1Decidable G c q
    exact instDecidableAnd
  | .orP p q => by
    haveI := d1Decidable G c p
    haveI := d1Decidable G c q
    exact instDecidableOr
  | .notP p => by
    haveI := d1Decidable G c p
    exact instDecidableNot
  | .tt => .isTrue trivial
  | .ff => .isFalse id
