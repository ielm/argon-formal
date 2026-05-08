/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Card
import ArgonFormal.Foundation.MetaValue
import ArgonFormal.Schema.TypeGraph

/-!
# Argon Decidability: Predicate Fragment

The inductive grammar of Argon's refinement predicate fragment. This is
the formal definition of the language whose decidability we prove.

## The Two Domains

**Domain 1 (type graph, elaboration-time):** All predicates evaluate over a finite,
known DAG of concepts with meta-property assignments. Quantification is bounded
over this finite graph. Transitive closure is precomputable.

**Domain 2 (instances, reasoning-time):** Predicates over instance populations that
may be unbounded under OWA. Includes QF-LIA (value predicates) and GNFO (guarded
negation). Decidability appeals to external results.

**Mixed predicates** combine both domains. The staging theorem (Theorem 3) shows
that evaluating Domain 1 atoms first and replacing them with constants preserves
semantics and decidability.

## Main definitions

- `D1Pred` — Domain 1 predicate AST
- `D2Pred` — Domain 2 predicate AST (partially opaque)
- `MixedPred` — predicates mixing both domains
-/

/-- Domain 1 predicates: evaluated over the finite type graph at elaboration time.

The evaluator (`d1Eval` in `Domain1/Eval.lean`) takes a `TypeGraph C A` and a
"focus concept" `c : C`, and interprets each constructor:

- `metaEq c' a v` — the meta-property of concept `c'` on axis `a` equals `v`
- `isDet c' a` — the meta-property of `c'` on `a` is determined (IS or NOT, not CAN)
- `hasAnc c' sub` — some ancestor of `c'` (via transitive specialization) satisfies `sub`
- `hasDesc c' sub` — some descendant of `c'` satisfies `sub`
- `countGeq sub n` — at least `n` concepts in the type graph satisfy `sub`
- `forallC sub` — every concept satisfies `sub`
- `existsC sub` — some concept satisfies `sub`
- `andP`, `orP`, `notP` — Boolean connectives
- `tt`, `ff` — literal truth values

All quantification is bounded over the finite concept type `C`, ensuring
decidability by reduction to finite iteration. -/
inductive D1Pred (C A : Type) : Type where
  /-- Meta-property equality: `c.a == v` -/
  | metaEq   : C → A → MetaValue → D1Pred C A
  /-- Determinacy test: `isDetermined(c.a)` -/
  | isDet    : C → A → D1Pred C A
  /-- Ancestor test: `∃ c' ∈ ancestors(c), P(c')` via transitive closure -/
  | hasAnc   : C → D1Pred C A → D1Pred C A
  /-- Descendant test: `∃ c' ∈ descendants(c), P(c')` via inverse TC -/
  | hasDesc  : C → D1Pred C A → D1Pred C A
  /-- Counting: `|{c' : C | P(c')}| ≥ n` -/
  | countGeq : D1Pred C A → Nat → D1Pred C A
  /-- Universal quantification: `∀ c' : C, P(c')` -/
  | forallC  : D1Pred C A → D1Pred C A
  /-- Existential quantification: `∃ c' : C, P(c')` -/
  | existsC  : D1Pred C A → D1Pred C A
  /-- Conjunction -/
  | andP     : D1Pred C A → D1Pred C A → D1Pred C A
  /-- Disjunction -/
  | orP      : D1Pred C A → D1Pred C A → D1Pred C A
  /-- Negation -/
  | notP     : D1Pred C A → D1Pred C A
  /-- Literal true -/
  | tt       : D1Pred C A
  /-- Literal false -/
  | ff       : D1Pred C A
  deriving Repr

/-- Domain 2 predicates: evaluated over instance values at reasoning time.

These are partially opaque — we do not formalize the internal structure of
QF-LIA formulas or GNFO sentences. Decidability is established by appeal to
external results (Presburger arithmetic, Bárány et al. 2015).

- `qflia` — a quantifier-free linear integer arithmetic formula
- `gnfo` — a guarded negation first-order logic sentence
- `enumEq` — equality over a finite enumeration (e.g., `phase == Active`)
- `andP`, `orP`, `notP` — Boolean connectives -/
inductive D2Pred : Type where
  /-- QF-LIA formula (opaque). Decidable by Presburger arithmetic (NP). -/
  | qflia  : D2Pred
  /-- GNFO sentence (opaque). Decidable by Bárány et al. 2015 (2-EXPTIME). -/
  | gnfo   : D2Pred
  /-- Finite enumeration equality (opaque). Decidable in O(1). -/
  | enumEq : D2Pred
  /-- Conjunction -/
  | andP   : D2Pred → D2Pred → D2Pred
  /-- Disjunction -/
  | orP    : D2Pred → D2Pred → D2Pred
  /-- Negation -/
  | notP   : D2Pred → D2Pred
  deriving Repr

/-- Mixed predicates: combine Domain 1 and Domain 2 atoms.

The staging theorem (Theorem 3) shows these are decidable:
Domain 1 atoms are evaluated first (at elaboration time) to ground truth
values, which become constants in the Domain 2 predicate. -/
inductive MixedPred (C A : Type) : Type where
  /-- A Domain 1 predicate (type graph) -/
  | d1   : D1Pred C A → MixedPred C A
  /-- A Domain 2 predicate (instances) -/
  | d2   : D2Pred → MixedPred C A
  /-- Conjunction -/
  | andP : MixedPred C A → MixedPred C A → MixedPred C A
  /-- Disjunction -/
  | orP  : MixedPred C A → MixedPred C A → MixedPred C A
  /-- Negation -/
  | notP : MixedPred C A → MixedPred C A
  deriving Repr
