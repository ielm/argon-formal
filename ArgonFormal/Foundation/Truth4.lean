/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.Foundation.MetaValue
import ArgonFormal.Reasoning.State
import ArgonFormal.Reasoning.Stratification

/-!
# Truth4 — Belnap–Dunn FDE Four-Valued Lattice

Defines the four-valued logic FDE (First-Degree Entailment, Belnap 1977 / Dunn 1976)
and proves its bilattice algebraic properties. This is the superlattice over the
existing `MetaValue` (K3, three-valued); `MetaValue` is recovered as the consistent
fragment of `Truth4` (theorem `Truth4.k3_iso` in `LatticeContext.lean`).

## The four values

- `is`   — told only true (T)
- `not`  — told only false (F)
- `can`  — told nothing yet (N / Unknown / Neither)
- `both` — told both T and F by distinct sources (B / Inconsistent)

The first three reproduce the existing `MetaValue` exactly. `both` is the new value
that captures *cross-source inconsistency* — only reachable when multiple sources
contribute conflicting evidence (e.g., cross-standpoint federated queries).

## The two orderings (Fitting 1991)

A bilattice carries two independent partial orders on the same carrier:

- **Truth ordering** (`truthLe`, `≤_t`): `not ≤_t (can | both) ≤_t is`. Reads "how
  strongly the evidence skews positive." `can` and `both` are *incomparable* in the
  truth ordering — both sit between `not` and `is`.

- **Information ordering** (`infoLe`, `≤_k`): `can ≤_k (is | not) ≤_k both`. Reads
  "how much evidence we have." `is` and `not` are *incomparable* in the information
  ordering — they're both maximally informed but in different directions.

Restricting `Truth4` to the consistent fragment `{is, not, can}` and dropping
`both` from the information ordering recovers exactly the existing `MetaValue`
information ordering.

## The four core operations

| Op | Symbol | Meaning |
|---|---|---|
| Truth meet | `∧_t` | Truth-order greatest lower bound. Used by conjunction in refinement bodies. |
| Truth join | `∨_t` | Truth-order least upper bound. Used by disjunction. |
| Negation  | `¬`   | Swap `is`/`not`; fix `can`/`both`. |
| Info meet | `⊗`   | Information-order greatest lower bound (*consensus* — drop disagreements to `can`). |
| Info join | `⊕`   | Information-order least upper bound (*gullibility* — accumulate to `both`). |

The K3 fragment (consistent values) is closed under truth meet, truth join,
negation, and information meet. It is **not** closed under information join —
`is ⊕ not = both` is exactly the cross-source-disagreement case where federation
escapes the K3 fragment.

## What is NOT in this file

This file defines the algebra. The K3/FDE/Boolean type-level lattice contexts
and the K3 ⊆ Truth4 closure theorems live in `LatticeContext.lean`. Projection
morphisms with policy parameters live in `Projection.lean`. Cross-standpoint
federation lives in `Federation.lean`.

## References

- Belnap, N.D. (1977). *A Useful Four-Valued Logic.* In Dunn & Epstein (eds.),
  *Modern Uses of Multiple-Valued Logic*, D. Reidel.
- Dunn, J.M. (1976). *Intuitive Semantics for First-Degree Entailments and
  'Coupled Trees'.* Philosophical Studies 29.
- Fitting, M. (1991). *Bilattices and the Semantics of Logic Programming.*
  Journal of Logic Programming 11(2):91–116.
-/

/-! ## The four-valued type -/

/-- Belnap–Dunn FDE four-valued type. Generalizes `MetaValue` by adding `both` —
the inconsistent value, only reachable under cross-source aggregation. -/
inductive Truth4 where
  /-- Told only true. Same as `MetaValue.is`. -/
  | is : Truth4
  /-- Told only false. Same as `MetaValue.not`. -/
  | not : Truth4
  /-- Told nothing yet. Same as `MetaValue.can`. -/
  | can : Truth4
  /-- Told both T and F by distinct sources. Inconsistent. New in FDE. -/
  | both : Truth4
  deriving DecidableEq, Repr, Inhabited

namespace Truth4

/-- `can` is the default — no information yet. Matches `MetaValue.default`. -/
instance : Inhabited Truth4 where
  default := .can

/-- A `Truth4` value is *consistent* if it does not contain a contradiction.
The consistent fragment is `{is, not, can}` — exactly `MetaValue`. -/
def isConsistent : Truth4 → Prop
  | .both => False
  | _     => True

instance : DecidablePred isConsistent := fun v =>
  match v with
  | .is   => .isTrue trivial
  | .not  => .isTrue trivial
  | .can  => .isTrue trivial
  | .both => .isFalse (fun h => h)

/-- A `Truth4` value is *determined* if it is positively committed in one direction:
`is` or `not`. `can` and `both` are both undetermined, but for different reasons. -/
def isDetermined : Truth4 → Prop
  | .is  => True
  | .not => True
  | _    => False

instance : DecidablePred isDetermined := fun v =>
  match v with
  | .is   => .isTrue trivial
  | .not  => .isTrue trivial
  | .can  => .isFalse (fun h => h)
  | .both => .isFalse (fun h => h)

/-! ## Truth ordering — `≤_t`

Reading: "how strongly the evidence skews positive." `not` is bottom, `is` is top.
`can` and `both` both sit strictly between, both incomparable to each other:
they're both "unsettled" in different ways.

Truth tables:
- `not ≤_t can`, `not ≤_t both`, `not ≤_t is`
- `can ≤_t is`, `both ≤_t is`
- `can` and `both` are incomparable (neither ≤ the other) -/

/-- The truth ordering: `a ≤_t b` iff "b is at least as truthy as a". -/
def truthLe : Truth4 → Truth4 → Prop
  | .not,  _     => True
  | _,     .is   => True
  | .can,  .can  => True
  | .both, .both => True
  | _,     _     => False

/-- `≤_t` is decidable. -/
instance : DecidableRel truthLe := fun a b =>
  match a, b with
  | .not,  _     => .isTrue (by cases b <;> simp [truthLe])
  | .is,   .is   => .isTrue trivial
  | .is,   .not  => .isFalse (by simp [truthLe])
  | .is,   .can  => .isFalse (by simp [truthLe])
  | .is,   .both => .isFalse (by simp [truthLe])
  | .can,  .is   => .isTrue trivial
  | .can,  .not  => .isFalse (by simp [truthLe])
  | .can,  .can  => .isTrue trivial
  | .can,  .both => .isFalse (by simp [truthLe])
  | .both, .is   => .isTrue trivial
  | .both, .not  => .isFalse (by simp [truthLe])
  | .both, .can  => .isFalse (by simp [truthLe])
  | .both, .both => .isTrue trivial

theorem truthLe_refl (a : Truth4) : truthLe a a := by
  cases a <;> simp [truthLe]

theorem truthLe_trans {a b c : Truth4} (hab : truthLe a b) (hbc : truthLe b c) : truthLe a c := by
  cases a <;> cases b <;> cases c <;> simp_all [truthLe]

theorem truthLe_antisymm {a b : Truth4} (hab : truthLe a b) (hba : truthLe b a) : a = b := by
  cases a <;> cases b <;> simp_all [truthLe]

/-! ## Information ordering — `≤_k`

Reading: "how much evidence we have." `can` is bottom (no info), `both` is top
(maximum info, including conflict). `is` and `not` are both maximal in their
respective directions but incomparable.

Truth tables:
- `can ≤_k is`, `can ≤_k not`, `can ≤_k both`
- `is ≤_k both`, `not ≤_k both`
- `is` and `not` are incomparable (neither ≤ the other)

This is the ordering that mirrors the existing `MetaValue.PartialOrder` on the
consistent fragment. The new value `both` extends it with a top element. -/

/-- The information ordering: `a ≤_k b` iff "b has at least as much information as a". -/
def infoLe : Truth4 → Truth4 → Prop
  | .can,  _     => True
  | _,     .both => True
  | .is,   .is   => True
  | .not,  .not  => True
  | _,     _     => False

instance : DecidableRel infoLe := fun a b =>
  match a, b with
  | .can,  _     => .isTrue (by cases b <;> simp [infoLe])
  | .is,   .is   => .isTrue trivial
  | .is,   .not  => .isFalse (by simp [infoLe])
  | .is,   .can  => .isFalse (by simp [infoLe])
  | .is,   .both => .isTrue trivial
  | .not,  .is   => .isFalse (by simp [infoLe])
  | .not,  .not  => .isTrue trivial
  | .not,  .can  => .isFalse (by simp [infoLe])
  | .not,  .both => .isTrue trivial
  | .both, .is   => .isFalse (by simp [infoLe])
  | .both, .not  => .isFalse (by simp [infoLe])
  | .both, .can  => .isFalse (by simp [infoLe])
  | .both, .both => .isTrue trivial

theorem infoLe_refl (a : Truth4) : infoLe a a := by
  cases a <;> simp [infoLe]

theorem infoLe_trans {a b c : Truth4} (hab : infoLe a b) (hbc : infoLe b c) : infoLe a c := by
  cases a <;> cases b <;> cases c <;> simp_all [infoLe]

theorem infoLe_antisymm {a b : Truth4} (hab : infoLe a b) (hba : infoLe b a) : a = b := by
  cases a <;> cases b <;> simp_all [infoLe]

/-- `can` is bottom in the information ordering. -/
theorem can_infoLe (v : Truth4) : infoLe .can v := by
  cases v <;> simp [infoLe]

/-- `both` is top in the information ordering. -/
theorem infoLe_both (v : Truth4) : infoLe v .both := by
  cases v <;> simp [infoLe]

/-! ## Truth meet `∧_t` and join `∨_t`

The operations on the truth ordering. These are the connectives users see in
refinement-body conjunctions and disjunctions: `where { p and q }`, `where { p or q }`. -/

/-- Truth meet: `a ∧_t b` is the truth-greatest-lower-bound. Pessimistic
in K3: `is ∧_t can = can` (an unknown clause makes the conjunction unknown). -/
def truthMeet : Truth4 → Truth4 → Truth4
  | .not,  _     => .not
  | _,     .not  => .not
  | .is,   y     => y
  | x,     .is   => x
  | .can,  .can  => .can
  | .can,  .both => .not  -- consensus on the F-side; see Belnap 1977 §1
  | .both, .can  => .not
  | .both, .both => .both

/-- Truth join: `a ∨_t b` is the truth-least-upper-bound. Optimistic in K3:
`not ∨_t can = can` (an unknown clause cannot rescue a refuted disjunction
from below `is`, but cannot push it down either). -/
def truthJoin : Truth4 → Truth4 → Truth4
  | .is,   _     => .is
  | _,     .is   => .is
  | .not,  y     => y
  | x,     .not  => x
  | .can,  .can  => .can
  | .can,  .both => .is   -- only common upper bound is `is`
  | .both, .can  => .is
  | .both, .both => .both

/-- Negation: swap `is`/`not`, fix `can`/`both`. -/
def neg : Truth4 → Truth4
  | .is   => .not
  | .not  => .is
  | .can  => .can
  | .both => .both

/-- Negation is involutive. -/
theorem neg_neg (a : Truth4) : neg (neg a) = a := by
  cases a <;> rfl

/-! ## Information meet `⊗` and join `⊕`

Information-side operations. `⊗` is *consensus* — combining sources, drop
disagreements. `⊕` is *gullibility* — accumulate everything, including conflict.

`⊕` is the operation that produces `both` from consistent inputs (`is ⊕ not = both`)
and is therefore the operation that escapes the K3 fragment. -/

/-- Information meet (consensus): `a ⊗ b` retains only what both sources agree on.
Cross-source agreement: `is ⊗ not = can` (drop the conflict to "no info"). -/
def infoMeet : Truth4 → Truth4 → Truth4
  | .can,  _     => .can
  | _,     .can  => .can
  | .is,   .is   => .is
  | .is,   .not  => .can  -- consensus: disagreement collapses
  | .not,  .is   => .can
  | .not,  .not  => .not
  | .both, .is   => .is   -- both ⊓_k is = is (info-meet)
  | .is,   .both => .is
  | .both, .not  => .not
  | .not,  .both => .not
  | .both, .both => .both

/-- Information join (gullibility): `a ⊕ b` accumulates evidence from both sources.
Cross-source conflict: `is ⊕ not = both` (record the inconsistency).
**This is the only operation that produces `both` from K3 inputs.** -/
def infoJoin : Truth4 → Truth4 → Truth4
  | .both, _     => .both
  | _,     .both => .both
  | .can,  y     => y
  | x,     .can  => x
  | .is,   .is   => .is
  | .not,  .not  => .not
  | .is,   .not  => .both  -- conflict accumulates
  | .not,  .is   => .both

/-- Negation distributes over truth meet (de Morgan). -/
theorem neg_truthMeet (a b : Truth4) : neg (truthMeet a b) = truthJoin (neg a) (neg b) := by
  cases a <;> cases b <;> rfl

/-- Negation distributes over truth join (de Morgan). -/
theorem neg_truthJoin (a b : Truth4) : neg (truthJoin a b) = truthMeet (neg a) (neg b) := by
  cases a <;> cases b <;> rfl

/-- Negation fixes information meet — both `is` and `not` map to themselves under ⊗. -/
theorem neg_infoMeet (a b : Truth4) : neg (infoMeet a b) = infoMeet (neg a) (neg b) := by
  cases a <;> cases b <;> rfl

/-- Negation fixes information join. -/
theorem neg_infoJoin (a b : Truth4) : neg (infoJoin a b) = infoJoin (neg a) (neg b) := by
  cases a <;> cases b <;> rfl

/-! ## Bilattice laws — sanity checks

These verify that the operations form a genuine bilattice (Fitting 1991):
each ordering's meet/join are commutative, associative, idempotent, and absorb
correctly. Proofs are by case-exhaustive `decide` over the 4×4 / 4×4×4 cases. -/

theorem truthMeet_comm (a b : Truth4) : truthMeet a b = truthMeet b a := by
  cases a <;> cases b <;> rfl

theorem truthMeet_assoc (a b c : Truth4) :
    truthMeet (truthMeet a b) c = truthMeet a (truthMeet b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem truthMeet_idem (a : Truth4) : truthMeet a a = a := by
  cases a <;> rfl

theorem truthJoin_comm (a b : Truth4) : truthJoin a b = truthJoin b a := by
  cases a <;> cases b <;> rfl

theorem truthJoin_assoc (a b c : Truth4) :
    truthJoin (truthJoin a b) c = truthJoin a (truthJoin b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem truthJoin_idem (a : Truth4) : truthJoin a a = a := by
  cases a <;> rfl

theorem infoMeet_comm (a b : Truth4) : infoMeet a b = infoMeet b a := by
  cases a <;> cases b <;> rfl

theorem infoMeet_assoc (a b c : Truth4) :
    infoMeet (infoMeet a b) c = infoMeet a (infoMeet b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem infoMeet_idem (a : Truth4) : infoMeet a a = a := by
  cases a <;> rfl

theorem infoJoin_comm (a b : Truth4) : infoJoin a b = infoJoin b a := by
  cases a <;> cases b <;> rfl

theorem infoJoin_assoc (a b c : Truth4) :
    infoJoin (infoJoin a b) c = infoJoin a (infoJoin b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem infoJoin_idem (a : Truth4) : infoJoin a a = a := by
  cases a <;> rfl

/-- Truth meet and join absorb: `a ∧_t (a ∨_t b) = a`. -/
theorem truthMeet_absorbs_join (a b : Truth4) : truthMeet a (truthJoin a b) = a := by
  cases a <;> cases b <;> rfl

/-- Truth join absorbs truth meet symmetrically. -/
theorem truthJoin_absorbs_meet (a b : Truth4) : truthJoin a (truthMeet a b) = a := by
  cases a <;> cases b <;> rfl

/-- Information meet absorbs information join. -/
theorem infoMeet_absorbs_join (a b : Truth4) : infoMeet a (infoJoin a b) = a := by
  cases a <;> cases b <;> rfl

/-- Information join absorbs information meet. -/
theorem infoJoin_absorbs_meet (a b : Truth4) : infoJoin a (infoMeet a b) = a := by
  cases a <;> cases b <;> rfl

/-! ## Connection to the truth/info orderings

Each operation computes the appropriate bound. These theorems pin down the
correctness of the truth-table definitions: `truthMeet` really is the truth-glb,
not just a function with the right name. -/

/-- `truthMeet` is the truth-greatest-lower-bound: `truthMeet a b ≤_t a` and `≤_t b`,
and any `c` with `c ≤_t a` and `c ≤_t b` satisfies `c ≤_t truthMeet a b`. -/
theorem truthMeet_isGLB (a b : Truth4) :
    truthLe (truthMeet a b) a ∧ truthLe (truthMeet a b) b ∧
    ∀ c, truthLe c a → truthLe c b → truthLe c (truthMeet a b) := by
  refine ⟨?_, ?_, ?_⟩
  · cases a <;> cases b <;> simp [truthMeet, truthLe]
  · cases a <;> cases b <;> simp [truthMeet, truthLe]
  · intro c hca hcb
    cases a <;> cases b <;> cases c <;> simp_all [truthMeet, truthLe]

/-- `truthJoin` is the truth-least-upper-bound. -/
theorem truthJoin_isLUB (a b : Truth4) :
    truthLe a (truthJoin a b) ∧ truthLe b (truthJoin a b) ∧
    ∀ c, truthLe a c → truthLe b c → truthLe (truthJoin a b) c := by
  refine ⟨?_, ?_, ?_⟩
  · cases a <;> cases b <;> simp [truthJoin, truthLe]
  · cases a <;> cases b <;> simp [truthJoin, truthLe]
  · intro c hac hbc
    cases a <;> cases b <;> cases c <;> simp_all [truthJoin, truthLe]

/-- `infoMeet` is the information-greatest-lower-bound. -/
theorem infoMeet_isGLB (a b : Truth4) :
    infoLe (infoMeet a b) a ∧ infoLe (infoMeet a b) b ∧
    ∀ c, infoLe c a → infoLe c b → infoLe c (infoMeet a b) := by
  refine ⟨?_, ?_, ?_⟩
  · cases a <;> cases b <;> simp [infoMeet, infoLe]
  · cases a <;> cases b <;> simp [infoMeet, infoLe]
  · intro c hca hcb
    cases a <;> cases b <;> cases c <;> simp_all [infoMeet, infoLe]

/-- `infoJoin` is the information-least-upper-bound. -/
theorem infoJoin_isLUB (a b : Truth4) :
    infoLe a (infoJoin a b) ∧ infoLe b (infoJoin a b) ∧
    ∀ c, infoLe a c → infoLe b c → infoLe (infoJoin a b) c := by
  refine ⟨?_, ?_, ?_⟩
  · cases a <;> cases b <;> simp [infoJoin, infoLe]
  · cases a <;> cases b <;> simp [infoJoin, infoLe]
  · intro c hac hbc
    cases a <;> cases b <;> cases c <;> simp_all [infoJoin, infoLe]

end Truth4
