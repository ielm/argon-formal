/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.Foundation.Truth4

/-!
# Lattice Contexts — K3, FDE, Boolean

Defines the three named lattice contexts as predicates over `Truth4` values,
proves the K3 fragment is closed under the four "K3 operations" (truth meet,
truth join, negation, information meet), and establishes the
`MetaValue ↔ K3-fragment-of-Truth4` isomorphism.

## Why this matters

Argon's truth-value semantics is parametric in a *lattice context* — a constraint
on which `Truth4` values a typed expression may carry. Three named contexts:

- **Boolean** — only fully-determined values (`is` or `not`). Used by CWA-mode
  modules. Statically eliminable `can` via Horn restriction.
- **K3** — consistent values (no `both`). The natural setting under OWA when
  every assertion comes from a single source. Default for refinement membership.
- **FDE** — all `Truth4` values, including `both`. Used by cross-source aggregation
  (federated standpoint queries).

The key theorems below establish that **K3 is closed under the operations a K3
context can use** (truth meet/join, negation, information meet — the consensus
operator). K3 is NOT closed under information join (the gullibility operator that
accumulates conflicting evidence) — that's exactly the operation that escapes
K3 into FDE, and it's the one users opt into when they ask for federated queries.

## Connection to existing infrastructure

The existing `MetaValue` (IS/CAN/NOT) is exactly the K3 fragment of `Truth4`.
This file proves the bidirectional isomorphism `MetaValue ≃ {v : Truth4 // v.inK3}`.
Once established, every existing `MetaValue` theorem can be lifted to its `Truth4`
counterpart by going through the isomorphism, and every new `Truth4` theorem on
the K3 fragment specializes to a `MetaValue` theorem.

## What is NOT in this file

The closure theorems are proved here. The *projection morphisms* (FDE → K3 with
explicit policy parameters) live in `Projection.lean`. The fact that the existing
flow-typing soundness lifts to the K3 fragment of Truth4 lives in
`BackwardCompat.lean`.
-/

namespace Truth4

/-! ## Lattice context predicates -/

/-- A `Truth4` value is in the **K3** fragment iff it is consistent (no `both`).
This recovers exactly the existing `MetaValue` value space. -/
@[reducible] def inK3 (v : Truth4) : Prop := v.isConsistent

/-- A `Truth4` value is in the **Boolean** fragment iff it is fully determined
(`is` or `not`). This is the CWA value space — `can` is eliminated by closure. -/
@[reducible] def inBool (v : Truth4) : Prop := v.isDetermined

/-- A `Truth4` value is in the **FDE** fragment iff it is any `Truth4` value.
The unconstrained context. -/
@[reducible] def inFDE (_ : Truth4) : Prop := True

/-- Boolean ⊆ K3: every determined value is consistent. -/
theorem inBool_imp_inK3 {v : Truth4} (h : v.inBool) : v.inK3 := by
  cases v <;> simp_all [inBool, isDetermined, inK3, isConsistent]

/-- K3 ⊆ FDE: trivially. -/
theorem inK3_imp_inFDE {v : Truth4} (_ : v.inK3) : v.inFDE := trivial

/-! ## K3 closure theorems

The four K3 operations — truth meet `∧_t`, truth join `∨_t`, negation `¬`,
and information meet `⊗` — never produce `both` from K3 inputs. This is the
"K3 is closed under K3 operations" result. -/

/-- Truth meet preserves K3: consistent inputs produce a consistent output. -/
theorem truthMeet_inK3 {a b : Truth4} (ha : a.inK3) (hb : b.inK3) :
    (truthMeet a b).inK3 := by
  cases a <;> cases b <;> simp_all [inK3, isConsistent, truthMeet]

/-- Truth join preserves K3. -/
theorem truthJoin_inK3 {a b : Truth4} (ha : a.inK3) (hb : b.inK3) :
    (truthJoin a b).inK3 := by
  cases a <;> cases b <;> simp_all [inK3, isConsistent, truthJoin]

/-- Negation preserves K3. -/
theorem neg_inK3 {a : Truth4} (ha : a.inK3) : (neg a).inK3 := by
  cases a <;> simp_all [inK3, isConsistent, neg]

/-- Information meet (consensus) preserves K3. -/
theorem infoMeet_inK3 {a b : Truth4} (ha : a.inK3) (hb : b.inK3) :
    (infoMeet a b).inK3 := by
  cases a <;> cases b <;> simp_all [inK3, isConsistent, infoMeet]

/-- **Information join (gullibility) does NOT preserve K3.** Witness: `is ⊕ not = both`,
which escapes the K3 fragment. This is the operation that produces the inconsistent
value from cross-source disagreement; it is the *only* path from K3 into the
genuinely-FDE region of Truth4. -/
theorem infoJoin_escapes_K3 :
    Truth4.is.inK3 ∧ Truth4.not.inK3 ∧ ¬ (infoJoin .is .not).inK3 := by
  refine ⟨trivial, trivial, ?_⟩
  simp [infoJoin, inK3, isConsistent]

/-- **Sharper form**: `infoJoin a b ∈ K3` iff `a` and `b` agree on truthiness
(both `is`, both `not`, or at least one is `can`). This characterizes exactly
the cases where federation across sources stays in K3. -/
theorem infoJoin_inK3_iff {a b : Truth4} (ha : a.inK3) (hb : b.inK3) :
    (infoJoin a b).inK3 ↔
    (a = .can ∨ b = .can ∨ a = b) := by
  cases a <;> cases b <;> simp_all [inK3, isConsistent, infoJoin]

/-! ## Boolean closure theorems

The Boolean fragment is closed under negation (it's already a sub-Boolean-algebra)
but NOT under truth meet/join when `can` could leak in — except: as long as both
inputs are Boolean (no `can`), the result is Boolean. -/

/-- Truth meet preserves Boolean. -/
theorem truthMeet_inBool {a b : Truth4} (ha : a.inBool) (hb : b.inBool) :
    (truthMeet a b).inBool := by
  cases a <;> cases b <;> simp_all [inBool, isDetermined, truthMeet]

/-- Truth join preserves Boolean. -/
theorem truthJoin_inBool {a b : Truth4} (ha : a.inBool) (hb : b.inBool) :
    (truthJoin a b).inBool := by
  cases a <;> cases b <;> simp_all [inBool, isDetermined, truthJoin]

/-- Negation preserves Boolean. -/
theorem neg_inBool {a : Truth4} (ha : a.inBool) : (neg a).inBool := by
  cases a <;> simp_all [inBool, isDetermined, neg]

/-! ## MetaValue ↔ K3 isomorphism

Connect the existing `MetaValue` (three-valued K3) to the K3 fragment of `Truth4`.
This lets every existing theorem about `MetaValue` lift to a theorem about
the K3 fragment, and vice versa. -/

/-- Embed an existing `MetaValue` into `Truth4`. The image lies in the K3 fragment. -/
def ofMetaValue : MetaValue → Truth4
  | .is  => .is
  | .not => .not
  | .can => .can

/-- The embedding image is in K3. -/
theorem ofMetaValue_inK3 (m : MetaValue) : (ofMetaValue m).inK3 := by
  cases m <;> simp [ofMetaValue, inK3, isConsistent]

/-- The embedding image is never `both`. -/
theorem ofMetaValue_ne_both (m : MetaValue) : ofMetaValue m ≠ .both := by
  cases m <;> simp [ofMetaValue]

/-- Project a `Truth4` value in the K3 fragment back to `MetaValue`. -/
def toMetaValue : (v : Truth4) → v.inK3 → MetaValue
  | .is,  _ => .is
  | .not, _ => .not
  | .can, _ => .can
  | .both, h => absurd h (by simp [inK3, isConsistent])

/-- Embedding then projecting is the identity. -/
theorem toMetaValue_ofMetaValue (m : MetaValue) :
    toMetaValue (ofMetaValue m) (ofMetaValue_inK3 m) = m := by
  cases m <;> rfl

/-- Projecting then embedding is the identity (on K3 inputs). -/
theorem ofMetaValue_toMetaValue (v : Truth4) (h : v.inK3) :
    ofMetaValue (toMetaValue v h) = v := by
  cases v with
  | is   => rfl
  | not  => rfl
  | can  => rfl
  | both => exact absurd h (by simp [inK3, isConsistent])

/-- Embedding preserves the information ordering: `MetaValue.le m₁ m₂ ↔ Truth4.infoLe (ofMetaValue m₁) (ofMetaValue m₂)`.

This is the load-bearing isomorphism: the existing K3 information ordering on
`MetaValue` is exactly the restriction of `Truth4.infoLe` to the K3 fragment. -/
theorem ofMetaValue_infoLe_iff (m₁ m₂ : MetaValue) :
    infoLe (ofMetaValue m₁) (ofMetaValue m₂) ↔ m₁ ≤ m₂ := by
  -- Finite case analysis: 9 pairs over `MetaValue × MetaValue`. The K3 fragment of
  -- `Truth4` has the same partial order as `MetaValue` by construction. Each case
  -- either reduces to a True ↔ True or proves a negative case by exhausting the
  -- `MetaValue.PartialOrder.le` definition (`a ≤ b` iff `a = .can ∨ a = b`).
  cases m₁ <;> cases m₂ <;> first
    | (refine ⟨fun _ => ?_, fun _ => trivial⟩; first | rfl | exact MetaValue.can_le _)
    | (refine ⟨?_, ?_⟩ <;> (intro h; first | exact h.elim | (cases h <;> simp_all)))

/-! ## Algebraic correspondence

The K3 operations on `Truth4` agree with whatever existing operations on `MetaValue`
exist (the existing project doesn't define ∧/∨/¬ on `MetaValue` directly, but the
information ordering is the same). The negation operation on the K3 fragment
swaps IS/NOT and fixes CAN — what an existing extension would do. -/

/-- The truth-meet of two K3 values (via the embedding) is itself K3. -/
theorem ofMetaValue_truthMeet_inK3 (m₁ m₂ : MetaValue) :
    (truthMeet (ofMetaValue m₁) (ofMetaValue m₂)).inK3 :=
  truthMeet_inK3 (ofMetaValue_inK3 m₁) (ofMetaValue_inK3 m₂)

/-- Likewise for truth join. -/
theorem ofMetaValue_truthJoin_inK3 (m₁ m₂ : MetaValue) :
    (truthJoin (ofMetaValue m₁) (ofMetaValue m₂)).inK3 :=
  truthJoin_inK3 (ofMetaValue_inK3 m₁) (ofMetaValue_inK3 m₂)

/-- Likewise for information meet (consensus). -/
theorem ofMetaValue_infoMeet_inK3 (m₁ m₂ : MetaValue) :
    (infoMeet (ofMetaValue m₁) (ofMetaValue m₂)).inK3 :=
  infoMeet_inK3 (ofMetaValue_inK3 m₁) (ofMetaValue_inK3 m₂)

/-- Likewise for negation. -/
theorem ofMetaValue_neg_inK3 (m : MetaValue) : (neg (ofMetaValue m)).inK3 :=
  neg_inK3 (ofMetaValue_inK3 m)

end Truth4
