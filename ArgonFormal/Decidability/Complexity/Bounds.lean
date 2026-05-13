/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import ArgonFormal.Decidability.Domain1.Decidability
import ArgonFormal.Decidability.Domain2.Decidability
import ArgonFormal.Decidability.CrossDomain.Decidability

/-!
# Theorem 4: Complexity Bounds

Complexity classification for each sub-fragment and the full combination.

| Fragment        | Complexity  | Justification                              |
|-----------------|-------------|--------------------------------------------|
| Domain 1 only   | PTime       | Finite model checking (proved below)       |
| QF-LIA only     | NP          | Presburger arithmetic (axiom)              |
| GNFO only       | 2-EXPTIME   | Bárány et al. 2015 (axiom)                 |
| Domain 1 + LIA  | NP          | Domain 1 is PTime; QF-LIA dominates        |
| Domain 1 + GNFO | 2-EXPTIME   | GNFO dominates                             |
| Full fragment    | 2-EXPTIME   | GNFO component dominates                  |

## Main results

- `d1QuantifierDepth` — quantifier depth of a D1 predicate
- `d1EvalBound` — Domain 1 evaluation cost is O(|C|^k) for depth k
-/

/-- Quantifier depth of a Domain 1 predicate.

This determines the polynomial degree of the evaluation cost:
each quantifier layer multiplies the work by `|C|`. -/
def d1QuantifierDepth {C A : Type} : D1Pred C A → Nat
  | .metaEq _ _ _  => 0
  | .isDet _ _     => 0
  | .hasAnc _ sub  => d1QuantifierDepth sub + 1   -- existential over ancestors
  | .hasDesc _ sub => d1QuantifierDepth sub + 1   -- existential over descendants
  | .countGeq sub _ => d1QuantifierDepth sub + 1  -- iterates over all concepts
  | .forallC sub   => d1QuantifierDepth sub + 1   -- universal over concepts
  | .existsC sub   => d1QuantifierDepth sub + 1   -- existential over concepts
  | .andP p q      => max (d1QuantifierDepth p) (d1QuantifierDepth q)
  | .orP p q       => max (d1QuantifierDepth p) (d1QuantifierDepth q)
  | .notP p        => d1QuantifierDepth p
  | .tt            => 0
  | .ff            => 0

/-- AST size of a Domain 1 predicate (number of nodes). This is the
predicate-dependent constant factor in the PTime bound. -/
def d1Size {C A : Type} : D1Pred C A → Nat
  | .metaEq _ _ _  => 1
  | .isDet _ _     => 1
  | .hasAnc _ sub  => 1 + d1Size sub
  | .hasDesc _ sub => 1 + d1Size sub
  | .countGeq sub _ => 1 + d1Size sub
  | .forallC sub   => 1 + d1Size sub
  | .existsC sub   => 1 + d1Size sub
  | .andP p q      => 1 + d1Size p + d1Size q
  | .orP p q       => 1 + d1Size p + d1Size q
  | .notP p        => 1 + d1Size p
  | .tt            => 1
  | .ff            => 1

/-- Number of atomic evaluations required to decide a Domain 1 predicate
`φ` against a type graph whose concept universe has cardinality `n`.

Cost model (one operation per AST node visit; quantifiers iterate over
the full concept universe):

| Constructor          | Cost |
|----------------------|------|
| `metaEq c' a v`       | 1 (one cell lookup) |
| `isDet c' a`          | 1 (one cell lookup) |
| `tt` / `ff`           | 1 |
| `hasAnc _ sub`        | `n * cost(sub)` (iterate ancestors) |
| `hasDesc _ sub`       | `n * cost(sub)` (iterate descendants) |
| `countGeq sub _`      | `n * cost(sub)` (iterate over concepts) |
| `forallC sub`         | `n * cost(sub)` |
| `existsC sub`         | `n * cost(sub)` |
| `andP p q` / `orP p q`| `cost(p) + cost(q)` |
| `notP p`              | `cost(p)` |

This is an upper bound on real evaluation: the implementation may
short-circuit (`existsC` returns on first hit, `hasAnc` may stop early
via memoized transitive closure), but those optimizations only
decrease cost. -/
def d1EvalCost {C A : Type} (n : Nat) : D1Pred C A → Nat
  | .metaEq _ _ _  => 1
  | .isDet _ _     => 1
  | .hasAnc _ sub  => n * d1EvalCost n sub
  | .hasDesc _ sub => n * d1EvalCost n sub
  | .countGeq sub _ => n * d1EvalCost n sub
  | .forallC sub   => n * d1EvalCost n sub
  | .existsC sub   => n * d1EvalCost n sub
  | .andP p q      => d1EvalCost n p + d1EvalCost n q
  | .orP p q       => d1EvalCost n p + d1EvalCost n q
  | .notP p        => d1EvalCost n p
  | .tt            => 1
  | .ff            => 1

/-- **Theorem 4a: Domain 1 PTime Bound.**

The cost of evaluating a Domain 1 predicate `φ` against a type graph
whose concept universe has cardinality `n` is bounded by
`d1Size φ * (n + 1)^(d1QuantifierDepth φ)`.

The `n + 1` base avoids the `n = 0` (empty universe) edge case: when
`C` is empty, quantifiers have cost 0 anyway, but the inequality
`d1EvalCost ≤ d1Size * 0^depth` is false at boundary cases (e.g.,
`0^0 = 1` while the depth-0 cost is also 1).

**Polynomial in `n` for fixed `φ`:** for a given predicate, `d1Size φ`
and `d1QuantifierDepth φ` are constants; the RHS is a polynomial in `n`
of degree `d1QuantifierDepth φ` (after the `n + 1` substitution).
Hence Domain 1 predicate evaluation is in PTime for fixed predicate
structure — the data complexity is polynomial.

**Proof:** structural induction on `φ`. At each quantifier node, the
inductive hypothesis is multiplied by `n` (the iteration); the `(n+1)`
base absorbs this. At each Boolean connective, the depth is the max of
the children's depths; we lift each child's bound to that max via
`Nat.pow_le_pow_right` (which requires base ≥ 1, satisfied by `n+1`). -/
theorem d1EvalCost_le {C A : Type} (n : Nat) (φ : D1Pred C A) :
    d1EvalCost n φ ≤ d1Size φ * (n + 1)^(d1QuantifierDepth φ) := by
  induction φ with
  | metaEq _ _ _ => simp [d1EvalCost, d1Size, d1QuantifierDepth]
  | isDet _ _ => simp [d1EvalCost, d1Size, d1QuantifierDepth]
  | tt => simp [d1EvalCost, d1Size, d1QuantifierDepth]
  | ff => simp [d1EvalCost, d1Size, d1QuantifierDepth]
  | hasAnc _ sub ih =>
    simp only [d1EvalCost, d1Size, d1QuantifierDepth]
    calc n * d1EvalCost n sub
        ≤ n * (d1Size sub * (n + 1) ^ d1QuantifierDepth sub) :=
          Nat.mul_le_mul_left n ih
      _ ≤ (n + 1) * (d1Size sub * (n + 1) ^ d1QuantifierDepth sub) :=
          Nat.mul_le_mul_right _ (Nat.le_succ n)
      _ = d1Size sub * ((n + 1) * (n + 1) ^ d1QuantifierDepth sub) := by ring
      _ = d1Size sub * (n + 1) ^ (d1QuantifierDepth sub + 1) := by
          rw [Nat.pow_succ]; ring
      _ ≤ (1 + d1Size sub) * (n + 1) ^ (d1QuantifierDepth sub + 1) :=
          Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  | hasDesc _ sub ih =>
    simp only [d1EvalCost, d1Size, d1QuantifierDepth]
    calc n * d1EvalCost n sub
        ≤ n * (d1Size sub * (n + 1) ^ d1QuantifierDepth sub) :=
          Nat.mul_le_mul_left n ih
      _ ≤ (n + 1) * (d1Size sub * (n + 1) ^ d1QuantifierDepth sub) :=
          Nat.mul_le_mul_right _ (Nat.le_succ n)
      _ = d1Size sub * ((n + 1) * (n + 1) ^ d1QuantifierDepth sub) := by ring
      _ = d1Size sub * (n + 1) ^ (d1QuantifierDepth sub + 1) := by
          rw [Nat.pow_succ]; ring
      _ ≤ (1 + d1Size sub) * (n + 1) ^ (d1QuantifierDepth sub + 1) :=
          Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  | countGeq sub _ ih =>
    simp only [d1EvalCost, d1Size, d1QuantifierDepth]
    calc n * d1EvalCost n sub
        ≤ n * (d1Size sub * (n + 1) ^ d1QuantifierDepth sub) :=
          Nat.mul_le_mul_left n ih
      _ ≤ (n + 1) * (d1Size sub * (n + 1) ^ d1QuantifierDepth sub) :=
          Nat.mul_le_mul_right _ (Nat.le_succ n)
      _ = d1Size sub * ((n + 1) * (n + 1) ^ d1QuantifierDepth sub) := by ring
      _ = d1Size sub * (n + 1) ^ (d1QuantifierDepth sub + 1) := by
          rw [Nat.pow_succ]; ring
      _ ≤ (1 + d1Size sub) * (n + 1) ^ (d1QuantifierDepth sub + 1) :=
          Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  | forallC sub ih =>
    simp only [d1EvalCost, d1Size, d1QuantifierDepth]
    calc n * d1EvalCost n sub
        ≤ n * (d1Size sub * (n + 1) ^ d1QuantifierDepth sub) :=
          Nat.mul_le_mul_left n ih
      _ ≤ (n + 1) * (d1Size sub * (n + 1) ^ d1QuantifierDepth sub) :=
          Nat.mul_le_mul_right _ (Nat.le_succ n)
      _ = d1Size sub * ((n + 1) * (n + 1) ^ d1QuantifierDepth sub) := by ring
      _ = d1Size sub * (n + 1) ^ (d1QuantifierDepth sub + 1) := by
          rw [Nat.pow_succ]; ring
      _ ≤ (1 + d1Size sub) * (n + 1) ^ (d1QuantifierDepth sub + 1) :=
          Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  | existsC sub ih =>
    simp only [d1EvalCost, d1Size, d1QuantifierDepth]
    calc n * d1EvalCost n sub
        ≤ n * (d1Size sub * (n + 1) ^ d1QuantifierDepth sub) :=
          Nat.mul_le_mul_left n ih
      _ ≤ (n + 1) * (d1Size sub * (n + 1) ^ d1QuantifierDepth sub) :=
          Nat.mul_le_mul_right _ (Nat.le_succ n)
      _ = d1Size sub * ((n + 1) * (n + 1) ^ d1QuantifierDepth sub) := by ring
      _ = d1Size sub * (n + 1) ^ (d1QuantifierDepth sub + 1) := by
          rw [Nat.pow_succ]; ring
      _ ≤ (1 + d1Size sub) * (n + 1) ^ (d1QuantifierDepth sub + 1) :=
          Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  | andP p q ih_p ih_q =>
    simp only [d1EvalCost, d1Size, d1QuantifierDepth]
    have h_base : 1 ≤ n + 1 := Nat.le_add_left _ _
    have h_p_lifted :
        d1EvalCost n p ≤ d1Size p * (n + 1) ^ max (d1QuantifierDepth p)
          (d1QuantifierDepth q) := by
      refine le_trans ih_p (Nat.mul_le_mul_left _ ?_)
      exact Nat.pow_le_pow_right h_base (le_max_left _ _)
    have h_q_lifted :
        d1EvalCost n q ≤ d1Size q * (n + 1) ^ max (d1QuantifierDepth p)
          (d1QuantifierDepth q) := by
      refine le_trans ih_q (Nat.mul_le_mul_left _ ?_)
      exact Nat.pow_le_pow_right h_base (le_max_right _ _)
    calc d1EvalCost n p + d1EvalCost n q
        ≤ d1Size p * (n + 1) ^ max (d1QuantifierDepth p) (d1QuantifierDepth q) +
          d1Size q * (n + 1) ^ max (d1QuantifierDepth p) (d1QuantifierDepth q) :=
          Nat.add_le_add h_p_lifted h_q_lifted
      _ = (d1Size p + d1Size q) *
            (n + 1) ^ max (d1QuantifierDepth p) (d1QuantifierDepth q) := by ring
      _ ≤ (1 + d1Size p + d1Size q) *
            (n + 1) ^ max (d1QuantifierDepth p) (d1QuantifierDepth q) := by
          apply Nat.mul_le_mul_right; omega
  | orP p q ih_p ih_q =>
    simp only [d1EvalCost, d1Size, d1QuantifierDepth]
    have h_base : 1 ≤ n + 1 := Nat.le_add_left _ _
    have h_p_lifted :
        d1EvalCost n p ≤ d1Size p * (n + 1) ^ max (d1QuantifierDepth p)
          (d1QuantifierDepth q) := by
      refine le_trans ih_p (Nat.mul_le_mul_left _ ?_)
      exact Nat.pow_le_pow_right h_base (le_max_left _ _)
    have h_q_lifted :
        d1EvalCost n q ≤ d1Size q * (n + 1) ^ max (d1QuantifierDepth p)
          (d1QuantifierDepth q) := by
      refine le_trans ih_q (Nat.mul_le_mul_left _ ?_)
      exact Nat.pow_le_pow_right h_base (le_max_right _ _)
    calc d1EvalCost n p + d1EvalCost n q
        ≤ d1Size p * (n + 1) ^ max (d1QuantifierDepth p) (d1QuantifierDepth q) +
          d1Size q * (n + 1) ^ max (d1QuantifierDepth p) (d1QuantifierDepth q) :=
          Nat.add_le_add h_p_lifted h_q_lifted
      _ = (d1Size p + d1Size q) *
            (n + 1) ^ max (d1QuantifierDepth p) (d1QuantifierDepth q) := by ring
      _ ≤ (1 + d1Size p + d1Size q) *
            (n + 1) ^ max (d1QuantifierDepth p) (d1QuantifierDepth q) := by
          apply Nat.mul_le_mul_right; omega
  | notP p ih_p =>
    simp only [d1EvalCost, d1Size, d1QuantifierDepth]
    exact le_trans ih_p (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))

/-- **Corollary: Domain 1 is in PTime for fixed predicates.**

For a fixed Domain 1 predicate `φ`, evaluation cost is polynomial in the
size of the concept universe: `O((n+1)^k)` with `k = d1QuantifierDepth φ`,
multiplied by the predicate-dependent constant `d1Size φ`.

Specialized to a typegraph with concept universe `C`: the cost is
bounded by `d1Size φ * (Fintype.card C + 1)^(d1QuantifierDepth φ)`,
which is polynomial in `Fintype.card C` for fixed `φ`. -/
theorem d1EvalBound {C A : Type} [Fintype C] [DecidableEq C]
    [Fintype A] [DecidableEq A]
    (_G : TypeGraph C A) (φ : D1Pred C A) :
    d1EvalCost (Fintype.card C) φ ≤
      d1Size φ * (Fintype.card C + 1) ^ d1QuantifierDepth φ :=
  d1EvalCost_le (Fintype.card C) φ

/-! ## Theorem 4 (cont.): polynomial bound for fixed predicates

The textbook "Domain 1 is in PTime" claim, in concrete form: for any
fixed predicate, evaluation cost is bounded by some polynomial in `n`.
This follows from `d1EvalCost_le` by reading off coefficient and degree. -/

/-- **Domain 1 polynomial bound.** For any fixed Domain 1 predicate `φ`,
there exist a coefficient and a degree such that the evaluation cost is
bounded by `coeff * (n + 1) ^ deg` for every concept-universe size `n`.

The witness coefficient is `d1Size φ` and the witness degree is
`d1QuantifierDepth φ` — both fixed once `φ` is fixed. -/
theorem d1_polynomial_bound {C A : Type} (φ : D1Pred C A) :
    ∃ coeff deg : Nat, ∀ n : Nat, d1EvalCost n φ ≤ coeff * (n + 1) ^ deg :=
  ⟨d1Size φ, d1QuantifierDepth φ, fun n => d1EvalCost_le n φ⟩

/-! ## Theorem 4 (full fragment): decidability

The "full fragment complexity" claim consists of two parts:

1. **Decidability:** every mixed predicate is decidable. This is proved
   in `Decidability/CrossDomain/Decidability.lean` as `mixedDecidable`,
   reducing mixed evaluation to the staged form (Domain 1 atoms first,
   then Domain 2 atoms over the resulting constants).

2. **Complexity-class assignment** (QF-LIA = NP, GNFO = 2-EXPTIME, full
   fragment = 2-EXPTIME via dominance): this is *external*, cited from
   primary sources (Ginsburg-Spanier 1966 for QF-LIA; Bárány-ten Cate-
   Segoufin 2015 for GNFO). A Lean expression of these classifications
   would require a Turing-machine formalization of the cost model for
   `d2Sat` — which is opaque by design (the satisfaction relation is
   axiomatic). The mechanical content we *can* state is the
   decidability witness in `Decidability/Domain2/Theories.lean`
   (`d2CombinedDecidable`). The complexity assignment lives in those
   cited papers and is preserved in our published proof obligations.

We therefore expose `fullFragmentDecidable` as the mechanically-proved
component of "full fragment complexity" and document the externality
of the rest. -/

/-- **Theorem 4 (full fragment decidable).** Every mixed predicate is
decidable, given the external decidability witnesses for the Domain 2
fragments. A direct restatement of `mixedDecidable` as a `Decidable`
instance constructor. -/
noncomputable def fullFragmentDecidable {C A : Type} [Fintype C] [DecidableEq C]
    [Fintype A] [DecidableEq A]
    (G : TypeGraph C A) (c : C) (φ : MixedPred C A) :
    Decidable (mixedEval G c φ) :=
  mixedDecidable G c φ

/-- **Theorem 4 (full fragment decidable, Prop form).** The proposition
"the mixed-predicate evaluation `mixedEval G c φ` is decidable" holds —
extracting the existence of a decision procedure as a `Prop` so it can
be referenced in places where `Decidable` (a `Type`) is not directly
usable. -/
theorem fullFragmentDecidable_prop {C A : Type} [Fintype C] [DecidableEq C]
    [Fintype A] [DecidableEq A]
    (G : TypeGraph C A) (c : C) (φ : MixedPred C A) :
    Nonempty (Decidable (mixedEval G c φ)) :=
  ⟨mixedDecidable G c φ⟩
