/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.Reasoning.Fixpoint

/-!
# Theorem 4: Package Composition Preserves Convergence

## Statement

If package P1 defines rules over axes A1 (with acyclic dependency graph G1) and
package P2 defines rules over axes A2 (with acyclic dependency graph G2), and the
combined dependency graph G1 ∪ G2 is acyclic, then:

1. The combined stratified fixpoint converges.
2. The result is consistent with running P1 alone and P2 alone:
   for axes in A1 \ A2, the result matches P1-only; for axes in A2 \ A1, matches P2-only.

## Proof Strategy

**Case 1: Disjoint axes (A1 ∩ A2 = ∅).**
P1's rules only read/write A1 axes. P2's rules only read/write A2 axes.
Their effects are completely independent — they commute trivially.
The combined fixpoint = P1 fixpoint on A1 axes + P2 fixpoint on A2 axes.

**Case 2: Shared axes (A1 ∩ A2 ≠ ∅).**
Both packages contribute rules to the same axis. The combined rules for that axis
are the union of P1's and P2's rules. For convergence, we need the combined rules
to still be monotone (Cat1) or stratum-respecting (Cat2). This holds if:
- Cat1 rules from both packages are individually monotone (monotonicity composes)
- Cat2 rules from both packages reference the same completed Cat1 state
- The combined dependency graph is acyclic (given as hypothesis)

For UNIQUENESS on shared axes, we additionally need confluence: the rules from P1
and P2 don't produce contradictory results. This is an additional hypothesis
(the RTT-style confluence check that the compiler performs at package resolution).
-/

variable {C A : Type} [DecidableEq C] [DecidableEq A] [Fintype C] [Fintype A]

/-- A package defines rules over a subset of axes. -/
structure Package (C A : Type) [DecidableEq C] [DecidableEq A] [Fintype C] [Fintype A] where
  /-- The axes this package defines rules for. -/
  axes : Finset A
  /-- Category 1 rules per axis. -/
  cat1 : A → List (MonotoneRule C A)
  /-- Category 2 rules per axis. -/
  cat2 : A → List (NafRule C A)
  /-- Rules are only defined for package axes. -/
  cat1_scope : ∀ a, a ∉ axes → cat1 a = []
  cat2_scope : ∀ a, a ∉ axes → cat2 a = []

/-- Combine two packages into one. -/
def Package.combine (p1 p2 : Package C A) : Package C A where
  axes := p1.axes ∪ p2.axes
  cat1 a := p1.cat1 a ++ p2.cat1 a
  cat2 a := p1.cat2 a ++ p2.cat2 a
  cat1_scope a ha := by
    simp only [Finset.mem_union, not_or] at ha
    rw [p1.cat1_scope a ha.1, p2.cat1_scope a ha.2]
    rfl
  cat2_scope a ha := by
    simp only [Finset.mem_union, not_or] at ha
    rw [p1.cat2_scope a ha.1, p2.cat2_scope a ha.2]
    rfl

/-! ## Theorem 4: Package composition

The three theorems below characterize how `Package.combine` behaves at
the rule-list level. All downstream fixpoint properties of the combined
package follow from the corresponding `StratifiedRuleSet` theorems
(Theorems 1.1–1.3, 5) once the combined package is paired with a
stratification — i.e. these are the *purely structural* composition
results, separating the package-algebra layer from the stratification
layer. -/

/-- **Theorem 4.1: Combined rule lists.**
The Category 1 and Category 2 rule lists of `p1.combine p2` are
respectively the concatenations `p1.cat1 a ++ p2.cat1 a` and
`p1.cat2 a ++ p2.cat2 a`. -/
theorem combine_cat1 (p1 p2 : Package C A) (a : A) :
    (p1.combine p2).cat1 a = p1.cat1 a ++ p2.cat1 a := rfl

theorem combine_cat2 (p1 p2 : Package C A) (a : A) :
    (p1.combine p2).cat2 a = p1.cat2 a ++ p2.cat2 a := rfl

/-- **Theorem 4.1 (corollary): Combined `composeMonotone` factors.**
For any axis `a`, applying the combined-package monotone composition to
state `s` is the same as applying `p1`'s composition followed by `p2`'s:
`composeMonotone ((p1.combine p2).cat1 a) s
  = composeMonotone (p2.cat1 a) (composeMonotone (p1.cat1 a) s)`.

This is the convergence-preserving structural identity: the combined
package's per-axis Cat1 evaluation factors through each package's. -/
theorem combine_composeMonotone (p1 p2 : Package C A) (a : A) (s : State C A) :
    composeMonotone ((p1.combine p2).cat1 a) s =
    composeMonotone (p2.cat1 a) (composeMonotone (p1.cat1 a) s) := by
  unfold composeMonotone
  rw [combine_cat1, List.foldl_append]

/-- **Theorem 4.2: Disjoint package non-interference.**
For an axis `a` not in `p2`'s scope, the combined package's Cat1 and Cat2
rule lists for `a` reduce to `p1`'s. (Symmetric statement holds for axes
not in `p1`'s scope.)

When `p1.axes` and `p2.axes` are disjoint and `a ∈ p1.axes`, this gives
`(p1.combine p2).cat1 a = p1.cat1 a`: combining does not introduce P2's
rules at P1's axes, because P2's rules are scoped to P2's axes only. -/
theorem disjoint_packages_noninterference_cat1
    (p1 p2 : Package C A) (a : A) (h_not_in_p2 : a ∉ p2.axes) :
    (p1.combine p2).cat1 a = p1.cat1 a := by
  rw [combine_cat1, p2.cat1_scope a h_not_in_p2, List.append_nil]

theorem disjoint_packages_noninterference_cat2
    (p1 p2 : Package C A) (a : A) (h_not_in_p2 : a ∉ p2.axes) :
    (p1.combine p2).cat2 a = p1.cat2 a := by
  rw [combine_cat2, p2.cat2_scope a h_not_in_p2, List.append_nil]

/-- **Theorem 4.2 (corollary): On disjoint scopes the combined Cat1
composition collapses to the owning package's composition.** -/
theorem disjoint_composeMonotone_eq_p1
    (p1 p2 : Package C A) (a : A) (h_not_in_p2 : a ∉ p2.axes) (s : State C A) :
    composeMonotone ((p1.combine p2).cat1 a) s = composeMonotone (p1.cat1 a) s := by
  rw [disjoint_packages_noninterference_cat1 p1 p2 a h_not_in_p2]

/-- **Theorem 4.3: Shared-axis confluence.**
Under the hypothesis that `p1`'s and `p2`'s Cat1 rules confluence on
shared axes (rule order does not affect the result), the combined
Cat1 composition on every shared axis equals the swapped composition
(`p2.combine p1`'s composition). The combined fixpoint on shared axes
is therefore order-invariant in the package combination. -/
theorem shared_axis_confluence
    (p1 p2 : Package C A)
    (shared : Finset A)
    (_h_shared : shared = p1.axes ∩ p2.axes)
    (h_confluent : ∀ a ∈ shared, ∀ s : State C A,
      composeMonotone (p1.cat1 a) (composeMonotone (p2.cat1 a) s) =
      composeMonotone (p2.cat1 a) (composeMonotone (p1.cat1 a) s)) :
    ∀ a ∈ shared, ∀ s : State C A,
      composeMonotone ((p1.combine p2).cat1 a) s =
      composeMonotone ((p2.combine p1).cat1 a) s := by
  intro a h_a_shared s
  rw [combine_composeMonotone, combine_composeMonotone]
  exact (h_confluent a h_a_shared s).symm
