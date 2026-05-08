/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.TypeSystem.Soundness.CrossStratum

/-!
# Stratified Cross-Standpoint Composition

Generalizes Vennekens, Gilis & Denecker (2006) "Splitting an Operator" to the
per-standpoint Argon setting: when standpoints form a DAG of refinement edges
and each standpoint's per-stratum AFT operator is inflationary in the
information ordering, the cross-standpoint fold is itself inflationary, and
narrowings established at any earlier standpoint persist through the fold.

This is the technical foundation for:

- `Federation.lean`'s correctness theorem (federated query = AFT join across
  stratified per-standpoint K3 results),
- `BackwardCompat.lean`'s claim that the new framework collapses to RFD-0016
  in the single-standpoint case.

## What's proved

The structure mirrors `CrossStratum.lean` at a higher granularity. Where the
existing proof treats *axes* as the strata (one axis processed per fold step),
this proof treats *standpoints* as the strata (one standpoint's full per-axis
fixpoint per fold step). The technical content is identical: foldl of
inflationary operators is inflationary, and `satisfiedBy_mono` carries
narrowings through.

Per Vennekens, Gilis & Denecker (2006): if the standpoint dependency graph is
a DAG, the global well-founded fixpoint computes stratum-by-stratum. The list
parameter `standpointSorted : List S` is the witness of the topological sort —
existence of such a list is equivalent to acyclicity.

## What is NOT in this file

This file proves the *composition* property: cross-standpoint fold preserves
narrowings. It does **not** prove that any specific per-standpoint operator
(OWA/CWA/LCWA/MKNF+WFS) is itself inflationary — those are properties of the
operator construction. For OWA (identity) inflationarity is trivial; for CWA
(stratified-negation closure) it follows from `cat2Apply_inflationary` and
`cat1Fixpoint_inflationary` lifted to the standpoint level.

The main result of this file is parametric in the per-standpoint operator;
specific operator constructions live in `ArgonFormal.Reasoning` (the rule
+ fixpoint substrate) and are lifted to the standpoint level here.
-/

variable {C A : Type} [DecidableEq C] [DecidableEq A] [Fintype C] [Fintype A]

/-! ## Standpoint operator abstraction -/

/-- A *standpoint operator* is a state-to-state function indexed by a standpoint
identifier. In the Argon implementation each standpoint's operator is
constructed from its declared world-assumption mode (OWA → identity, CWA →
stratified-negation closure, etc.); here we abstract over those constructions
and only require inflationarity in the information ordering. -/
structure StandpointOperator (S C A : Type) [DecidableEq C] [DecidableEq A]
    [Fintype C] [Fintype A] where
  /-- The operator itself: takes a standpoint id and a state, returns a state. -/
  apply : S → State C A → State C A
  /-- **The load-bearing property:** every per-standpoint operator is
  inflationary in the information ordering. Established for the standard
  operators (OWA / CWA / LCWA) by the per-axis stratified-fixpoint proofs in
  `ArgonFormal.TypeSystem.Soundness.CrossStratum` and
  `ArgonFormal.Reasoning.Fixpoint`. -/
  inflationary : ∀ (s : S) (st : State C A), st ≤ apply s st

namespace StandpointOperator

variable {S : Type}

/-! ## The cross-standpoint fold -/

/-- Cross-standpoint fold: process standpoints in topological order. Mirrors
`stratifiedFixpoint` but over standpoints rather than axes. -/
def crossStandpointFold (op : StandpointOperator S C A)
    (standpointSorted : List S) (s₀ : State C A) : State C A :=
  standpointSorted.foldl (fun s sp => op.apply sp s) s₀

/-- The cross-standpoint fold is inflationary. Direct generalization of
`stratifiedFixpoint_inflationary`: foldl of inflationary operators is itself
inflationary in the information ordering. -/
theorem crossStandpointFold_inflationary (op : StandpointOperator S C A)
    (standpointSorted : List S) (s₀ : State C A) :
    s₀ ≤ op.crossStandpointFold standpointSorted s₀ := by
  induction standpointSorted generalizing s₀ with
  | nil => exact le_refl _
  | cons sp sps ih =>
    simp only [crossStandpointFold, List.foldl]
    exact le_trans (op.inflationary sp s₀) (ih (op.apply sp s₀))

/-! ## Narrowing preservation -/

/-- **Cross-standpoint narrowing preservation.**

If a narrowing environment is satisfied at any state encountered during
cross-standpoint composition, it is satisfied at the resulting state.

This is the standpoint-level analogue of `narrowing_preserved_cross_stratum`:
narrowings are upward-closed in the information ordering, the fold is
inflationary in the information ordering, therefore narrowings survive the
fold. -/
theorem narrowing_preserved_across_standpoints (op : StandpointOperator S C A)
    (standpointSorted : List S) (env : NarrowEnv C A) (s₀ : State C A)
    (h : env.satisfiedBy s₀) :
    env.satisfiedBy (op.crossStandpointFold standpointSorted s₀) :=
  env.satisfiedBy_mono (op.crossStandpointFold_inflationary standpointSorted s₀) h

/-! ## Composition: per-standpoint stratified-fixpoint as a `StandpointOperator`

The standard construction: given a `StratifiedRuleSet` per standpoint, build a
`StandpointOperator` whose per-standpoint application is exactly the existing
per-axis `stratifiedFixpoint`. This is what plugs the new cross-standpoint
machinery into the existing per-axis machinery. -/

/-- Build a `StandpointOperator` from a per-standpoint stratified rule set + axis order.

`rules sp` gives the rule set for standpoint `sp`; `axisSorted sp` gives the
topological axis order for that standpoint's dependency graph. The resulting
operator's per-standpoint application is the existing `stratifiedFixpoint` over
that standpoint's rules. -/
noncomputable def fromStratifiedPerStandpoint
    (rules : S → StratifiedRuleSet C A) (axisSorted : S → List A) :
    StandpointOperator S C A where
  apply sp s := stratifiedFixpoint (rules sp) (axisSorted sp) s
  inflationary sp s := stratifiedFixpoint_inflationary (rules sp) (axisSorted sp) s

/-! ## End-to-end soundness -/

/-- **End-to-end soundness for the standard construction.**

When the per-standpoint operator is the standard stratified-fixpoint, narrowings
from any earlier state survive the cross-standpoint fold all the way to the
final result. Combines `narrowing_preserved_across_standpoints` with
`fromStratifiedPerStandpoint`. -/
theorem stratified_cross_standpoint_soundness
    (rules : S → StratifiedRuleSet C A) (axisSorted : S → List A)
    (standpointSorted : List S)
    (env : NarrowEnv C A) (s₀ : State C A)
    (h : env.satisfiedBy s₀) :
    env.satisfiedBy
      ((fromStratifiedPerStandpoint rules axisSorted).crossStandpointFold
        standpointSorted s₀) :=
  narrowing_preserved_across_standpoints _ standpointSorted env s₀ h

end StandpointOperator
