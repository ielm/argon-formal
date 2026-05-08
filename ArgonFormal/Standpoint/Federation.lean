/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.Foundation.Projection
import ArgonFormal.Standpoint.Stratification

/-!
# Cross-Standpoint Federation via AFT Join

A *federated query* in Argon aggregates per-standpoint results across multiple
standpoints. Each contributing standpoint produces a K3 value (`Truth4` in the
consistent fragment); the federation operation combines these into a single
`Truth4` value that may be in FDE (carry `both`) when sources disagree.

The aggregation is **AFT information join (gullibility, `⊕`)**: the
information-order least-upper-bound of all contributions. The resulting
`Truth4` reads:

| Federation result | Interpretation |
|---|---|
| `is`   | At least one source said T; none said F or `both`. |
| `not`  | At least one source said F; none said T or `both`. |
| `can`  | No source had evidence (every contribution was `can`). |
| `both` | At least one source said T **and** at least one said F (or any source already said `both`). |

The `both` case is exactly cross-source disagreement. It arises only via
information-join — the operation that escapes the K3 fragment per
`infoJoin_escapes_K3`.

## Proof strategy

Rather than proving each direction of the four classification iffs separately,
we define a structural classification function `classify : List Truth4 → Truth4`
that scans the list and returns the same result by case analysis on what's
present. We then prove `federate contribs = classify contribs` by induction;
all the iff theorems follow as corollaries.

This is cleaner than direct fold-induction because `classify` is monotone in
list-prefix and gives us a clean single-step inductive argument.

## Connection to the standpoint composition framework

This file consumes `StandpointStratification.lean`'s cross-standpoint fold —
each standpoint produces a per-standpoint `MetaValue` result via its own
stratified-fixpoint computation, and federation is the additional aggregation
step layered on top.
-/

namespace Truth4

/-! ## Federation as foldl over `infoJoin` -/

/-- Federate a list of per-standpoint contributions into a single `Truth4` value.
The aggregation is information-join (gullibility / AFT info-LUB), starting from
`can` (the bottom of the information ordering — "no info"). -/
def federate (contribs : List Truth4) : Truth4 :=
  contribs.foldl infoJoin .can

/-! ## Structural classification of contribution lists

The classification scans the list and reports which truth-evidence appears.
We prove `federate = classify` by induction; all the case-analysis theorems
about `federate` then follow from the classification's straightforward
case structure. -/

/-- True iff some element of the list is `is`. -/
def hasIs (l : List Truth4) : Prop := .is ∈ l

/-- True iff some element of the list is `not`. -/
def hasNot (l : List Truth4) : Prop := .not ∈ l

/-- True iff some element of the list is `both`. -/
def hasBoth (l : List Truth4) : Prop := .both ∈ l

instance : DecidablePred hasIs := fun l => by
  unfold hasIs; infer_instance
instance : DecidablePred hasNot := fun l => by
  unfold hasNot; infer_instance
instance : DecidablePred hasBoth := fun l => by
  unfold hasBoth; infer_instance

/-- Classify a contribution list directly: predict the `Truth4` value the
information-join fold will produce. -/
def classify (l : List Truth4) : Truth4 :=
  if hasBoth l then .both
  else if hasIs l ∧ hasNot l then .both
  else if hasIs l then .is
  else if hasNot l then .not
  else .can

/-! ## The classification matches the fold

Proof by induction over the list, generalizing over the accumulator. The key
property: the fold's accumulator at each step is `infoJoin acc v` where `v` is
the head; this is determined by what `acc` and `v` carry, which the
classification tracks. -/

/-- Helper: classification of a cons list reduces to info-join of the head with
classification of the tail. This is the key step in the fold-equals-classify
inductive proof; we prove it by case analysis on the head and on which values
appear in the tail. -/
private theorem classify_cons (v : Truth4) (vs : List Truth4) :
    classify (v :: vs) = infoJoin v (classify vs) := by
  unfold classify
  unfold hasBoth hasIs hasNot
  cases v <;>
    by_cases h_both : (Truth4.both ∈ vs) <;>
    by_cases h_is : (Truth4.is ∈ vs) <;>
    by_cases h_not : (Truth4.not ∈ vs) <;>
    simp_all [List.mem_cons, infoJoin]

/-- Helper: the fold's behaviour with an arbitrary starting accumulator. The
running accumulator's information content equals the info-join of the starting
accumulator with everything seen so far. -/
private theorem foldl_infoJoin_classify (l : List Truth4) (acc : Truth4) :
    l.foldl infoJoin acc = infoJoin acc (classify l) := by
  induction l generalizing acc with
  | nil =>
    -- Goal: acc = infoJoin acc (classify [])
    -- classify [] = .can, and infoJoin acc .can = acc
    cases acc <;> simp [classify, hasBoth, hasIs, hasNot, infoJoin]
  | cons v vs ih =>
    -- LHS: (v :: vs).foldl infoJoin acc = vs.foldl infoJoin (infoJoin acc v)
    -- RHS: infoJoin acc (classify (v :: vs)) = infoJoin acc (infoJoin v (classify vs))
    --                                        = infoJoin (infoJoin acc v) (classify vs) [assoc]
    -- And by IH, LHS = infoJoin (infoJoin acc v) (classify vs).
    calc (v :: vs).foldl infoJoin acc
        = vs.foldl infoJoin (infoJoin acc v) := by rfl
      _ = infoJoin (infoJoin acc v) (classify vs) := ih (infoJoin acc v)
      _ = infoJoin acc (infoJoin v (classify vs)) := infoJoin_assoc acc v (classify vs)
      _ = infoJoin acc (classify (v :: vs)) := by rw [classify_cons]

/-- **The classification equals the federation.** Direct corollary of the
helper with `acc = .can`. -/
theorem federate_eq_classify (contribs : List Truth4) :
    federate contribs = classify contribs := by
  unfold federate
  rw [foldl_infoJoin_classify]
  -- infoJoin can (classify contribs) = classify contribs
  cases h : classify contribs <;> rfl

/-! ## Basic properties as corollaries -/

/-- Federating an empty list yields `can`. -/
@[simp] theorem federate_nil : federate [] = .can := rfl

/-- Federating a singleton list yields the single contribution. -/
@[simp] theorem federate_singleton (v : Truth4) : federate [v] = v := by
  rw [federate_eq_classify]
  cases v <;> simp [classify, hasIs, hasNot, hasBoth]

/-- Federation absorbs `can` contributions. The membership-checks `is ∈ _`,
`not ∈ _`, `both ∈ _` are unaffected by adding/removing a `can` element. -/
theorem federate_can_irrelevant (vs : List Truth4) (ws : List Truth4) :
    federate (vs ++ .can :: ws) = federate (vs ++ ws) := by
  rw [federate_eq_classify, federate_eq_classify]
  unfold classify hasIs hasNot hasBoth
  by_cases h_b : Truth4.both ∈ (vs ++ ws) <;>
    by_cases h_i : Truth4.is ∈ (vs ++ ws) <;>
    by_cases h_n : Truth4.not ∈ (vs ++ ws) <;>
    simp_all [List.mem_append, List.mem_cons]

/-! ## Disagreement characterization

The headline theorems: when does federation produce `both`? When does it stay
in K3? -/

/-- **Federation produces `both` iff at least one contribution is itself `both`,
or contributions disagree on truthiness (some `is` and some `not`).** -/
theorem federate_eq_both_iff (contribs : List Truth4) :
    federate contribs = .both ↔ hasBoth contribs ∨ (hasIs contribs ∧ hasNot contribs) := by
  rw [federate_eq_classify]
  unfold classify
  split_ifs with h1 h2 h3 h4 <;> simp_all

/-- **K3 closure on agreement.** If every contribution is in K3 (no source
already said `both`) and no two contributions disagree, the federation result
stays in K3. -/
theorem federate_inK3_of_agreement (contribs : List Truth4)
    (h_consist : ∀ v ∈ contribs, v.inK3)
    (h_agree : ¬ (hasIs contribs ∧ hasNot contribs)) :
    (federate contribs).inK3 := by
  -- By `federate_eq_both_iff`, the result is `.both` iff some source said
  -- `both` (ruled out by `h_consist`) or sources disagreed (ruled out by
  -- `h_agree`). Neither holds, so the result is not `.both` — i.e., in K3.
  have h_not_both : federate contribs ≠ .both := by
    intro h_eq
    rw [federate_eq_both_iff] at h_eq
    rcases h_eq with h_both | h_disagree
    · -- Some contribution is `both`; contradicts `h_consist`.
      have h_inK3 : (Truth4.both).inK3 := h_consist .both h_both
      simp [inK3, isConsistent] at h_inK3
    · exact h_agree h_disagree
  -- `inK3 = isConsistent`, which holds for everything except `both`.
  cases h : federate contribs <;> simp_all [inK3, isConsistent]

/-! ## Federation soundness via projection -/

/-- Single-standpoint federation = the contribution itself. Useful as a
back-compat hook: when the federation is over one standpoint, it reduces to
the existing single-standpoint K3 result. -/
theorem federate_single_standpoint (m : MetaValue) :
    federate [ofMetaValue m] = ofMetaValue m :=
  federate_singleton _

/-- Project a single-standpoint federation back to `MetaValue`: the round-trip
is the identity, regardless of policy. -/
theorem federate_single_standpoint_project (policy : ProjectionPolicy) (m : MetaValue) :
    project policy (federate [ofMetaValue m]) = some m := by
  rw [federate_single_standpoint]
  exact project_ofMetaValue policy m

/-- The `treatAsError` projection of a federation succeeds **iff** the federation
result is in K3. By `federate_eq_both_iff`, this is iff no source said `both`
and no two sources disagreed on truthiness. -/
theorem federate_project_treatAsError_iff (contribs : List Truth4) :
    (∃ m, project .treatAsError (federate contribs) = some m) ↔ (federate contribs).inK3 := by
  exact project_treatAsError_iff _

end Truth4
