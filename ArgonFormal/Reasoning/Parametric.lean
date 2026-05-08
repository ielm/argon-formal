/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.Reasoning.Composition

/-!
# Parametric Propagation: Termination via Expansion Equivalence

Parametric rules (universally quantified over axes satisfying a bound predicate)
are equivalent to their monomorphized expansion. All existing fixpoint theorems
(convergence, uniqueness, stability, composition) lift directly to parametric
rule sets via this reduction.

## Key Insight

A parametric rule over a finite parameter space is syntactic sugar for a finite
set of concrete rules. The `inst_targets` invariant — each instantiation targets
the axis it was instantiated for — ensures stratification is preserved through
expansion. "Lazy" evaluation (instantiating per-stratum) and "eager" evaluation
(expanding all rules upfront) produce definitionally equal rule lists per axis.

## Main Definitions

- `ParametricMonotoneRule` — a Cat1 rule template parameterized by an axis bound
- `ParametricNafRule` — a Cat2 rule template parameterized by an axis bound
- `ParametricRuleSet` — a rule set mixing concrete and parametric rules
- `ParametricRuleSet.expand` — monomorphize parametric rules into a `StratifiedRuleSet`
- `parametricFixpoint` — the stratified fixpoint of an expanded parametric rule set

## Main Results

- `parametric_fixpoint_terminates` — T_P.1: termination (via Theorem 1.1)
- `parametric_fixpoint_unique` — T_P.2: uniqueness (via Theorem 1.2)
- `parametric_fixpoint_stable` — T_P.3: stability (via Theorem 1.3)
- `lazy_eq_eager` — T_P.4: lazy per-axis expansion = eager full expansion
- `parametric_combine_expand_perm_cat1/cat2` — T_P.5: combine then expand ~ expand then combine
- `parametric_rule_count_bound` — T_P.6: expanded rule count ≤ concrete + parametric count
-/

variable {C A : Type} [DecidableEq C] [DecidableEq A] [Fintype C] [Fintype A]

/-! ## Parametric Rule Structures -/

/-- A parametric Category 1 (positive propagation) rule.

Universally quantified over axes satisfying a bound predicate.
For each axis `a` where `bound a` holds, `instantiate a` produces a concrete
`MonotoneRule` targeting axis `a`. This models generic constraints like
`<Ax: ordered_axis>` in the meta-property calculus. -/
structure ParametricMonotoneRule (C A : Type) [DecidableEq C] [DecidableEq A] where
  /-- Predicate selecting which axes this rule applies to. -/
  bound : A → Prop
  /-- The bound is decidable (enables enumeration of matching axes). -/
  bound_decidable : DecidablePred bound
  /-- For each axis satisfying the bound, a concrete monotone rule. -/
  instantiate : (a : A) → bound a → MonotoneRule C A
  /-- Each instantiation targets the axis it was instantiated for.
  This is the key invariant: it ensures expansion preserves stratification. -/
  inst_targets : ∀ (a : A) (h : bound a), (instantiate a h).axis = a

/-- A parametric Category 2 (negation-as-failure) rule.

Same structure as `ParametricMonotoneRule` but produces `NafRule`s. -/
structure ParametricNafRule (C A : Type) [DecidableEq C] [DecidableEq A] where
  /-- Predicate selecting which axes this rule applies to. -/
  bound : A → Prop
  /-- The bound is decidable. -/
  bound_decidable : DecidablePred bound
  /-- For each axis satisfying the bound, a concrete NAF rule. -/
  instantiate : (a : A) → bound a → NafRule C A
  /-- Each instantiation targets the axis it was instantiated for. -/
  inst_targets : ∀ (a : A) (h : bound a), (instantiate a h).axis = a

/-! ## Try-Instantiate Helpers -/

/-- Try to instantiate a parametric Cat1 rule for a specific axis.
Returns `some r` if the bound is satisfied, `none` otherwise. -/
def ParametricMonotoneRule.tryInstantiate (pr : ParametricMonotoneRule C A) (a : A) :
    Option (MonotoneRule C A) :=
  match pr.bound_decidable a with
  | .isTrue h => some (pr.instantiate a h)
  | .isFalse _ => none

/-- Try to instantiate a parametric Cat2 rule for a specific axis. -/
def ParametricNafRule.tryInstantiate (pr : ParametricNafRule C A) (a : A) :
    Option (NafRule C A) :=
  match pr.bound_decidable a with
  | .isTrue h => some (pr.instantiate a h)
  | .isFalse _ => none

/-- If `tryInstantiate` succeeds, the resulting rule targets the given axis. -/
theorem ParametricMonotoneRule.tryInstantiate_axis
    {pr : ParametricMonotoneRule C A} {a : A} {r : MonotoneRule C A}
    (heq : pr.tryInstantiate a = some r) : r.axis = a := by
  unfold tryInstantiate at heq
  revert heq
  cases pr.bound_decidable a with
  | isTrue hb =>
    intro heq
    injection heq with heq
    rw [← heq]
    exact pr.inst_targets a hb
  | isFalse _ =>
    intro heq; exact absurd heq (by simp)

/-- If `tryInstantiate` succeeds for a NAF rule, the result targets the given axis. -/
theorem ParametricNafRule.tryInstantiate_axis
    {pr : ParametricNafRule C A} {a : A} {r : NafRule C A}
    (heq : pr.tryInstantiate a = some r) : r.axis = a := by
  unfold tryInstantiate at heq
  revert heq
  cases pr.bound_decidable a with
  | isTrue hb =>
    intro heq
    injection heq with heq
    rw [← heq]
    exact pr.inst_targets a hb
  | isFalse _ =>
    intro heq; exact absurd heq (by simp)

/-! ## Parametric Rule Set -/

/-- A rule set with both concrete and parametric rules.

Extends `StratifiedRuleSet` with parametric rule lists. The `expand` function
monomorphizes parametric rules into concrete rules, producing a standard
`StratifiedRuleSet` to which all existing theorems apply. -/
structure ParametricRuleSet (C A : Type) [DecidableEq C] [DecidableEq A] [Fintype C] [Fintype A] where
  /-- The stratification of axes. -/
  strat : Stratification A
  /-- Concrete Category 1 rules, indexed by axis. -/
  cat1 : A → List (MonotoneRule C A)
  /-- Concrete Category 2 rules, indexed by axis. -/
  cat2 : A → List (NafRule C A)
  /-- Parametric Category 1 rules. -/
  pcat1 : List (ParametricMonotoneRule C A)
  /-- Parametric Category 2 rules. -/
  pcat2 : List (ParametricNafRule C A)
  /-- Constraint checks (always concrete). -/
  cat3 : List (ConstraintCheck C A)
  /-- Concrete Cat1 rules for axis `a` target axis `a`. -/
  cat1_axis : ∀ a, ∀ r ∈ cat1 a, r.axis = a
  /-- Concrete Cat2 rules for axis `a` target axis `a`. -/
  cat2_axis : ∀ a, ∀ r ∈ cat2 a, r.axis = a
  /-- Concrete Cat1 rules at axis `a` have trigger reads strictly below `strat a`. -/
  cat1_strat_consistent : ∀ a, ∀ r ∈ cat1 a, ∀ b ∈ r.read_axes,
    strat.strat b < strat.strat a
  /-- Concrete Cat2 rules at axis `a` have trigger reads strictly below `strat a`. -/
  cat2_strat_consistent : ∀ a, ∀ r ∈ cat2 a, ∀ b ∈ r.read_axes,
    strat.strat b < strat.strat a
  /-- Parametric Cat1 rules: every instantiation respects stratification. -/
  pcat1_strat_consistent : ∀ pr ∈ pcat1, ∀ (a : A) (h : pr.bound a),
    ∀ b ∈ (pr.instantiate a h).read_axes,
      strat.strat b < strat.strat a
  /-- Parametric Cat2 rules: every instantiation respects stratification. -/
  pcat2_strat_consistent : ∀ pr ∈ pcat2, ∀ (a : A) (h : pr.bound a),
    ∀ b ∈ (pr.instantiate a h).read_axes,
      strat.strat b < strat.strat a

/-! ## Expansion (Monomorphization) -/

/-- Helper: expand parametric Cat1 rules for a specific axis. -/
def expandCat1ForAxis (pcat1 : List (ParametricMonotoneRule C A)) (a : A) :
    List (MonotoneRule C A) :=
  pcat1.filterMap fun pr => pr.tryInstantiate a

/-- Helper: expand parametric Cat2 rules for a specific axis. -/
def expandCat2ForAxis (pcat2 : List (ParametricNafRule C A)) (a : A) :
    List (NafRule C A) :=
  pcat2.filterMap fun pr => pr.tryInstantiate a

/-- Every rule in `expandCat1ForAxis` targets the given axis. -/
theorem expandCat1ForAxis_axis (pcat1 : List (ParametricMonotoneRule C A)) (a : A) :
    ∀ r ∈ expandCat1ForAxis pcat1 a, r.axis = a := by
  intro r hr
  simp only [expandCat1ForAxis, List.mem_filterMap] at hr
  obtain ⟨pr, _, heq⟩ := hr
  exact ParametricMonotoneRule.tryInstantiate_axis heq

/-- Every rule in `expandCat2ForAxis` targets the given axis. -/
theorem expandCat2ForAxis_axis (pcat2 : List (ParametricNafRule C A)) (a : A) :
    ∀ r ∈ expandCat2ForAxis pcat2 a, r.axis = a := by
  intro r hr
  simp only [expandCat2ForAxis, List.mem_filterMap] at hr
  obtain ⟨pr, _, heq⟩ := hr
  exact ParametricNafRule.tryInstantiate_axis heq

/-- Monomorphize a parametric rule set into a concrete `StratifiedRuleSet`.

For each axis `a`, the expanded Cat1 rules are the concrete rules for `a`
followed by all parametric rules instantiated for `a` (those whose bound
is satisfied). Similarly for Cat2. -/
def ParametricRuleSet.expand (prs : ParametricRuleSet C A) : StratifiedRuleSet C A where
  strat := prs.strat
  cat1 a := prs.cat1 a ++ expandCat1ForAxis prs.pcat1 a
  cat2 a := prs.cat2 a ++ expandCat2ForAxis prs.pcat2 a
  cat3 := prs.cat3
  cat1_axis := by
    intro a r hr
    rw [List.mem_append] at hr
    cases hr with
    | inl h => exact prs.cat1_axis a r h
    | inr h => exact expandCat1ForAxis_axis prs.pcat1 a r h
  cat2_axis := by
    intro a r hr
    rw [List.mem_append] at hr
    cases hr with
    | inl h => exact prs.cat2_axis a r h
    | inr h => exact expandCat2ForAxis_axis prs.pcat2 a r h
  cat1_strat_consistent := by
    intro a r hr b hb
    rw [List.mem_append] at hr
    cases hr with
    | inl h => exact prs.cat1_strat_consistent a r h b hb
    | inr h =>
      -- r came from expanding some parametric rule pr at axis a.
      simp only [expandCat1ForAxis, List.mem_filterMap] at h
      obtain ⟨pr, hpr, heq⟩ := h
      unfold ParametricMonotoneRule.tryInstantiate at heq
      revert heq
      cases hbnd : pr.bound_decidable a with
      | isTrue hb' =>
        intro heq
        injection heq with heq
        rw [← heq] at hb
        exact prs.pcat1_strat_consistent pr hpr a hb' b hb
      | isFalse _ => intro heq; exact absurd heq (by simp)
  cat2_strat_consistent := by
    intro a r hr b hb
    rw [List.mem_append] at hr
    cases hr with
    | inl h => exact prs.cat2_strat_consistent a r h b hb
    | inr h =>
      simp only [expandCat2ForAxis, List.mem_filterMap] at h
      obtain ⟨pr, hpr, heq⟩ := h
      unfold ParametricNafRule.tryInstantiate at heq
      revert heq
      cases hbnd : pr.bound_decidable a with
      | isTrue hb' =>
        intro heq
        injection heq with heq
        rw [← heq] at hb
        exact prs.pcat2_strat_consistent pr hpr a hb' b hb
      | isFalse _ => intro heq; exact absurd heq (by simp)

/-! ## Parametric Fixpoint -/

/-- The stratified fixpoint of a parametric rule set, computed by first
expanding (monomorphizing) all parametric rules and then running the
standard stratified fixpoint engine. -/
noncomputable def parametricFixpoint (prs : ParametricRuleSet C A)
    (axisSorted : List A) (s₀ : State C A) : State C A :=
  stratifiedFixpoint prs.expand axisSorted s₀

/-! ## T_P.1: Termination -/

/-- **Theorem T_P.1: Parametric fixpoint terminates.**

Follows immediately from Theorem 1.1 applied to the expanded rule set.
The expansion is a valid `StratifiedRuleSet`, so all existing convergence
machinery applies. -/
theorem parametric_fixpoint_terminates (prs : ParametricRuleSet C A)
    (axisSorted : List A) (s₀ : State C A) :
    ∃ result : State C A, result = parametricFixpoint prs axisSorted s₀ :=
  stratified_fixpoint_terminates prs.expand axisSorted s₀

/-! ## T_P.2: Uniqueness -/

/-- **Theorem T_P.2: Parametric fixpoint is unique.**

The result is independent of the topological order chosen, as long as
the order is a valid topological sort. Follows from Theorem 1.2 applied
to the expanded rule set. -/
theorem parametric_fixpoint_unique (prs : ParametricRuleSet C A)
    (sort1 sort2 : List A)
    (h_perm : sort1.Perm sort2)
    (h_nodup : sort1.Nodup)
    (hvalid1 : IsTopoSort prs.strat sort1)
    (hvalid2 : IsTopoSort prs.strat sort2) :
    parametricFixpoint prs sort1 State.initial =
    parametricFixpoint prs sort2 State.initial := by
  -- Delegates to Theorem 1.2 on the expanded rule set.
  -- The expanded set uses the same stratification as the parametric set.
  exact stratified_fixpoint_unique prs.expand sort1 sort2 h_perm h_nodup
    (show IsTopoSort prs.expand.strat sort1 from hvalid1)
    (show IsTopoSort prs.expand.strat sort2 from hvalid2)

/-! ## T_P.3: Stability -/

/-- **Theorem T_P.3: Parametric fixpoint is stable.**

No rule application (concrete or expanded parametric) changes the result.
Follows from Theorem 1.3 applied to the expanded rule set. -/
theorem parametric_fixpoint_stable (prs : ParametricRuleSet C A)
    (axisSorted : List A)
    (h_nodup : axisSorted.Nodup)
    (h_valid : IsTopoSort prs.strat axisSorted) :
    let result := parametricFixpoint prs axisSorted State.initial
    (∀ a ∈ axisSorted, ∀ r ∈ prs.expand.cat1 a, r.apply result = result) ∧
    (∀ a ∈ axisSorted, ∀ r ∈ prs.expand.cat2 a, r.apply result = result) :=
  stratified_fixpoint_stable prs.expand axisSorted h_nodup
    (show IsTopoSort prs.expand.strat axisSorted from h_valid)

/-! ## T_P.4: Lazy Expansion Equivalence -/

/-- Lazy expansion for a single axis: only instantiate parametric rules
whose bound matches this specific axis.

This is the "on-demand" evaluation strategy where rules are instantiated
as their strata are processed, rather than all upfront. -/
def lazyExpandAxis (prs : ParametricRuleSet C A) (a : A) :
    List (MonotoneRule C A) × List (NafRule C A) :=
  (prs.cat1 a ++ expandCat1ForAxis prs.pcat1 a,
   prs.cat2 a ++ expandCat2ForAxis prs.pcat2 a)

/-- **Theorem T_P.4: Lazy expansion equals eager expansion.**

For each axis, the rules produced by lazy per-axis expansion are
definitionally equal to the rules in the eagerly expanded `StratifiedRuleSet`.

This is the core "lazy termination" result: there is no separate proof needed
because lazy and eager evaluation compute the same thing per axis. The
`inst_targets` invariant ensures each parametric instantiation contributes
rules to exactly one axis's stratum. -/
theorem lazy_eq_eager (prs : ParametricRuleSet C A) (a : A) :
    (lazyExpandAxis prs a).1 = prs.expand.cat1 a ∧
    (lazyExpandAxis prs a).2 = prs.expand.cat2 a :=
  ⟨rfl, rfl⟩

/-! ## T_P.5: Parametric Package Composition -/

/-- A package with both concrete and parametric rules.

Extends `Package` with parametric rule lists and scope constraints ensuring
parametric rules only instantiate for axes owned by this package. -/
structure ParametricPackage (C A : Type) [DecidableEq C] [DecidableEq A] [Fintype C] [Fintype A] where
  /-- The axes this package defines rules for. -/
  axes : Finset A
  /-- Concrete Category 1 rules per axis. -/
  cat1 : A → List (MonotoneRule C A)
  /-- Concrete Category 2 rules per axis. -/
  cat2 : A → List (NafRule C A)
  /-- Parametric Category 1 rules. -/
  pcat1 : List (ParametricMonotoneRule C A)
  /-- Parametric Category 2 rules. -/
  pcat2 : List (ParametricNafRule C A)
  /-- Concrete rules are scoped to package axes. -/
  cat1_scope : ∀ a, a ∉ axes → cat1 a = []
  /-- Concrete Cat2 rules are scoped to package axes. -/
  cat2_scope : ∀ a, a ∉ axes → cat2 a = []
  /-- Parametric Cat1 rules only instantiate for package axes. -/
  pcat1_scope : ∀ pr ∈ pcat1, ∀ a, pr.bound a → a ∈ axes
  /-- Parametric Cat2 rules only instantiate for package axes. -/
  pcat2_scope : ∀ pnr ∈ pcat2, ∀ a, pnr.bound a → a ∈ axes

/-- Combine two parametric packages. -/
def ParametricPackage.combine (pp1 pp2 : ParametricPackage C A) : ParametricPackage C A where
  axes := pp1.axes ∪ pp2.axes
  cat1 a := pp1.cat1 a ++ pp2.cat1 a
  cat2 a := pp1.cat2 a ++ pp2.cat2 a
  pcat1 := pp1.pcat1 ++ pp2.pcat1
  pcat2 := pp1.pcat2 ++ pp2.pcat2
  cat1_scope a ha := by
    simp [Finset.mem_union] at ha
    rw [pp1.cat1_scope a ha.1, pp2.cat1_scope a ha.2]; simp
  cat2_scope a ha := by
    simp [Finset.mem_union] at ha
    rw [pp1.cat2_scope a ha.1, pp2.cat2_scope a ha.2]; simp
  pcat1_scope pr hpr a hba := by
    rw [List.mem_append] at hpr
    cases hpr with
    | inl h => exact Finset.mem_union_left _ (pp1.pcat1_scope pr h a hba)
    | inr h => exact Finset.mem_union_right _ (pp2.pcat1_scope pr h a hba)
  pcat2_scope pnr hpnr a hba := by
    rw [List.mem_append] at hpnr
    cases hpnr with
    | inl h => exact Finset.mem_union_left _ (pp1.pcat2_scope pnr h a hba)
    | inr h => exact Finset.mem_union_right _ (pp2.pcat2_scope pnr h a hba)

/-- Expand a parametric package into a concrete `Package`. -/
def ParametricPackage.expandToPackage (pp : ParametricPackage C A) : Package C A where
  axes := pp.axes
  cat1 a := pp.cat1 a ++ expandCat1ForAxis pp.pcat1 a
  cat2 a := pp.cat2 a ++ expandCat2ForAxis pp.pcat2 a
  cat1_scope a ha := by
    rw [List.append_eq_nil_iff]
    exact ⟨pp.cat1_scope a ha, by
      rw [expandCat1ForAxis, List.filterMap_eq_nil_iff]
      intro pr hpr
      show pr.tryInstantiate a = none
      unfold ParametricMonotoneRule.tryInstantiate
      cases pr.bound_decidable a with
      | isTrue hb => exact absurd (pp.pcat1_scope pr hpr a hb) ha
      | isFalse _ => rfl⟩
  cat2_scope a ha := by
    rw [List.append_eq_nil_iff]
    exact ⟨pp.cat2_scope a ha, by
      rw [expandCat2ForAxis, List.filterMap_eq_nil_iff]
      intro pnr hpnr
      show pnr.tryInstantiate a = none
      unfold ParametricNafRule.tryInstantiate
      cases pnr.bound_decidable a with
      | isTrue hb => exact absurd (pp.pcat2_scope pnr hpnr a hb) ha
      | isFalse _ => rfl⟩

/-! ## T_P.5: Parametric Package Composition

**Theorem T_P.5:** Combining parametric packages then expanding produces
a permutation of expanding then combining.

Strict list equality fails because the interleaving differs:
- `expand(combine(P1,P2)).cat1 a = (P1.cat1 ++ P2.cat1) ++ (fmap P1.pcat1 ++ fmap P2.pcat1)`
- `combine(expand(P1),expand(P2)).cat1 a = (P1.cat1 ++ fmap P1.pcat1) ++ (P2.cat1 ++ fmap P2.pcat1)`

These are permutations of each other. Since `composeMonotone` applied to
a permuted rule list reaches the same fixpoint (Theorem 1.2 gives
order-independence), this suffices for all composition results. -/

/-- Auxiliary: `(A++B)++(C++D) ~ (A++C)++(B++D)` for any four lists. -/
private theorem perm_append_four {α : Type*} (l1 l2 l3 l4 : List α) :
    ((l1 ++ l2) ++ (l3 ++ l4)).Perm ((l1 ++ l3) ++ (l2 ++ l4)) := by
  -- Right-associate everything, then permute the middle segments.
  rw [List.append_assoc, List.append_assoc]
  -- Goal: (l1 ++ (l2 ++ (l3 ++ l4))).Perm (l1 ++ (l3 ++ (l2 ++ l4)))
  apply List.Perm.append_left l1
  -- Goal: (l2 ++ (l3 ++ l4)).Perm (l3 ++ (l2 ++ l4))
  rw [← List.append_assoc, ← List.append_assoc]
  -- Goal: ((l2 ++ l3) ++ l4).Perm ((l3 ++ l2) ++ l4)
  exact List.Perm.append_right l4 List.perm_append_comm

theorem parametric_combine_expand_perm_cat1 (pp1 pp2 : ParametricPackage C A) (a : A) :
    ((pp1.combine pp2).expandToPackage.cat1 a).Perm
      ((pp1.expandToPackage.combine pp2.expandToPackage).cat1 a) := by
  simp only [ParametricPackage.expandToPackage, Package.combine, ParametricPackage.combine,
    expandCat1ForAxis, List.filterMap_append]
  exact perm_append_four _ _ _ _

/-- Same permutation result for Cat2 rules. -/
theorem parametric_combine_expand_perm_cat2 (pp1 pp2 : ParametricPackage C A) (a : A) :
    ((pp1.combine pp2).expandToPackage.cat2 a).Perm
      ((pp1.expandToPackage.combine pp2.expandToPackage).cat2 a) := by
  simp only [ParametricPackage.expandToPackage, Package.combine, ParametricPackage.combine,
    expandCat2ForAxis, List.filterMap_append]
  exact perm_append_four _ _ _ _

/-! ## T_P.6: Complexity Bound -/

/-- The number of expanded Cat1 rules for axis `a` from parametric rules is
at most the total number of parametric Cat1 rules. -/
theorem expandCat1_length_le (pcat1 : List (ParametricMonotoneRule C A)) (a : A) :
    (expandCat1ForAxis pcat1 a).length ≤ pcat1.length := by
  simp only [expandCat1ForAxis]
  exact List.length_filterMap_le _ _

/-- The number of expanded Cat2 rules for axis `a` from parametric rules is
at most the total number of parametric Cat2 rules. -/
theorem expandCat2_length_le (pcat2 : List (ParametricNafRule C A)) (a : A) :
    (expandCat2ForAxis pcat2 a).length ≤ pcat2.length := by
  simp only [expandCat2ForAxis]
  exact List.length_filterMap_le _ _

/-- **Theorem T_P.6: Parametric expansion produces bounded rule counts.**

For each axis, the total number of expanded rules is at most the number of
concrete rules plus the number of parametric rules. In practice, if only K
of N possible axes satisfy a parametric bound, only K instantiations are
produced — the rest are filtered out by `tryInstantiate`. -/
theorem parametric_rule_count_bound (prs : ParametricRuleSet C A) (a : A) :
    (prs.expand.cat1 a).length + (prs.expand.cat2 a).length ≤
    (prs.cat1 a).length + prs.pcat1.length +
    ((prs.cat2 a).length + prs.pcat2.length) := by
  simp only [ParametricRuleSet.expand, List.length_append]
  have h1 := expandCat1_length_le prs.pcat1 a
  have h2 := expandCat2_length_le prs.pcat2 a
  omega

/-! ## Summary of Proof Status

### Zero new sorry's in this file.

All theorems are fully proved. `parametric_fixpoint_unique` and
`parametric_fixpoint_stable` delegate to sorry'd theorems in
`Fixpoint.lean` (Theorems 1.2 and 1.3), but this file adds no new
proof obligations.

### Fully proved:
- All structure definitions and `expand` well-formedness (T_P.0)
- `parametric_fixpoint_terminates` (T_P.1)
- `parametric_fixpoint_unique` (T_P.2, delegates to Theorem 1.2)
- `parametric_fixpoint_stable` (T_P.3, delegates to Theorem 1.3)
- `lazy_eq_eager` (T_P.4) — definitional equality (`rfl`)
- `parametric_combine_expand_perm_cat1/cat2` (T_P.5) — permutation
- `parametric_rule_count_bound` (T_P.6) — complexity bound
-/
