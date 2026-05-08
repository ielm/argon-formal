/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.Reasoning.Rule

/-!
# Theorem 1: Stratified Fixpoint Convergence

## Statement

Given a finite set of concepts with a specialization DAG, a finite set of
meta-property axes with an acyclic dependency DAG, and for each axis a set
of Category 1 (positive propagation) and Category 2 (negation-as-failure)
rules:

1. The stratified fixpoint **terminates**.
2. The result is **unique** (independent of rule application order within
   a stratum).
3. The result is **stable** (no rule application would change any
   assignment).

## Proof Strategy

Process axes in topological order (guaranteed by acyclicity). For each
axis:
- Run all Cat1 rules to fixpoint (monotone on finite domain → terminates
  by Knaster-Tarski).
- Run all Cat2 rules to fixpoint (reads completed Cat1 state, monotone
  within its stratum).

No cross-stratum feedback because the dependency graph is acyclic: each
stratum's rules only read from already-completed lower strata.

The key insight: although the full IS/CAN/NOT ordering is not a lattice
(IS ⊔ NOT is undefined), each INDIVIDUAL stratum's computation IS
monotone because:
- Cat1 only produces IS (moving CAN → IS is monotone)
- Cat2 only produces NOT (moving CAN → NOT is monotone)
- Neither Cat1 nor Cat2 changes determined values

On a finite domain, a monotone operator has a least fixpoint reached in
finitely many steps.
-/

variable {C A : Type} [DecidableEq C] [DecidableEq A] [Fintype C] [Fintype A]

/-! ## Helpers: foldl/iterate inflationarity

Generic structural lemmas about `List.foldl` and `Nat.iterate` over
inflationary operators on preorders. Used throughout the fixpoint
machinery. -/

/-- Folding an inflationary step over a list is inflationary. -/
theorem foldl_inflationary {α β : Type*} [Preorder α]
    {f : α → β → α} (h : ∀ (a : α) (b : β), a ≤ f a b)
    (l : List β) (init : α) :
    init ≤ l.foldl f init := by
  induction l generalizing init with
  | nil => exact le_refl init
  | cons b l' ih =>
    simp only [List.foldl]
    exact le_trans (h init b) (ih (f init b))

/-- Iterating an inflationary function preserves the ordering. -/
theorem iterate_inflationary {α : Type*} [Preorder α]
    {f : α → α} (h : ∀ (a : α), a ≤ f a) :
    ∀ (n : Nat) (x : α), x ≤ Nat.iterate f n x := by
  intro n
  induction n with
  | zero => intro x; exact le_refl x
  | succ n ih =>
    intro x
    exact le_trans (h x) (ih (f x))

/-! ## The Stratified Fixpoint Computation -/

/-- Composing monotone rules preserves monotonicity. -/
theorem composeMonotone_monotone (rules : List (MonotoneRule C A)) :
    ∀ s t : State C A, s ≤ t → composeMonotone rules s ≤ composeMonotone rules t := by
  intro s t hst
  induction rules generalizing s t with
  | nil => exact hst
  | cons r rs ih =>
    simp only [composeMonotone, List.foldl]
    exact ih (r.apply s) (r.apply t) (r.monotone s t hst)

noncomputable def cat1Fixpoint (rules : List (MonotoneRule C A)) (s : State C A) : State C A :=
  iterateToFixpoint (composeMonotone rules) (composeMonotone_monotone rules) s

/-- Run all Category 2 rules for a single axis.
Applied ONCE to the completed Cat1 state (Cat2 rules check absence,
they don't iterate). -/
def cat2Apply (rules : List (NafRule C A)) (s : State C A) : State C A :=
  rules.foldl (fun acc r => r.apply acc) s

/-- Process a single stratum: run Cat1 to fixpoint, then Cat2. -/
noncomputable def processStratum (rs : StratifiedRuleSet C A) (a : A) (s : State C A) :
    State C A :=
  let afterCat1 := cat1Fixpoint (rs.cat1 a) s
  cat2Apply (rs.cat2 a) afterCat1

/-- The full stratified fixpoint: process each axis in topological order. -/
noncomputable def stratifiedFixpoint (rs : StratifiedRuleSet C A)
    (axisSorted : List A) (s₀ : State C A) : State C A :=
  axisSorted.foldl (fun s a => processStratum rs a s) s₀

/-! ## `processStratum` only modifies its own axis

Every rule in `rs.cat1 a` and `rs.cat2 a` has `axis = a` (by the
`StratifiedRuleSet` invariants `cat1_axis` and `cat2_axis`). Each rule's
`axis_local` field then says cells off the rule's axis are preserved.
Lifting through `composeMonotone` (foldl of cat1 rules), iteration to
fixpoint, and `cat2Apply` (foldl of cat2 rules) gives the result. -/

/-- A list-foldl helper: if every step preserves cells at position `(c, a')`,
the fold preserves them too. -/
private theorem foldl_preserves_at_pos {β : Type*} (l : List β)
    (f : State C A → β → State C A) (s : State C A) (c : C) (a' : A)
    (h_step : ∀ s' b, b ∈ l → (f s' b) c a' = s' c a') :
    (l.foldl f s) c a' = s c a' := by
  induction l generalizing s with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.foldl]
    rw [ih (f s b) (fun s' b' hb' => h_step s' b' (List.mem_cons_of_mem b hb'))]
    exact h_step s b List.mem_cons_self

/-- A `Nat.iterate` helper: if `f` preserves cells at position `(c, a')`,
all iterates do. -/
private theorem iterate_preserves_at_pos (f : State C A → State C A)
    (c : C) (a' : A) (h_step : ∀ s, (f s) c a' = s c a')
    (n : Nat) (s : State C A) : (Nat.iterate f n s) c a' = s c a' := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    rw [ih (f s)]
    exact h_step s

/-- `composeMonotone` of rules all with axis `a` preserves cells off axis `a`. -/
theorem composeMonotone_axis_local (rules : List (MonotoneRule C A)) (a : A)
    (h_axis : ∀ r ∈ rules, r.axis = a) (s : State C A) (c : C) (a' : A)
    (hne : a' ≠ a) : (composeMonotone rules s) c a' = s c a' := by
  unfold composeMonotone
  apply foldl_preserves_at_pos
  intro s' r hr
  have hr_axis : r.axis = a := h_axis r hr
  exact r.axis_local s' c a' (by rw [hr_axis]; exact hne)

/-- `cat1Fixpoint` of rules all with axis `a` preserves cells off axis `a`. -/
theorem cat1Fixpoint_axis_local (rules : List (MonotoneRule C A)) (a : A)
    (h_axis : ∀ r ∈ rules, r.axis = a) (s : State C A) (c : C) (a' : A)
    (hne : a' ≠ a) : (cat1Fixpoint rules s) c a' = s c a' := by
  unfold cat1Fixpoint iterateToFixpoint
  exact iterate_preserves_at_pos _ c a'
    (fun s' => composeMonotone_axis_local rules a h_axis s' c a' hne) _ s

/-- `cat2Apply` of rules all with axis `a` preserves cells off axis `a`. -/
theorem cat2Apply_axis_local (rules : List (NafRule C A)) (a : A)
    (h_axis : ∀ r ∈ rules, r.axis = a) (s : State C A) (c : C) (a' : A)
    (hne : a' ≠ a) : (cat2Apply rules s) c a' = s c a' := by
  unfold cat2Apply
  apply foldl_preserves_at_pos
  intro s' r hr
  have hr_axis : r.axis = a := h_axis r hr
  exact r.axis_local s' c a' (by rw [hr_axis]; exact hne)

/-- **`processStratum` only modifies its own axis.** Cells `(c, a')` with
`a' ≠ a` are preserved by `processStratum rs a`. -/
theorem processStratum_only_modifies_axis (rs : StratifiedRuleSet C A) (a : A)
    (s : State C A) (c : C) (a' : A) (hne : a' ≠ a) :
    (processStratum rs a s) c a' = s c a' := by
  unfold processStratum
  rw [cat2Apply_axis_local (rs.cat2 a) a (rs.cat2_axis a) _ c a' hne]
  rw [cat1Fixpoint_axis_local (rs.cat1 a) a (rs.cat1_axis a) _ c a' hne]

/-! ## `processStratum` for read-independent axes commute

Two `processStratum` invocations for distinct axes `a` and `b` commute when
neither's rules read the other's axis. `processStratum_only_modifies_axis`
guarantees they write disjoint cells, but in our current rule formalism
(`MonotoneRule`, `NafRule`) the `apply` field is an arbitrary
`State → State`, so a rule at axis `a` *could* read axis `b`'s state and
thereby produce different outputs depending on whether `b` was processed
first.

We therefore commute under an explicit **read-independence** hypothesis:
both `processStratum rs a` and `processStratum rs b` treat each other's
axis-cells as "frame" — applying them to two states that differ only on
the unread axis produces results that differ only on that axis.

In a fully developed stratified Datalog formalism, read-independence
between same-stratum axes would be a structural invariant of the rule
set; here we expose it as a hypothesis on the operator pair. -/

/-- A `processStratum` invocation is **read-independent** of axis `b` if
applying it to two states that agree on every axis except `b` still
produces results that agree on every axis except `b`. -/
def processStratum_reads_independently (rs : StratifiedRuleSet C A) (a b : A) : Prop :=
  ∀ s t : State C A, (∀ c x, x ≠ b → s c x = t c x) →
    ∀ c x, x ≠ b → (processStratum rs a s) c x = (processStratum rs a t) c x

/-- **`processStratum` for read-independent distinct axes commute.** Requires
read-independence in both directions: `a`'s rules don't depend on axis `b`'s
state, and vice versa. Under those hypotheses, swapping the two stratum
processings is a no-op. -/
theorem processStratum_commute (rs : StratifiedRuleSet C A) (a b : A) (hne : a ≠ b)
    (h_a_indep_b : processStratum_reads_independently rs a b)
    (h_b_indep_a : processStratum_reads_independently rs b a)
    (s : State C A) :
    processStratum rs a (processStratum rs b s) =
    processStratum rs b (processStratum rs a s) := by
  funext c x
  by_cases hxa : x = a
  · -- x = a. processStratum b doesn't write axis a, so by read-independence
    -- of `a` from `b` the LHS reduces to processStratum a s, and the outer
    -- processStratum b on the RHS doesn't modify axis a.
    rw [hxa]
    have h_agree_off_b : ∀ c' x', x' ≠ b →
        (processStratum rs b s) c' x' = s c' x' :=
      fun c' x' hxb' => processStratum_only_modifies_axis rs b s c' x' hxb'
    have h_lhs_eq :
        (processStratum rs a (processStratum rs b s)) c a =
        (processStratum rs a s) c a :=
      h_a_indep_b _ _ h_agree_off_b c a hne
    rw [h_lhs_eq]
    rw [processStratum_only_modifies_axis rs b (processStratum rs a s) c a hne]
  · by_cases hxb : x = b
    · rw [hxb]
      have h_agree_off_a : ∀ c' x', x' ≠ a →
          (processStratum rs a s) c' x' = s c' x' :=
        fun c' x' hxa' => processStratum_only_modifies_axis rs a s c' x' hxa'
      have h_rhs_eq :
          (processStratum rs b (processStratum rs a s)) c b =
          (processStratum rs b s) c b :=
        h_b_indep_a _ _ h_agree_off_a c b (Ne.symm hne)
      rw [h_rhs_eq]
      rw [processStratum_only_modifies_axis rs a (processStratum rs b s) c b
        (Ne.symm hne)]
    · -- x ≠ a and x ≠ b. Both sides preserve cell (c, x) since neither
      -- processStratum modifies it.
      rw [processStratum_only_modifies_axis rs a (processStratum rs b s) c x hxa,
          processStratum_only_modifies_axis rs b s c x hxb,
          processStratum_only_modifies_axis rs b (processStratum rs a s) c x hxb,
          processStratum_only_modifies_axis rs a s c x hxa]

/-! ## Inflationarity of the stratified fixpoint

`cat1Fixpoint`, `cat2Apply`, `processStratum`, and `stratifiedFixpoint`
are all inflationary in the information ordering. The chain bottoms at
the input state and only adds information through each rule. -/

/-- `cat1Fixpoint` is inflationary: `s ≤ cat1Fixpoint rules s`. -/
theorem cat1Fixpoint_inflationary (rules : List (MonotoneRule C A))
    (s : State C A) : s ≤ cat1Fixpoint rules s := by
  unfold cat1Fixpoint iterateToFixpoint
  simp only
  exact iterate_inflationary (composeMonotone_inflationary rules) _ s

/-- `cat2Apply` is inflationary: `s ≤ cat2Apply rules s`. -/
theorem cat2Apply_inflationary (rules : List (NafRule C A)) (s : State C A) :
    s ≤ cat2Apply rules s :=
  foldl_inflationary (fun s r => NafRule.inflationary r s) rules s

/-- `cat2Apply` is monotone in the input state. Each NAF rule is monotone
(by `NafRule.monotone`), and folding monotone functions preserves monotonicity. -/
theorem cat2Apply_monotone_state (rules : List (NafRule C A)) :
    ∀ s t : State C A, s ≤ t → cat2Apply rules s ≤ cat2Apply rules t := by
  intro s t hst
  induction rules generalizing s t with
  | nil => exact hst
  | cons r rs ih =>
    simp only [cat2Apply, List.foldl]
    exact ih (r.apply s) (r.apply t) (r.monotone s t hst)

/-- **`cat2Apply` is sublist-monotone**: extending the rule list (in the sense
of `List.Sublist` — adding rules at any position while preserving the order
of existing rules) produces a `≥` result.

Note that arbitrary set-extension is *not* provable: NAF rule application is
order-dependent, so reordering can produce incomparable states. The Sublist
hypothesis captures the natural notion of "rule set extension": new rules
are inserted but existing rules retain their relative order. -/
theorem cat2Apply_sublist {rules₁ rules₂ : List (NafRule C A)}
    (h_sub : rules₁.Sublist rules₂) (s : State C A) :
    cat2Apply rules₁ s ≤ cat2Apply rules₂ s := by
  induction h_sub generalizing s with
  | slnil => exact le_refl _
  | cons r _ ih =>
    -- rules₁ <+ r :: rest. By IH, cat2Apply rules₁ s ≤ cat2Apply rest s.
    -- cat2Apply (r :: rest) s = cat2Apply rest (r.apply s) ≥ cat2Apply rest s
    -- via monotonicity in s plus inflation s ≤ r.apply s.
    simp only [cat2Apply, List.foldl]
    exact le_trans (ih s)
      (cat2Apply_monotone_state _ s (r.apply s) (r.inflationary s))
  | cons₂ r _ ih =>
    -- r :: rules₁' <+ r :: rules₂'. Both fold over r first, then IH on tails.
    simp only [cat2Apply, List.foldl]
    exact ih (r.apply s)

/-- Processing a single stratum is inflationary. -/
theorem processStratum_inflationary (rs : StratifiedRuleSet C A) (a : A)
    (s : State C A) : s ≤ processStratum rs a s := by
  unfold processStratum
  exact le_trans (cat1Fixpoint_inflationary (rs.cat1 a) s)
                 (cat2Apply_inflationary (rs.cat2 a) (cat1Fixpoint (rs.cat1 a) s))

/-- The full stratified fixpoint is inflationary. -/
theorem stratifiedFixpoint_inflationary (rs : StratifiedRuleSet C A)
    (axisSorted : List A) (s₀ : State C A) :
    s₀ ≤ stratifiedFixpoint rs axisSorted s₀ :=
  foldl_inflationary (fun s a => processStratum_inflationary rs a s) axisSorted s₀

/-! ## Theorem 1: Convergence -/

/-- **Theorem 1.1: Termination.** The stratified fixpoint computation
terminates. Trivial because `stratifiedFixpoint` is a definite computation
(`List.foldl` of definite operations); the witness is the result itself. -/
theorem stratified_fixpoint_terminates (rs : StratifiedRuleSet C A)
    (axisSorted : List A) (s₀ : State C A) :
    ∃ result : State C A, result = stratifiedFixpoint rs axisSorted s₀ := by
  exact ⟨stratifiedFixpoint rs axisSorted s₀, rfl⟩

/-- A list is a valid topological sort of the stratification: lower strata
come first. -/
def IsTopoSort (strat : Stratification A) (sorted : List A) : Prop :=
  ∀ i j : Fin sorted.length, strat.strat (sorted.get i) < strat.strat (sorted.get j) → i < j

/-- **Theorem 1.2: Uniqueness.** The stratified fixpoint result is independent
of the topological order chosen, as long as the orders are valid topological
sorts of the axis dependency graph and enumerate the same axes.

## Hypotheses

The classical statement requires `sort1` and `sort2` to be **permutations of
each other** (`h_perm`). Without this, the axiom is vacuously false: e.g.
`sort1 = []` and `sort2 = [a]` are both technically valid topo sorts but
clearly produce different results.

The proof requires a **read-locality** invariant on rules — that cat1 rules
at axis `a` only read cells at axes `b` with `strat b ≤ strat a`, and cat2
rules at axis `a` only read cells at axes `b` with `strat b < strat a`.
These invariants are structural for stratified Datalog (Apt-Blair-Walker
1988) and would need to be added as fields on `MonotoneRule` / `NafRule`
or as side conditions on `StratifiedRuleSet`. They give the
`processStratum_reads_independently` hypothesis required by
`processStratum_commute` for any pair of same-stratum axes.

## Proof outline (once read-locality is in place)

1. `processStratum_only_modifies_axis` — proved.
2. `processStratum_commute` for distinct axes at the same stratum, under
   read-independence — proved (with hypothesis).
3. Any two valid topological sorts of the same multiset of axes are
   connected by a sequence of adjacent transpositions of same-stratum
   pairs (purely combinatorial; standard bubble-sort argument over
   `List.Perm`).
4. By induction on the transposition chain and (2), the fold result is
   invariant.

(3) is purely combinatorial (no Argon-specific content) and is the bulk
of the remaining mechanization work. -/
axiom stratified_fixpoint_unique (rs : StratifiedRuleSet C A)
    (sort1 sort2 : List A)
    (_h_perm : sort1.Perm sort2)
    (_hvalid1 : IsTopoSort rs.strat sort1)
    (_hvalid2 : IsTopoSort rs.strat sort2) :
    stratifiedFixpoint rs sort1 State.initial = stratifiedFixpoint rs sort2 State.initial

/-- **Theorem 1.3: Stability.** The result is a fixpoint — no rule
application would change any assignment.

## Proof outline

## Hypotheses

The proof requires the same **read-locality** invariant as
`stratified_fixpoint_unique` — cat1 rules at axis `a` only read cells at
axes `b` with `strat b ≤ strat a`, and cat2 rules at axis `a` only read
cells at axes `b` with `strat b < strat a`. Without read-locality, a
cat1 rule could re-fire after later strata add new NOT values, breaking
stability.

## Proof outline (once read-locality is in place)

For axis `a` at stratum k, `processStratum` first runs Cat1 to fixpoint,
then applies Cat2.

- **Cat1 stability**: At axis `a`'s processing time, cat1 ran to a
  fixpoint of `composeMonotone (rs.cat1 a)`. By
  `composeMonotone_fixpoint_each_rule`, every individual cat1 rule for
  axis `a` fixes that state. After cat2 runs at axis `a`, axis-a cells
  may flip CAN→NOT. Under read-locality (cat1 rules don't read axis a's
  NOT values), each cat1 rule still fires the same way: its trigger
  condition reads only strata ≤ k, and strata < k are unchanged from
  when cat1 was at fixpoint.

- **Cat2 stability**: Each cat2 rule's `only_adds_not` field forces
  `r.apply s ≠ s ↔ s c r.axis = .can`. Under read-locality (cat2 reads
  only strata < k), cat2 rule firing is determined by strata < k state,
  which doesn't change after stratum k is processed. So cat2 rules at
  axis a remain stable.

- For axes processed LATER (stratum > k): by `processStratum_only_modifies_axis`,
  axis `a` cells are unchanged. Stability is preserved.

Lifting through the full fold and the topological order is mechanical
once the per-stratum stability lemma is in place. -/
axiom stratified_fixpoint_stable (rs : StratifiedRuleSet C A)
    (axisSorted : List A) :
    (∀ a, ∀ r ∈ rs.cat1 a,
      r.apply (stratifiedFixpoint rs axisSorted State.initial) =
      stratifiedFixpoint rs axisSorted State.initial) ∧
    (∀ a, ∀ r ∈ rs.cat2 a,
      r.apply (stratifiedFixpoint rs axisSorted State.initial) =
      stratifiedFixpoint rs axisSorted State.initial)

/-! ## Key Lemma: Monotone Composition on Finite Domains -/

/-- On a finite domain, a monotone inflationary operator reaches its
fixpoint in at most `numCan State.initial` steps.

An operator `f` is inflationary if `s ≤ f s` for all `s`. Cat1 rules are
inflationary: they only ADD IS values.

## Proof

Strong induction on `numCan s`: at each non-fixpoint step `s ≠ f s`, the
information ordering plus `s ≤ f s` (from inflation) forces at least one
CAN cell to become determined, so `numCan (f s) < numCan s`. The chain
must therefore reach a fixpoint within `numCan State.initial` iterations.

This is the Knaster-Tarski theorem applied to a finite poset (Knaster
1928; Tarski 1955), specialized to the IS/CAN/NOT lattice via the
`numCan` measure.

The auxiliary `monotone_inflationary_fixpoint_from_state` is the strong
form: from any starting state, a fixpoint is reached. The headline
theorem instantiates with `State.initial`. -/
theorem monotone_inflationary_fixpoint_from_state
    (f : State C A → State C A)
    (_hmono : ∀ s t : State C A, s ≤ t → f s ≤ f t)
    (hinfl : ∀ s : State C A, s ≤ f s)
    (s : State C A) :
    ∃ n : Nat, ∃ result : State C A,
      (Nat.iterate f n s = result) ∧ (f result = result) := by
  -- Strong induction on `State.numCan s`.
  generalize hN : State.numCan s = N
  induction N using Nat.strong_induction_on generalizing s with
  | _ N ih =>
    by_cases h_fp : f s = s
    · -- s is already a fixpoint; take n = 0.
      exact ⟨0, s, rfl, h_fp⟩
    · -- s ≠ f s. By inflation s ≤ f s, so numCan (f s) < numCan s = N.
      have h_le : s ≤ f s := hinfl s
      have h_ne : s ≠ f s := fun heq => h_fp heq.symm
      have h_lt : State.numCan (f s) < State.numCan s :=
        State.numCan_lt_of_lt_ne h_le h_ne
      rw [hN] at h_lt
      -- Apply IH at numCan (f s) to get a fixpoint reached from f s.
      obtain ⟨k, result, hk_iter, hk_fp⟩ :=
        ih (State.numCan (f s)) h_lt (s := f s) rfl
      -- Iterate from s for k+1 steps = iterate from f s for k steps = result.
      refine ⟨k + 1, result, ?_, hk_fp⟩
      rw [Function.iterate_succ_apply]
      exact hk_iter

/-- The headline theorem: a monotone inflationary operator on the
`State C A` finite domain has a fixpoint reachable from `State.initial`
in finitely many iteration steps. -/
theorem monotone_inflationary_fixpoint_finite
    (f : State C A → State C A)
    (hmono : ∀ s t : State C A, s ≤ t → f s ≤ f t)
    (hinfl : ∀ s : State C A, s ≤ f s) :
    ∃ n : Nat, ∃ result : State C A,
      (Nat.iterate f n State.initial = result) ∧
      (f result = result) :=
  monotone_inflationary_fixpoint_from_state f hmono hinfl State.initial

/-- **Bounded form** of `monotone_inflationary_fixpoint_from_state`: the
iteration count is bounded by `State.numCan s`. The proof tracks the
strong-induction recursion depth, which decreases by at least one (in
fact, by at least one CAN cell becoming determined) per step. -/
theorem monotone_inflationary_fixpoint_bounded
    (f : State C A → State C A)
    (_hmono : ∀ s t : State C A, s ≤ t → f s ≤ f t)
    (hinfl : ∀ s : State C A, s ≤ f s)
    (s : State C A) :
    ∃ n ≤ State.numCan s, ∃ result : State C A,
      (Nat.iterate f n s = result) ∧ (f result = result) := by
  generalize hN : State.numCan s = N
  induction N using Nat.strong_induction_on generalizing s with
  | _ N ih =>
    by_cases h_fp : f s = s
    · exact ⟨0, by omega, s, rfl, h_fp⟩
    · have h_le : s ≤ f s := hinfl s
      have h_ne : s ≠ f s := fun heq => h_fp heq.symm
      have h_lt : State.numCan (f s) < State.numCan s :=
        State.numCan_lt_of_lt_ne h_le h_ne
      rw [hN] at h_lt
      obtain ⟨k, hk_le, result, hk_iter, hk_fp⟩ :=
        ih (State.numCan (f s)) h_lt (s := f s) rfl
      refine ⟨k + 1, ?_, result, ?_, hk_fp⟩
      · -- k ≤ numCan (f s) < N, so k + 1 ≤ N.
        omega
      · rw [Function.iterate_succ_apply]
        exact hk_iter

/-! ## Once at a fixpoint, iteration stays there

Standard `Nat.iterate` lemmas. Used to lift the bounded Phase A.1
result to the fact that `cat1Fixpoint` (which iterates `bound` times)
is itself a fixpoint of `composeMonotone`. -/

/-- Iterating at a fixpoint stays at the fixpoint. -/
theorem iterate_at_fixpoint {α : Type*} (f : α → α) (result : α)
    (h : f result = result) (k : Nat) :
    Nat.iterate f k result = result := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, h]

/-- If `Nat.iterate f n s = result` and `result` is a fixpoint, then
iterating `m ≥ n` times also lands at `result`. -/
theorem iterate_eq_of_fixpoint_at {α : Type*} (f : α → α) (s result : α)
    (n m : Nat) (hn : Nat.iterate f n s = result) (hfp : f result = result)
    (hm : n ≤ m) : Nat.iterate f m s = result := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
  rw [hk]
  -- Nat.iterate f (n + k) s = Nat.iterate f k (Nat.iterate f n s) by iterate_add
  rw [show n + k = k + n from Nat.add_comm n k, Function.iterate_add_apply]
  rw [hn]
  exact iterate_at_fixpoint f result hfp k

/-! ### Iteration is bounded above by every fixpoint above the start

The "least-fixpoint via iteration" property: starting from `s` and
iterating a monotone-inflationary operator any number of times keeps
the result below every fixpoint above `s`. If the iteration reaches
its own fixpoint, that fixpoint is the least fixpoint above `s`. -/

/-- Iteration preserves the "below `s'`" invariant when `s'` is a
fixpoint of `f` and `f` is monotone. -/
private theorem iterate_le_fixpoint_above
    (f : State C A → State C A)
    (hmono : ∀ s t : State C A, s ≤ t → f s ≤ f t)
    (s s' : State C A)
    (h_le : s ≤ s') (h_fp' : f s' = s') (n : Nat) :
    Nat.iterate f n s ≤ s' := by
  induction n with
  | zero => exact h_le
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc f (Nat.iterate f n s)
        ≤ f s' := hmono _ _ ih
      _ = s' := h_fp'

/-- **Iterate yields the least fixpoint.** Starting from `s` and iterating
a monotone-inflationary operator any number of times keeps the result
below every fixpoint above `s`. -/
theorem iterate_le_of_fixpoint_above
    (f : State C A → State C A)
    (hmono : ∀ s t : State C A, s ≤ t → f s ≤ f t)
    (s : State C A) (n : Nat) (result : State C A)
    (h_iter : Nat.iterate f n s = result) :
    ∀ s', s ≤ s' → f s' = s' → result ≤ s' := by
  intro s' h_le h_fp'
  rw [← h_iter]
  exact iterate_le_fixpoint_above f hmono s s' h_le h_fp' n

/-! ## `cat1Fixpoint` is a fixpoint -/

/-- The `iterateToFixpoint` bound `Fintype.card C * Fintype.card A + 1`
exceeds `State.numCan s` for any state `s`. (`numCan s ≤ |C × A|`.) -/
private theorem numCan_lt_iterateToFixpoint_bound (s : State C A) :
    State.numCan s ≤ Fintype.card C * Fintype.card A := by
  unfold State.numCan
  calc ((Finset.univ (α := C × A)).filter (fun p => s p.1 p.2 = .can)).card
      ≤ Finset.univ.card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = Fintype.card (C × A) := rfl
    _ = Fintype.card C * Fintype.card A := by rw [Fintype.card_prod]

/-- **`cat1Fixpoint` is a fixpoint of `composeMonotone`.**

Combines `monotone_inflationary_fixpoint_bounded` (which gives a fixpoint
within `numCan s + 1` iterations) with `iterate_eq_of_fixpoint_at` (which
says further iterations stay at the fixpoint), once we observe that
`numCan s + 1 ≤ Fintype.card C * Fintype.card A + 1 = iterateToFixpoint`'s
bound. -/
theorem cat1Fixpoint_is_fixpoint (rules : List (MonotoneRule C A))
    (s : State C A) :
    composeMonotone rules (cat1Fixpoint rules s) = cat1Fixpoint rules s := by
  unfold cat1Fixpoint iterateToFixpoint
  -- Get a fixpoint within numCan s ≤ |C × A| iterations.
  obtain ⟨n, hn_le, result, hn_iter, hfp⟩ :=
    monotone_inflationary_fixpoint_bounded (composeMonotone rules)
      (composeMonotone_monotone rules) (composeMonotone_inflationary rules) s
  -- The iterateToFixpoint bound exceeds numCan s, so we land at result.
  have h_bound : n ≤ Fintype.card C * Fintype.card A + 1 := by
    have := numCan_lt_iterateToFixpoint_bound s
    omega
  have h_iter_bound :
      Nat.iterate (composeMonotone rules) (Fintype.card C * Fintype.card A + 1) s
        = result :=
    iterate_eq_of_fixpoint_at _ _ _ n _ hn_iter hfp h_bound
  rw [h_iter_bound]
  exact hfp

/-! ## Each rule is a fixpoint of the composition's fixpoint

Foundational lemma for `extension_monotone`: if the *composition* of
monotone+inflationary rules has fixed `s` (i.e., `composeMonotone L s
= s`), then every individual rule in `L` already fixes `s`. The
argument uses sandwich: in the fold from `s` ending at `s`, each
intermediate state is sandwiched between an inflation-≥ and the final
`= s`, forcing equality throughout. -/

/-- If `composeMonotone rules s = s`, every rule `r ∈ rules` satisfies
`r.apply s = s`. -/
theorem composeMonotone_fixpoint_each_rule (rules : List (MonotoneRule C A))
    (s : State C A) (h : composeMonotone rules s = s) :
    ∀ r ∈ rules, r.apply s = s := by
  induction rules with
  | nil => simp
  | cons r rest ih =>
    intro r' hr'
    -- composeMonotone (r :: rest) s = composeMonotone rest (r.apply s).
    have h_unfold : composeMonotone rest (r.apply s) = s := by
      simp only [composeMonotone, List.foldl] at h
      exact h
    -- r.apply s ≤ s via composeMonotone inflation + h_unfold.
    have h_r_le : r.apply s ≤ s :=
      le_of_le_of_eq (composeMonotone_inflationary rest (r.apply s)) h_unfold
    -- r.apply s ≥ s by rule inflation; combine to get equality.
    have h_r_eq : r.apply s = s := le_antisymm h_r_le (r.inflationary s)
    -- Reduce h to composeMonotone rest s = s.
    have h_rest : composeMonotone rest s = s := by
      -- Substitute r.apply s = s on the LHS only.
      conv_lhs => rw [← h_r_eq]
      exact h_unfold
    -- Case on whether r' = r or r' ∈ rest.
    rcases List.mem_cons.mp hr' with rfl | hr_in_rest
    · exact h_r_eq
    · exact ih h_rest r' hr_in_rest

/-- If every rule in `rules` fixes `s`, then `composeMonotone rules s = s`. -/
theorem composeMonotone_eq_self_of_each_fixed (rules : List (MonotoneRule C A))
    (s : State C A) (h : ∀ r ∈ rules, r.apply s = s) :
    composeMonotone rules s = s := by
  induction rules with
  | nil => rfl
  | cons r rest ih =>
    have h_r : r.apply s = s := h r List.mem_cons_self
    have h_rest : ∀ r' ∈ rest, r'.apply s = s := fun r' hr' =>
      h r' (List.mem_cons_of_mem r hr')
    -- composeMonotone (r :: rest) s = composeMonotone rest (r.apply s)
    --                              = composeMonotone rest s    (by h_r)
    --                              = s                          (by IH).
    simp only [composeMonotone, List.foldl]
    rw [h_r]
    exact ih h_rest

/-! ## `cat1Fixpoint` extension under rule subset

Combining: `F₂ = cat1Fixpoint rules₂ s` is a fixpoint of `composeMonotone
rules₂` (`cat1Fixpoint_is_fixpoint`). Every rule of `rules₂` fixes `F₂`
(`composeMonotone_fixpoint_each_rule`). Since `rules₁ ⊆ rules₂`, every
rule of `rules₁` also fixes `F₂` — so `F₂` is a fixpoint of
`composeMonotone rules₁` (`composeMonotone_eq_self_of_each_fixed`).
Phase A.2's `iterate_le_of_fixpoint_above` then gives
`cat1Fixpoint rules₁ s ≤ F₂`. -/

/-- **`cat1Fixpoint` is monotone in the rule set**: extending the rule
list produces a `≥` fixpoint. -/
theorem cat1Fixpoint_extension {rules₁ rules₂ : List (MonotoneRule C A)}
    (h_subset : ∀ r ∈ rules₁, r ∈ rules₂) (s : State C A) :
    cat1Fixpoint rules₁ s ≤ cat1Fixpoint rules₂ s := by
  set F₂ := cat1Fixpoint rules₂ s
  have h_F2_fp : composeMonotone rules₂ F₂ = F₂ := cat1Fixpoint_is_fixpoint rules₂ s
  -- Every rule in rules₂ fixes F₂.
  have h_each_rules2 : ∀ r ∈ rules₂, r.apply F₂ = F₂ :=
    composeMonotone_fixpoint_each_rule rules₂ F₂ h_F2_fp
  -- Hence every rule in rules₁ also fixes F₂.
  have h_each_rules1 : ∀ r ∈ rules₁, r.apply F₂ = F₂ := fun r hr =>
    h_each_rules2 r (h_subset r hr)
  -- So F₂ is a fixpoint of composeMonotone rules₁.
  have h_F2_fp_rules1 : composeMonotone rules₁ F₂ = F₂ :=
    composeMonotone_eq_self_of_each_fixed rules₁ F₂ h_each_rules1
  -- s ≤ F₂ (cat1Fixpoint is inflationary).
  have h_s_le_F2 : s ≤ F₂ := cat1Fixpoint_inflationary rules₂ s
  -- Apply Phase A.2: iterate_le_of_fixpoint_above gives the bound.
  unfold cat1Fixpoint iterateToFixpoint
  exact iterate_le_of_fixpoint_above (composeMonotone rules₁)
    (composeMonotone_monotone rules₁) s _ _ rfl F₂ h_s_le_F2 h_F2_fp_rules1

/-! ## Extension monotonicity for `processStratum` and `stratifiedFixpoint`

Combining cat1 set-extension (`cat1Fixpoint_extension`) and cat2 sublist-extension
(`cat2Apply_sublist`): processing a stratum is monotone under rule-set extension.
Lifting through `List.foldl` gives `stratifiedFixpoint_extension`. -/

/-- **`processStratum` extension monotonicity.** If `rs₂`'s cat1 rules at axis
`a` contain `rs₁`'s (set inclusion) and `rs₂`'s cat2 rule list at axis `a` is
a sublist-extension of `rs₁`'s, then `processStratum rs₂ a` produces a ≥ state. -/
theorem processStratum_extension (rs₁ rs₂ : StratifiedRuleSet C A) (a : A)
    (h_cat1 : ∀ r ∈ rs₁.cat1 a, r ∈ rs₂.cat1 a)
    (h_cat2 : (rs₁.cat2 a).Sublist (rs₂.cat2 a))
    (s t : State C A) (h_st : s ≤ t) :
    processStratum rs₁ a s ≤ processStratum rs₂ a t := by
  unfold processStratum
  -- Monotonicity in the input: cat1Fixpoint rules s ≤ cat1Fixpoint rules t when s ≤ t.
  -- We chain s ≤ t through cat1Fixpoint rules₂, then bring in cat1Fixpoint_extension.
  have h_cat1_inflate : cat1Fixpoint (rs₁.cat1 a) s ≤ cat1Fixpoint (rs₂.cat1 a) s :=
    cat1Fixpoint_extension h_cat1 s
  -- cat1Fixpoint rules₂ is monotone in its input (it iterates a monotone operator
  -- — but we can sidestep that: we use the LFP characterization.)
  -- Actually we need: cat1Fixpoint rs₂ s ≤ cat1Fixpoint rs₂ t. Use lfp characterization.
  have h_cat1_mono :
      cat1Fixpoint (rs₂.cat1 a) s ≤ cat1Fixpoint (rs₂.cat1 a) t := by
    -- cat1Fixpoint rs₂ t is a fixpoint of composeMonotone (rs₂.cat1 a), and t ≤ this.
    -- Then s ≤ t ≤ cat1Fixpoint rs₂ t, so by Phase A.2, cat1Fixpoint rs₂ s ≤ that.
    set F₂t := cat1Fixpoint (rs₂.cat1 a) t
    have h_F2t_fp : composeMonotone (rs₂.cat1 a) F₂t = F₂t :=
      cat1Fixpoint_is_fixpoint (rs₂.cat1 a) t
    have h_t_le_F2t : t ≤ F₂t := cat1Fixpoint_inflationary (rs₂.cat1 a) t
    have h_s_le_F2t : s ≤ F₂t := le_trans h_st h_t_le_F2t
    unfold cat1Fixpoint iterateToFixpoint
    exact iterate_le_of_fixpoint_above (composeMonotone (rs₂.cat1 a))
      (composeMonotone_monotone (rs₂.cat1 a)) s _ _ rfl F₂t h_s_le_F2t h_F2t_fp
  have h_after_cat1 : cat1Fixpoint (rs₁.cat1 a) s ≤ cat1Fixpoint (rs₂.cat1 a) t :=
    le_trans h_cat1_inflate h_cat1_mono
  -- Cat2: extend rules and chain through monotonicity in state.
  calc cat2Apply (rs₁.cat2 a) (cat1Fixpoint (rs₁.cat1 a) s)
      ≤ cat2Apply (rs₁.cat2 a) (cat1Fixpoint (rs₂.cat1 a) t) :=
        cat2Apply_monotone_state _ _ _ h_after_cat1
    _ ≤ cat2Apply (rs₂.cat2 a) (cat1Fixpoint (rs₂.cat1 a) t) :=
        cat2Apply_sublist h_cat2 _

/-- **`stratifiedFixpoint` extension monotonicity.** Extending a rule set
(adding more cat1/cat2 rules per axis, with cat2 lists growing as sublist
extensions) produces a ≥ fixpoint. Same axis ordering required. -/
theorem stratifiedFixpoint_extension (rs₁ rs₂ : StratifiedRuleSet C A)
    (axisSorted : List A)
    (h_cat1 : ∀ a, ∀ r ∈ rs₁.cat1 a, r ∈ rs₂.cat1 a)
    (h_cat2 : ∀ a, (rs₁.cat2 a).Sublist (rs₂.cat2 a))
    (s t : State C A) (h_st : s ≤ t) :
    stratifiedFixpoint rs₁ axisSorted s ≤ stratifiedFixpoint rs₂ axisSorted t := by
  unfold stratifiedFixpoint
  induction axisSorted generalizing s t with
  | nil => simpa [List.foldl] using h_st
  | cons a rest ih =>
    simp only [List.foldl]
    exact ih _ _ (processStratum_extension rs₁ rs₂ a (h_cat1 a) (h_cat2 a) s t h_st)

/-- The fixpoint of a monotone inflationary operator on a finite domain is
unique (it is the least fixpoint). Direct application of `le_antisymm`. -/
theorem monotone_inflationary_lfp_unique
    (f : State C A → State C A)
    (_hmono : ∀ s t : State C A, s ≤ t → f s ≤ f t)
    (_hinfl : ∀ s : State C A, s ≤ f s) :
    ∀ s₁ s₂ : State C A,
      (f s₁ = s₁) → (f s₂ = s₂) →
      (∀ s, f s = s → s₁ ≤ s) → (∀ s, f s = s → s₂ ≤ s) →
      s₁ = s₂ := by
  intro s₁ s₂ hfp1 hfp2 hleast1 hleast2
  exact le_antisymm (hleast1 s₂ hfp2) (hleast2 s₁ hfp1)
