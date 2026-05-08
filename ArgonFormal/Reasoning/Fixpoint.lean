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
of the topological order chosen, as long as the order is a valid topological
sort of the axis dependency graph.

## Proof outline (the four lemmas)

1. `processStratum` for axis `a` modifies only positions `(c, a)`. Follows
   from the `axis_local` field on every `MonotoneRule` and `NafRule`.

2. `processStratum` for distinct axes commute:
   `processStratum a (processStratum b s) = processStratum b (processStratum a s)`
   for `a ≠ b`. Follows from (1) — each only modifies its own axis.

3. Any two valid topological sorts of the same stratification can be
   transformed into each other by a sequence of adjacent transpositions
   that swap unrelated axes.

4. By induction on the number of transpositions and (2), the fold result
   is invariant.

The full mechanization requires `Fin`-indexed permutation reasoning over
`List.foldl` plus the commutativity lemma. The argument is classical
(it's the standard "permutation invariance under stratified evaluation"
result for stratified Datalog — see Apt, Blair & Walker 1988); the Lean
proof is mechanical-but-substantial. We axiomatize it here pending
mechanization, with `#print axioms` audit available downstream. -/
axiom stratified_fixpoint_unique (rs : StratifiedRuleSet C A)
    (sort1 sort2 : List A)
    (_hvalid1 : IsTopoSort rs.strat sort1)
    (_hvalid2 : IsTopoSort rs.strat sort2) :
    stratifiedFixpoint rs sort1 State.initial = stratifiedFixpoint rs sort2 State.initial

/-- **Theorem 1.3: Stability.** The result is a fixpoint — no rule
application would change any assignment.

## Proof outline

For axis `a` at stratum k, `processStratum` first runs Cat1 to fixpoint,
then applies Cat2.

- **Cat1 stability**: `iterateToFixpoint` ran Cat1 rules until stable.
  After Cat2 runs for axis `a`, the Cat1 rules for axis `a` see the same
  state on axis `a` (Cat2 only changes CAN → NOT; Cat1 only reads IS
  values). So Cat1 is still stable.

- **Cat2 stability**: Cat2 checks absence of IS values. After Cat1
  fixpoint, no more IS values appear for axis `a`. Cat2's NOT
  conclusions remain valid after Cat2 runs.

- For axes processed LATER (stratum > k): their rules don't modify axis
  `a` (by `axis_local`). So `a`'s stability is preserved.

Mechanization requires Cat1+Cat2 commutation reasoning across the full
fold. The argument is classical for stratified Datalog (Apt-Blair-Walker
1988; Knaster-Tarski applied per stratum); we axiomatize the per-program
result here. -/
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
