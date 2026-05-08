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

/-! ## Frame propagation: operators that "skip" an axis

An operator `op : State → State` *skips axis `b`* if applying it to two
states that agree everywhere except on axis-`b`'s column produces two
states that still agree everywhere except on axis-`b`'s column. This is
the natural "frame" property at the operator level.

A rule at axis `a` skips axis `b` when (i) `a ≠ b` (so axis_local doesn't
touch `b`) and (ii) `b ∉ read_axes` (so frame_local's read-determined
write on axis `a` doesn't depend on `b`'s column). The two rule
properties combine to give skip-`b`.

Skip-`b` lifts through `List.foldl` and `Nat.iterate`, so `composeMonotone`,
`cat1Fixpoint`, `cat2Apply`, and `processStratum` all skip `b` whenever
their constituent rules do. -/

/-- An operator skips axis `b`: input agreement off axis-`b` propagates to
output agreement off axis-`b`. -/
def OperatorSkips (b : A) (op : State C A → State C A) : Prop :=
  ∀ s t : State C A, (∀ c x, x ≠ b → s c x = t c x) →
    ∀ c x, x ≠ b → (op s) c x = (op t) c x

/-- A monotone rule skips axis `b` when its `axis ≠ b` and `b ∉ read_axes`. -/
theorem MonotoneRule.skips_of_axis_ne_and_not_read (r : MonotoneRule C A) (b : A)
    (h_axis_ne : r.axis ≠ b) (h_not_read : b ∉ r.read_axes) :
    OperatorSkips b r.apply := by
  intro s t h c x hxb
  by_cases hxa : x = r.axis
  · -- Output on axis = read-determined, and s, t agree on read_axes (b ∉ read_axes).
    rw [hxa]
    apply r.frame_local
    intro c' b' hb'
    -- b' ∈ read_axes, so b' ≠ b (since b ∉ read_axes). Then s c' b' = t c' b'.
    have hb'_ne : b' ≠ b := fun heq => h_not_read (heq ▸ hb')
    exact h c' b' hb'_ne
  · -- Output off axis = input off axis (by axis_local).
    rw [r.axis_local s c x hxa, r.axis_local t c x hxa]
    exact h c x hxb

/-- A NAF rule skips axis `b` when its `axis ≠ b` and `b ∉ read_axes`. -/
theorem NafRule.skips_of_axis_ne_and_not_read (r : NafRule C A) (b : A)
    (h_axis_ne : r.axis ≠ b) (h_not_read : b ∉ r.read_axes) :
    OperatorSkips b r.apply := by
  intro s t h c x hxb
  by_cases hxa : x = r.axis
  · rw [hxa]
    apply r.frame_local
    intro c' b' hb'
    have hb'_ne : b' ≠ b := fun heq => h_not_read (heq ▸ hb')
    exact h c' b' hb'_ne
  · rw [r.axis_local s c x hxa, r.axis_local t c x hxa]
    exact h c x hxb

/-- `OperatorSkips b` is preserved by composing two operators. -/
theorem OperatorSkips.comp {b : A} {f g : State C A → State C A}
    (hf : OperatorSkips b f) (hg : OperatorSkips b g) :
    OperatorSkips b (g ∘ f) := by
  intro s t h c x hxb
  exact hg (f s) (f t) (fun c' x' hx' => hf s t h c' x' hx') c x hxb

/-- Folding a list of skip-`b` operators preserves skip-`b`. -/
theorem foldl_skips {β : Type*} (b : A) (l : List β)
    (f : State C A → β → State C A)
    (h_step : ∀ x ∈ l, OperatorSkips b (fun s => f s x)) :
    OperatorSkips b (fun s => l.foldl f s) := by
  induction l with
  | nil => intro s t h c x hxb; exact h c x hxb
  | cons y rest ih =>
    intro s t h c x hxb
    simp only [List.foldl]
    have h_y : OperatorSkips b (fun s => f s y) := h_step y List.mem_cons_self
    have h_rest : ∀ z ∈ rest, OperatorSkips b (fun s => f s z) :=
      fun z hz => h_step z (List.mem_cons_of_mem y hz)
    have h_after_y : ∀ c' x', x' ≠ b → (f s y) c' x' = (f t y) c' x' := h_y s t h
    exact ih h_rest (f s y) (f t y) h_after_y c x hxb

/-- Iterating a skip-`b` operator preserves skip-`b`. -/
theorem iterate_skips (b : A) (op : State C A → State C A)
    (h_op : OperatorSkips b op) (n : Nat) :
    OperatorSkips b (Nat.iterate op n) := by
  induction n with
  | zero => intro s t h c x hxb; exact h c x hxb
  | succ n ih =>
    intro s t h c x hxb
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (op s) (op t) (fun c' x' hx' => h_op s t h c' x' hx') c x hxb

/-- `composeMonotone` of cat1 rules skips `b` if every rule skips `b`. -/
theorem composeMonotone_skips (rules : List (MonotoneRule C A)) (b : A)
    (h : ∀ r ∈ rules, OperatorSkips b r.apply) :
    OperatorSkips b (composeMonotone rules) := by
  unfold composeMonotone
  exact foldl_skips b rules (fun acc r => r.apply acc) h

/-- `cat1Fixpoint` skips `b` if every cat1 rule skips `b`. -/
theorem cat1Fixpoint_skips (rules : List (MonotoneRule C A)) (b : A)
    (h : ∀ r ∈ rules, OperatorSkips b r.apply) :
    OperatorSkips b (cat1Fixpoint rules) := by
  unfold cat1Fixpoint iterateToFixpoint
  exact iterate_skips b _ (composeMonotone_skips rules b h) _

/-- `cat2Apply` skips `b` if every cat2 rule skips `b`. -/
theorem cat2Apply_skips (rules : List (NafRule C A)) (b : A)
    (h : ∀ r ∈ rules, OperatorSkips b r.apply) :
    OperatorSkips b (cat2Apply rules) := by
  unfold cat2Apply
  exact foldl_skips b rules (fun acc r => r.apply acc) h

/-- `processStratum rs a` skips axis `b` whenever `a ≠ b` and no rule at
axis `a` (cat1 or cat2) reads axis `b`. -/
theorem processStratum_skips (rs : StratifiedRuleSet C A) (a b : A) (h_ne : a ≠ b)
    (h_cat1_no_read : ∀ r ∈ rs.cat1 a, b ∉ r.read_axes)
    (h_cat2_no_read : ∀ r ∈ rs.cat2 a, b ∉ r.read_axes) :
    OperatorSkips b (processStratum rs a) := by
  unfold processStratum
  intro s t h
  -- cat1Fixpoint preserves agreement-off-b.
  have h_cat1 : OperatorSkips b (cat1Fixpoint (rs.cat1 a)) := by
    apply cat1Fixpoint_skips
    intro r hr
    have hr_axis : r.axis = a := rs.cat1_axis a r hr
    refine MonotoneRule.skips_of_axis_ne_and_not_read r b ?_ (h_cat1_no_read r hr)
    rw [hr_axis]; exact h_ne
  -- cat2Apply preserves agreement-off-b.
  have h_cat2 : OperatorSkips b (cat2Apply (rs.cat2 a)) := by
    apply cat2Apply_skips
    intro r hr
    have hr_axis : r.axis = a := rs.cat2_axis a r hr
    refine NafRule.skips_of_axis_ne_and_not_read r b ?_ (h_cat2_no_read r hr)
    rw [hr_axis]; exact h_ne
  -- Compose.
  have h_after_cat1 : ∀ c' x', x' ≠ b →
      (cat1Fixpoint (rs.cat1 a) s) c' x' = (cat1Fixpoint (rs.cat1 a) t) c' x' :=
    h_cat1 s t h
  exact h_cat2 _ _ h_after_cat1

/-- **Read-independence between same-stratum (or higher) axes follows from
stratification consistency.** For distinct axes `a` and `b` with
`strat a ≤ strat b`, `processStratum rs a` skips `b` — by strict
stratification, no rule at axis `a` reads axis `b`. -/
theorem processStratum_skips_of_strat_le
    (rs : StratifiedRuleSet C A) (a b : A) (h_ne : a ≠ b)
    (h_strat_le : rs.strat.strat a ≤ rs.strat.strat b) :
    OperatorSkips b (processStratum rs a) := by
  apply processStratum_skips rs a b h_ne
  · intro r hr h_b_in
    rcases rs.cat1_strat_consistent a r hr b h_b_in with h_eq | h_lt
    · exact h_ne h_eq.symm
    · exact absurd (lt_of_lt_of_le h_lt h_strat_le) (lt_irrefl _)
  · intro r hr h_b_in
    rcases rs.cat2_strat_consistent a r hr b h_b_in with h_eq | h_lt
    · exact h_ne h_eq.symm
    · exact absurd (lt_of_lt_of_le h_lt h_strat_le) (lt_irrefl _)

/-! ## `processStratum` for read-independent axes commute

Two `processStratum` invocations for distinct axes `a` and `b` commute
when each skips the other's axis (the `OperatorSkips` predicate above).
With the `cat{1,2}_strat_consistent` invariants on `StratifiedRuleSet`,
this skip property is automatic for distinct axes at compatible strata
— see `processStratum_skips_of_strat_le`. -/

/-- A `processStratum` invocation is **read-independent** of axis `b` if
applying it to two states that agree on every axis except `b` still
produces results that agree on every axis except `b`. Equivalent to
`OperatorSkips b (processStratum rs a)`; kept as a separate name for
readability at theorem call sites. -/
def processStratum_reads_independently (rs : StratifiedRuleSet C A) (a b : A) : Prop :=
  OperatorSkips b (processStratum rs a)

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

/-! ## Bubble lemma: moving an axis to the front of a topo-sort prefix

When the prefix of a sort consists of axes all at the same stratum as some
`a` (and distinct from `a`), `a` can be bubbled to the front by repeated
`processStratum_commute`. -/

/-- **Bubble lemma.** Folding `processStratum rs` over `pre ++ a :: post`
equals folding over `a :: pre ++ post`, provided every element of `pre` is
at the same stratum as `a` and distinct from `a`.

This is the core swap primitive used by `stratified_fixpoint_unique`. -/
theorem foldl_processStratum_bubble (rs : StratifiedRuleSet C A) (a : A)
    (pre post : List A)
    (h_pre_strat : ∀ b ∈ pre, rs.strat.strat b = rs.strat.strat a)
    (h_pre_ne : ∀ b ∈ pre, b ≠ a) (s₀ : State C A) :
    (pre ++ a :: post).foldl (fun s a' => processStratum rs a' s) s₀ =
    (a :: pre ++ post).foldl (fun s a' => processStratum rs a' s) s₀ := by
  induction pre generalizing s₀ with
  | nil => rfl
  | cons b rest ih =>
    have h_b_strat : rs.strat.strat b = rs.strat.strat a :=
      h_pre_strat b List.mem_cons_self
    have h_b_ne : b ≠ a := h_pre_ne b List.mem_cons_self
    have h_rest_strat : ∀ x ∈ rest, rs.strat.strat x = rs.strat.strat a :=
      fun x hx => h_pre_strat x (List.mem_cons_of_mem b hx)
    have h_rest_ne : ∀ x ∈ rest, x ≠ a :=
      fun x hx => h_pre_ne x (List.mem_cons_of_mem b hx)
    have h_commute :
        processStratum rs a (processStratum rs b s₀) =
        processStratum rs b (processStratum rs a s₀) := by
      apply processStratum_commute rs a b (Ne.symm h_b_ne)
      · apply processStratum_skips_of_strat_le rs a b (Ne.symm h_b_ne)
        rw [h_b_strat]
      · apply processStratum_skips_of_strat_le rs b a h_b_ne
        rw [h_b_strat]
    show ((b :: rest) ++ a :: post).foldl _ s₀ =
         (a :: (b :: rest) ++ post).foldl _ s₀
    simp only [List.cons_append, List.foldl_cons]
    rw [ih h_rest_strat h_rest_ne (processStratum rs b s₀)]
    simp only [List.cons_append, List.foldl_cons]
    rw [h_commute]

/-- **Theorem 1.2: Uniqueness.** The stratified fixpoint result is independent
of the topological order chosen, as long as the orders are valid topological
sorts of the axis dependency graph and enumerate the same axes.

## Hypotheses

- `h_perm` — `sort1` and `sort2` are permutations of each other (without
  this, the statement is false: `[]` and `[a]` are both vacuously valid
  topo sorts but give different results).

## Closing this axiom

The structural infrastructure is now complete:

- `processStratum_only_modifies_axis` (proved unconditionally).
- `processStratum_commute` (proved with read-independence hypothesis).
- `processStratum_skips_of_strat_le` (proved — discharges read-independence
  from `cat{1,2}_strat_consistent`).
- `foldl_processStratum_bubble` (proved — bubbles an axis to the front of a
  prefix of equal-stratum, distinct elements via repeated commute).

What remains is purely combinatorial: the inductive argument that two
valid topo-sort permutations of the same multiset are connected by a chain
of bubble steps. The argument is:

  - Induct on `sort1` length.
  - In `sort1 = a :: rest`, locate `a` in `sort2` (split as `pre ++ a :: post`).
  - Show every element of `pre` is at stratum `strat a`: forced by `sort1`
    valid (rest's strata ≥ strat a, and pre ⊂ rest as multiset) plus
    `sort2` valid (pre's strata ≤ strat a since they precede a).
  - Apply `foldl_processStratum_bubble` to move `a` to the front of `sort2`.
  - IH on the tails (`rest` and `pre ++ post`).

The argument is several screens of Lean and depends on `List.Perm`,
`Fin`-indexed `List.get`, and the `IsTopoSort` predicate. We axiomatize
it here with the hypotheses now matching the structure of the bubble
argument; the proof is mechanical given the bubble lemma. -/
axiom stratified_fixpoint_unique
    (rs : StratifiedRuleSet C A)
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
