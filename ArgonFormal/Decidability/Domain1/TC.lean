/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

/-!
# Transitive Closure Decidability on Finite Types

On a finite type with a decidable relation, the transitive closure is decidable.
This is the key lemma enabling `hasAnc` and `hasDesc` in the Domain 1 decidability
proof: we can decide whether one concept is a TC-ancestor/descendant of another.

## Approach

We compute reachability iteratively: starting from concept `a`, expand the set of
reachable concepts by one step of the relation, repeating at most `|C|` times.
Termination: the reachable set is monotonically growing and bounded by `Finset.univ`,
so it stabilizes in at most `|C|` steps.

## Main results

- `transGenDecidable` — `Relation.TransGen r` is decidable on `Fintype C`
-/

namespace ArgonDecidability

variable {C : Type} [Fintype C] [DecidableEq C]
variable {r : C → C → Prop} [DecidableRel r]

/-- One-step expansion: add all elements reachable in one `r`-step from `s`. -/
private def stepReachable (r : C → C → Prop) [DecidableRel r] (s : Finset C) : Finset C :=
  s ∪ s.biUnion (fun a => Finset.univ.filter (fun b => r a b))

/-- Iterated reachability: expand `n` times from initial set. -/
private def iterReachable (r : C → C → Prop) [DecidableRel r]
    (s : Finset C) : Nat → Finset C
  | 0     => s
  | n + 1 => stepReachable r (iterReachable r s n)

/-- The reachable set from a single element after `|C|` expansions. -/
private def reachableFrom (r : C → C → Prop) [DecidableRel r] (a : C) : Finset C :=
  iterReachable r (Finset.univ.filter (fun b => r a b)) (Fintype.card C)

/-- Generalized soundness: if every element of `s` is `TransGen`-reachable from
`a`, then every element of `iterReachable r s n` is too. -/
private theorem iterReachable_sound (a : C) (s : Finset C) (n : Nat) (b : C)
    (hs : ∀ x ∈ s, Relation.TransGen r a x)
    (hb : b ∈ iterReachable r s n) :
    Relation.TransGen r a b := by
  induction n generalizing b with
  | zero =>
    -- iterReachable r s 0 = s
    simp only [iterReachable] at hb
    exact hs b hb
  | succ n ih =>
    -- iterReachable r s (n+1) = stepReachable r (iterReachable r s n)
    -- which is `prev ∪ prev.biUnion (Finset.univ.filter (r c))`.
    simp only [iterReachable, stepReachable, Finset.mem_union, Finset.mem_biUnion,
               Finset.mem_filter, Finset.mem_univ, true_and] at hb
    rcases hb with h_prev | ⟨c, hc_prev, hc_step⟩
    · -- b was already in the previous iteration; apply IH.
      exact ih b h_prev
    · -- b was newly reachable from some c ∈ prev via `r c b`.
      have hac : Relation.TransGen r a c := ih c hc_prev
      exact hac.tail hc_step

/-- Soundness: if `b ∈ reachableFrom r a`, then `TransGen r a b`.

The initial set is `Finset.univ.filter (r a)` — every element x in it satisfies
`r a x`, so by `TransGen.single`, `TransGen r a x`. The generalized
`iterReachable_sound` then carries this through every iteration. -/
private theorem reachableFrom_sound (a b : C) (h : b ∈ reachableFrom r a) :
    Relation.TransGen r a b := by
  apply iterReachable_sound (r := r) a (Finset.univ.filter (fun b => r a b))
    (Fintype.card C) b
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact Relation.TransGen.single hx
  · exact h

/-- iterReachable is monotone in the iteration count: more iterations only add
elements, never remove. Direct from `stepReachable`'s `s ⊆ stepReachable r s`. -/
private theorem iterReachable_mono (s : Finset C) (n m : Nat) (hnm : n ≤ m) :
    iterReachable r s n ⊆ iterReachable r s m := by
  induction m with
  | zero =>
    -- m = 0 forces n = 0.
    have hn : n = 0 := Nat.le_zero.mp hnm
    rw [hn]
  | succ m ih =>
    by_cases h : n ≤ m
    · -- n ≤ m, transitivity.
      refine subset_trans (ih h) ?_
      simp only [iterReachable, stepReachable]
      exact Finset.subset_union_left
    · -- ¬ n ≤ m and n ≤ m+1 means n = m+1.
      have h_eq : n = m + 1 := Nat.le_antisymm hnm (Nat.lt_of_not_le h)
      rw [h_eq]

/-- Existence: TransGen-reachability implies membership in `iterReachable` at
*some* step. We make this a separate lemma because the witness step count is
implicit in the TransGen-derivation depth. -/
private theorem exists_iter_step (a b : C) (h : Relation.TransGen r a b) :
    ∃ n, b ∈ iterReachable r (Finset.univ.filter (fun b => r a b)) n := by
  induction h with
  | single hab =>
    -- r a b → b ∈ initial filter → b ∈ iterReachable _ 0.
    refine ⟨0, ?_⟩
    simp only [iterReachable, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hab
  | tail _ hcb ih =>
    -- IH gives n with c ∈ iterReachable _ n. One more step puts b in iterReachable _ (n+1).
    obtain ⟨n, hc⟩ := ih
    refine ⟨n + 1, ?_⟩
    simp only [iterReachable, stepReachable, Finset.mem_union, Finset.mem_biUnion,
               Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inr ⟨_, hc, hcb⟩

/-! ### Saturation: the chain stabilizes within `Fintype.card C` steps

The chain `iterReachable s 0 ⊆ iterReachable s 1 ⊆ ...` is bounded by
`Finset.univ`, so it stabilizes within `Fintype.card C` iterations.
Proof structure:

1. `iterReachable_constant_after_fixpoint`: once a step's iter is equal
   to the previous step's iter (a fixpoint of `stepReachable`), the
   chain stays constant from that point.
2. `exists_fixpoint_within_card`: at least one such fixpoint occurs
   within `Fintype.card C` iterations (by pigeonhole — strictly
   increasing chain bounded by `Fintype.card C` can have at most
   `Fintype.card C` strict steps).
3. Combining: anything reachable at any iteration is reachable at step
   `Fintype.card C`.
-/

/-- Once a step's iter equals the previous step's iter, the chain is
constant from there on. Pure functional consequence of `iterReachable`'s
definition + `stepReachable` being deterministic. -/
private theorem iterReachable_constant_after_fixpoint
    (s : Finset C) (k : Nat)
    (h : iterReachable r s (k + 1) = iterReachable r s k) :
    ∀ n ≥ k, iterReachable r s n = iterReachable r s k := by
  intro n hn
  induction n with
  | zero =>
    -- n = 0; hn : k ≤ 0 forces k = 0.
    have hk : k = 0 := Nat.le_zero.mp hn
    rw [hk]
  | succ n ih =>
    by_cases hkn : k ≤ n
    · -- IH applies; iter (n+1) = step (iter n) = step (iter k) = iter (k+1) = iter k.
      have h_n := ih hkn
      simp only [iterReachable]
      rw [show iterReachable r s n = iterReachable r s k from h_n]
      -- Goal: stepReachable r (iterReachable r s k) = iterReachable r s k.
      -- Note: iterReachable r s (k+1) = stepReachable r (iterReachable r s k) by def.
      -- And h says that = iterReachable r s k.
      exact h
    · -- ¬ k ≤ n means n + 1 = k.
      have hnk : n + 1 = k := by omega
      rw [hnk]

/-- Pigeonhole step: in any chain of Finsets bounded by `Finset.univ` of
length `M + 1`, at least two consecutive elements are equal. Specialized
to the iterReachable chain. -/
private theorem exists_fixpoint_within_card (s : Finset C) :
    ∃ k ≤ Fintype.card C,
      iterReachable r s (k + 1) = iterReachable r s k := by
  -- Suppose no fixpoint in `[0, Fintype.card C]`. Then every consecutive
  -- pair is strict, giving `Fintype.card C + 1` strict cardinality
  -- increases — contradicting the bound `card ≤ Fintype.card C`.
  by_contra h_none
  push Not at h_none
  -- h_none: ∀ k ≤ Fintype.card C, iterReachable s (k+1) ≠ iterReachable s k
  -- Combined with `iterReachable_mono`, we get strict subset at each step.
  -- Card chain: c_0 ≤ c_1 ≤ ... with c_i < c_{i+1} for i < Fintype.card C + 1.
  -- So c_(Fintype.card C + 1) ≥ c_0 + (Fintype.card C + 1) ≥ Fintype.card C + 1.
  -- But c_(Fintype.card C + 1) ≤ Fintype.card C. Contradiction.
  have h_card_bound : ∀ k, (iterReachable r s k).card ≤ Fintype.card C := by
    intro k
    exact (iterReachable r s k).card_le_univ
  have h_strict : ∀ k ≤ Fintype.card C,
      (iterReachable r s k).card < (iterReachable r s (k + 1)).card := by
    intro k hk
    have h_sub : iterReachable r s k ⊆ iterReachable r s (k + 1) :=
      iterReachable_mono s k (k + 1) (Nat.le_succ k)
    have h_ne : iterReachable r s (k + 1) ≠ iterReachable r s k := h_none k hk
    refine Finset.card_lt_card ⟨h_sub, ?_⟩
    intro h_super
    apply h_ne
    exact le_antisymm h_super h_sub
  -- The card chain has at least Fintype.card C + 1 strict increases:
  -- c_0 < c_1 < ... < c_(Fintype.card C + 1).
  -- So c_(Fintype.card C + 1) ≥ Fintype.card C + 1.
  have h_chain : ∀ k ≤ Fintype.card C + 1,
      k ≤ (iterReachable r s k).card := by
    intro k hk
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hk' : k ≤ Fintype.card C + 1 := Nat.le_of_succ_le hk
      have hk_le_C : k ≤ Fintype.card C := by omega
      have h_card_lt := h_strict k hk_le_C
      have h_ih := ih hk'
      omega
  have h_final : Fintype.card C + 1 ≤
      (iterReachable r s (Fintype.card C + 1)).card :=
    h_chain (Fintype.card C + 1) (le_refl _)
  have h_bound := h_card_bound (Fintype.card C + 1)
  omega

/-- **Saturation theorem**: anything reachable at any iteration is
reachable by step `Fintype.card C`. -/
private theorem iterReachable_saturates (a : C) (n : Nat) (b : C)
    (h : b ∈ iterReachable r (Finset.univ.filter (fun b => r a b)) n) :
    b ∈ iterReachable r (Finset.univ.filter (fun b => r a b)) (Fintype.card C) := by
  set s := Finset.univ.filter (fun b => r a b)
  -- Find a fixpoint within Fintype.card C steps; chain stabilizes there.
  obtain ⟨k, hk_le, hk_fix⟩ := exists_fixpoint_within_card s (r := r)
  -- For n ≤ Fintype.card C: by mono.
  -- For n > Fintype.card C: chain stabilized by step k ≤ Fintype.card C; both
  --   iterReachable s n and iterReachable s (Fintype.card C) equal iterReachable s k.
  by_cases h_n_le : n ≤ Fintype.card C
  · exact iterReachable_mono s n (Fintype.card C) h_n_le h
  · -- n > Fintype.card C ≥ k.
    have h_n_ge : n ≥ k := by omega
    have h_C_ge : Fintype.card C ≥ k := hk_le
    have h_iter_n := iterReachable_constant_after_fixpoint s k hk_fix n h_n_ge
    have h_iter_C := iterReachable_constant_after_fixpoint s k hk_fix
      (Fintype.card C) h_C_ge
    rw [h_iter_n] at h
    rw [h_iter_C]
    exact h

/-- Completeness: if `TransGen r a b`, then `b ∈ reachableFrom r a`.

Combines `exists_iter_step` (existence at some n) with `iterReachable_saturates`
(saturation by step `Fintype.card C`). -/
private theorem reachableFrom_complete (a b : C)
    (h : Relation.TransGen r a b) : b ∈ reachableFrom r a := by
  obtain ⟨n, hb_n⟩ := exists_iter_step a b h
  exact iterReachable_saturates a n b hb_n

/-- Transitive closure of a decidable relation on a finite type is decidable.

This is the fundamental result enabling hierarchy traversal in Domain 1:
we can decide `has_ancestor(c, P)` by checking all TC-reachable ancestors. -/
instance transGenDecidable : DecidableRel (Relation.TransGen r) :=
  fun a b =>
    if h : b ∈ reachableFrom r a then
      .isTrue (reachableFrom_sound a b h)
    else
      .isFalse (fun htg => h (reachableFrom_complete a b htg))

end ArgonDecidability
