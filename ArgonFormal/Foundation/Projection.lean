/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.Foundation.LatticeContext

/-!
# Projection Morphisms — FDE → K3 with Policy Parameters

When an FDE value (the result of cross-source aggregation, e.g. a federated
standpoint query) flows into a K3-typed consumer (refinement membership, rule
body, single-standpoint query), the inconsistent value `both` must be resolved.
Argon does not silently collapse `both` into `can` — every projection carries
an **explicit policy** that the user picks. This is the fail-closed convention:
the type system makes the projection visible at the source.

## The four built-in policies

- **`collapseToUnknown`** — `both` → `can`. Treats source disagreement as
  "we don't know yet." Most common; the natural choice when downstream logic
  is fail-closed and unknown is acceptable.
- **`treatAsError`** — `both` → fail (modeled here as `Option.none`). For
  contexts where source disagreement should immediately surface as a
  diagnostic.
- **`preferIs`** — `both` → `is`. Use when the standpoint's priority lattice
  declares T-evidence to win.
- **`preferNot`** — `both` → `not`. Symmetric. Use when F-evidence wins.

The `preferIs`/`preferNot` policies are the simplest priority-lattice case;
richer policies (resolve via a per-standpoint priority order) lift on top of
this surface and are not formalized in this file.

## What's proved

For each policy:

1. The projection is the **identity on K3 inputs** (consistent inputs round-trip
   through the projection unchanged).
2. The projection is **total** for non-error policies (returns `Some _`).
3. The K3 ↪ FDE embedding (`Truth4.ofMetaValue`) followed by projection (with
   any policy) recovers the original `MetaValue` — the embedding is a section
   of every projection.
4. Composition with `treatAsError` produces `Some _` exactly on K3 inputs.

## What is NOT in this file

These are *value-level* projections. The corresponding *type-level* commitment
— that an FDE → K3 conversion in Argon source code requires an explicit
projection — is a typechecker rule, not a theorem. The soundness theorems
here are the witness that the typechecker rule is enforceable.

The federation operation that produces FDE values (information join across
multiple sources) lives in `Federation.lean`.
-/

namespace Truth4

/-! ## Projection policy -/

/-- A policy for resolving the inconsistent value `both` when projecting from
the FDE lattice context to the K3 lattice context. -/
inductive ProjectionPolicy where
  /-- `both` → `can`. Drop source-level disagreement to "no info." -/
  | collapseToUnknown : ProjectionPolicy
  /-- `both` → fail. Surface the disagreement as a downstream error. -/
  | treatAsError : ProjectionPolicy
  /-- `both` → `is`. T-side wins in priority resolution. -/
  | preferIs : ProjectionPolicy
  /-- `both` → `not`. F-side wins in priority resolution. -/
  | preferNot : ProjectionPolicy
  deriving DecidableEq, Repr

/-! ## The projection itself -/

/-- Project an FDE value to a K3 value (`MetaValue`) under the given policy.
Returns `Option MetaValue` because `treatAsError` may fail; `none` represents
the error path. -/
def project (policy : ProjectionPolicy) : Truth4 → Option MetaValue
  | .is   => some .is
  | .not  => some .not
  | .can  => some .can
  | .both =>
    match policy with
    | .collapseToUnknown => some .can
    | .treatAsError      => none
    | .preferIs          => some .is
    | .preferNot         => some .not

/-! ## Identity on K3 inputs -/

/-- For any K3 input, every policy returns the underlying K3 value. The choice
of policy matters only for `both`-valued inputs. -/
theorem project_inK3 (policy : ProjectionPolicy) (v : Truth4) (h : v.inK3) :
    project policy v = some (toMetaValue v h) := by
  cases v with
  | is   => rfl
  | not  => rfl
  | can  => rfl
  | both => exact absurd h (by simp [inK3, isConsistent])

/-- The embedding `MetaValue ↪ Truth4` is a section of every projection: every
policy recovers the original `MetaValue` after embedding. -/
theorem project_ofMetaValue (policy : ProjectionPolicy) (m : MetaValue) :
    project policy (ofMetaValue m) = some m := by
  cases m <;> rfl

/-! ## Totality for non-error policies -/

/-- The `collapseToUnknown` projection is total: it never returns `none`. -/
theorem project_collapseToUnknown_total (v : Truth4) :
    ∃ m, project .collapseToUnknown v = some m := by
  cases v with
  | is   => exact ⟨.is, rfl⟩
  | not  => exact ⟨.not, rfl⟩
  | can  => exact ⟨.can, rfl⟩
  | both => exact ⟨.can, rfl⟩

/-- The `preferIs` projection is total. -/
theorem project_preferIs_total (v : Truth4) :
    ∃ m, project .preferIs v = some m := by
  cases v with
  | is   => exact ⟨.is, rfl⟩
  | not  => exact ⟨.not, rfl⟩
  | can  => exact ⟨.can, rfl⟩
  | both => exact ⟨.is, rfl⟩

/-- The `preferNot` projection is total. -/
theorem project_preferNot_total (v : Truth4) :
    ∃ m, project .preferNot v = some m := by
  cases v with
  | is   => exact ⟨.is, rfl⟩
  | not  => exact ⟨.not, rfl⟩
  | can  => exact ⟨.can, rfl⟩
  | both => exact ⟨.not, rfl⟩

/-- The `treatAsError` projection succeeds **iff** the input is in the K3
fragment. This characterizes the "fail-closed" property: the only way to
"escape" the `treatAsError` projection is to be already-consistent. -/
theorem project_treatAsError_iff (v : Truth4) :
    (∃ m, project .treatAsError v = some m) ↔ v.inK3 := by
  cases v <;> simp [project, inK3, isConsistent]

/-! ## Output values are bounded by policy -/

/-- `collapseToUnknown` never produces `is`-valued or `not`-valued output from
a `both` input. Useful when reasoning about which policies preserve which
invariants. -/
theorem project_collapseToUnknown_both : project .collapseToUnknown .both = some .can := rfl

/-- `treatAsError` is the *only* projection policy that fails on `both`. -/
theorem project_fails_iff (policy : ProjectionPolicy) (v : Truth4) :
    project policy v = none ↔ (v = .both ∧ policy = .treatAsError) := by
  cases v <;> cases policy <;> simp [project]

/-! ## Composition: K3 ↪ FDE ↪ K3 round-trip

The headline theorem: starting from a `MetaValue`, embedding into `Truth4`,
then projecting back with any policy, recovers the original `MetaValue`.
This is the load-bearing soundness statement for "K3 contexts are not
weakened by passing through FDE." -/

/-- **Round-trip soundness:** `project policy (ofMetaValue m) = some m` for
every policy and every `MetaValue`. The K3 ↪ FDE ↪ K3 path is identity. -/
theorem roundtrip_K3_FDE_K3 (policy : ProjectionPolicy) (m : MetaValue) :
    project policy (ofMetaValue m) = some m :=
  project_ofMetaValue policy m

/-! ## Projection respects truth-side operations under collapse policy

The `collapseToUnknown` policy commutes with truth-side operations on K3
inputs. Concretely: projecting after a truth meet equals truth-meeting after
projection (modulo the option monad). This is the analogue of "embedding
preserves operations" but in the projection direction.

These lemmas are needed for `Federation.lean` when we prove that federated
queries projected back to K3 still satisfy K3 algebraic laws. -/

/-- Helper: lift a binary K3 operation through the option monad. -/
private def liftOp2 (op : MetaValue → MetaValue → MetaValue) :
    Option MetaValue → Option MetaValue → Option MetaValue
  | some a, some b => some (op a b)
  | _, _ => none

/-- The K3 fragment defines a `MetaValue` truth meet via the projection. -/
def metaTruthMeet (m₁ m₂ : MetaValue) : MetaValue :=
  (project .collapseToUnknown
    (truthMeet (ofMetaValue m₁) (ofMetaValue m₂))).getD .can

/-- Truth meet via the projection is independent of the chosen policy *on K3
inputs* — because the result of truth-meeting two K3 values is itself K3
(closure theorem). -/
theorem metaTruthMeet_policy_invariant (policy : ProjectionPolicy) (m₁ m₂ : MetaValue) :
    project policy (truthMeet (ofMetaValue m₁) (ofMetaValue m₂)) =
    some (metaTruthMeet m₁ m₂) := by
  -- Truth meet of K3 inputs stays in K3 (proved in `LatticeContext.lean`).
  -- Therefore every policy returns the same K3 value.
  have h_inK3 : (truthMeet (ofMetaValue m₁) (ofMetaValue m₂)).inK3 :=
    truthMeet_inK3 (ofMetaValue_inK3 m₁) (ofMetaValue_inK3 m₂)
  rw [project_inK3 policy _ h_inK3]
  -- The `metaTruthMeet` definition uses `collapseToUnknown`, but by closure the
  -- value is already in K3 so all policies agree.
  cases m₁ <;> cases m₂ <;> rfl

end Truth4
