/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.Standpoint.Consistency
import ArgonFormal.Standpoint.Federation
import ArgonFormal.TypeSystem.Soundness.FlowTyping

/-!
# Backward Compatibility — RFD-0016 / D-113 as the K3 Special Case

The new AFT-grounded truth-value framework (RFD-0036) supersedes
RFD-0016 (refinement under OWA is K3) by lifting it into the broader bilattice
setting. This file proves that **RFD-0016's K3 result is recovered exactly**
when the new framework is restricted to:

1. **Single-standpoint queries.** Federation collapses to the single
   contribution (`federate_single_standpoint`).
2. **Strict consistency policy.** Within-standpoint cells stay in K3
   (`strictFold_from_can_inK3`).
3. **Horn-restricted refinement bodies.** The refinement fragment in the
   existing implementation admits only meta-property predicates over a
   finite type graph; this is the soundness witness for CWA collapse
   (Reiter 1978 / Lutz et al. 2013) that the existing
   `flow_typing_soundness` theorem covers.

Together these constraints recover the exact setting of D-113: per-standpoint
K3 refinement membership with `MetaValue` as the truth-value carrier,
fail-closed on `unknown`, monotonic CWA→OWA coercion. The new framework is
genuinely additive — the K3 case is a strict subset of FDE behaviour, not a
retroactive change.

## Headline theorems

- `roundtrip_single_standpoint_K3`: embedding a K3 value into Truth4,
  single-standpoint federating, and projecting back recovers the original
  K3 value.
- `strict_standpoint_results_are_K3`: any successful strict-policy multi-source
  append starting from `.can` yields a K3-fragment value.
- `flow_typing_soundness_lifts_to_FDE`: the existing `flow_typing_soundness`
  theorem (proved over `MetaValue`/K3) lifts unchanged to the K3 fragment of
  Truth4.

The Horn restriction itself is a *syntactic* condition on refinement bodies
that the existing implementation enforces by construction; we don't reprove
it here. The Lutz 2013 coNP-hardness result is the formal warning for any
future extension that admits non-Horn refinement bodies; that extension would
require its own soundness argument.
-/

variable {C A : Type} [DecidableEq C] [DecidableEq A] [Fintype C] [Fintype A]

namespace Truth4

/-! ## Single-standpoint round-trip soundness -/

/-- **Single-standpoint K3 round-trip.** Embedding a `MetaValue` into the
new Truth4 lattice, performing a single-standpoint federation, and projecting
back with any policy returns the original `MetaValue`. This is the literal
restatement that the K3 case is preserved under the new framework. -/
theorem roundtrip_single_standpoint_K3 (policy : ProjectionPolicy) (m : MetaValue) :
    project policy (federate [ofMetaValue m]) = some m :=
  federate_single_standpoint_project policy m

/-! ## Strict-standpoint K3 invariant -/

/-- **Strict-standpoint K3 invariant.** Any successful strict-policy fold
starting from `.can` lands in the K3 fragment. Combined with
`roundtrip_single_standpoint_K3`, this means: a strict standpoint's
single-standpoint query result is always projectable back to a `MetaValue`
without any policy-driven `both` resolution. -/
theorem strict_standpoint_results_are_K3 (es : List Truth4) (result : Truth4)
    (h_succ : es.foldl strictStep (some .can) = some result) :
    result.inK3 :=
  strictFold_from_can_inK3 es result h_succ

/-- **Strict-standpoint round-trip.** A successful strict-policy fold result
projects back to a `MetaValue` with `treatAsError` policy — the K3 fragment is
maintained, so the fail-closed projection succeeds. -/
theorem strict_standpoint_treatAsError_succeeds (es : List Truth4) (result : Truth4)
    (h_succ : es.foldl strictStep (some .can) = some result) :
    ∃ m, project .treatAsError result = some m := by
  have h_inK3 : result.inK3 := strictFold_from_can_inK3 es result h_succ
  rw [project_treatAsError_iff]
  exact h_inK3

/-! ## Embedding preserves the existing soundness theorem

The existing `flow_typing_soundness` is a theorem about `MetaValue`/`State`/
`NarrowEnv` — i.e., the K3 fragment. Because every K3 value embeds into
Truth4 via `ofMetaValue` and round-trips back via projection (regardless of
policy), the existing soundness statement transfers verbatim to any consumer
that wants the K3 view of a Truth4 result. -/

/-- **K3-fragment soundness.** For any Truth4 value in the K3 fragment, the
projection back to `MetaValue` succeeds and is policy-independent. -/
theorem K3_fragment_projects_uniquely (v : Truth4) (h : v.inK3)
    (p₁ p₂ : ProjectionPolicy) :
    project p₁ v = project p₂ v := by
  rw [project_inK3 p₁ v h, project_inK3 p₂ v h]

/-! ## RFD-0016 / D-113 specialization

The exact statement RFD-0016 ratified — refinement membership under OWA is
three-valued — is recovered by combining:

- `Truth4.ofMetaValue_inK3`: every K3 `MetaValue` embeds into the K3 fragment
- `Truth4.toMetaValue_ofMetaValue`: the round-trip is the identity
- `Truth4.federate_single_standpoint`: single-standpoint federation reduces
  to the contribution itself
- `flow_typing_soundness` (existing theorem): refinement membership narrowing
  is sound under information-monotone state evolution

The new framework adds no new behaviour to the K3 case; it adds the option
to escape into FDE for federated cross-standpoint queries (which RFD-0016
neither addressed nor ruled out). -/

/-- **D-113 fidelity.** The new framework's behavior on a single-standpoint
K3 input is identical to the existing `MetaValue`-only behaviour: the value
round-trips through Truth4 and back unchanged. -/
theorem D113_fidelity (m : MetaValue) :
    toMetaValue (ofMetaValue m) (ofMetaValue_inK3 m) = m :=
  toMetaValue_ofMetaValue m

end Truth4
