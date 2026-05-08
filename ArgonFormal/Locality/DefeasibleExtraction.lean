/-
  CWA-Conservative Module Extraction
  Defeat-Aware Module Extraction (Thread 3)

  Removing a defeater can reinstate a previously overridden
  default (Bonatti et al. 2022). Defeat-complete extraction
  ensures all defeat chains for Σ-concepts are retained.
-/
import ArgonFormal.Schema.Signature
import ArgonFormal.Schema.Ontology
import ArgonFormal.Schema.WorldAssumption
import ArgonFormal.Locality.Locality

/-! ## Defeasible Rules and Superiority -/

variable {RuleId : Type} [DecidableEq RuleId] [Fintype RuleId]
variable {CN RN IN : Type} [DecidableEq CN] [DecidableEq RN]

/-- Rule strength. -/
inductive RuleStrength where
  | strict     : RuleStrength
  | defeasible : RuleStrength
  | defeater   : RuleStrength
deriving DecidableEq

/-- The superiority relation: r₁ defeats r₂. -/
def SuperiorityRel (RuleId : Type) := RuleId → RuleId → Prop

/-- Acyclicity: no rule defeats itself. -/
def superiorityAcyclic (sup : SuperiorityRel RuleId) : Prop :=
  ∀ r : RuleId, ¬ sup r r

/-! ## Defeasible Conclusions -/

/-- Whether a defeasible conclusion is warranted:
    the support rule fires AND no higher-priority rule
    with support defeats it. -/
def defeasibleWarranted
    (sup : SuperiorityRel RuleId)
    (supported : RuleId → Prop)
    (r : RuleId) : Prop :=
  supported r ∧
  ¬ ∃ (s : RuleId), sup s r ∧ supported s

/-! ## Defeat-Complete Extraction Theorem

If support is preserved for all rules in the defeat
neighborhood (the rule itself + all its defeaters +
all rules it defeats), then defeasible conclusions
are preserved. -/

theorem defeat_complete_preserves
    (sup : SuperiorityRel RuleId)
    (supp_full supp_extr : RuleId → Prop)
    (r : RuleId)
    -- Support of the target rule is preserved
    (h_r_supp : supp_full r ↔ supp_extr r)
    -- Support of every defeater of r is preserved
    (h_defeater_supp : ∀ s,
      sup s r → (supp_full s ↔ supp_extr s))
    : (defeasibleWarranted sup supp_full r ↔
       defeasibleWarranted sup supp_extr r) := by
  simp only [defeasibleWarranted]
  constructor
  · intro ⟨h_supp, h_not_def⟩
    exact ⟨h_r_supp.mp h_supp, fun ⟨s, hs, hss⟩ =>
      h_not_def ⟨s, hs,
        (h_defeater_supp s hs).mpr hss⟩⟩
  · intro ⟨h_supp, h_not_def⟩
    exact ⟨h_r_supp.mpr h_supp, fun ⟨s, hs, hss⟩ =>
      h_not_def ⟨s, hs,
        (h_defeater_supp s hs).mp hss⟩⟩

/-!
## Summary

The defeat-complete extraction theorem is clean:
if you preserve the support status of (a) the rule
itself and (b) all its defeaters, then the defeasible
conclusion (warranted or not) is preserved.

This means the defeat-closure algorithm only needs to
include rules that are in a direct superiority relation
with retained rules — NOT the transitive closure. The
Governatori algorithm checks direct defeat only.

Combined with locality-based TBox extraction (which
preserves support by preserving all Σ-entailments),
this gives sound tree-shaking for defeasible modules.
-/
