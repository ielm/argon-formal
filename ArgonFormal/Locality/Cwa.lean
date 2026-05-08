/-
  CWA-Conservative Module Extraction
  CWA Rules, Domain Predicates, and Conservativity Notions
-/
import ArgonFormal.Schema.Signature
import ArgonFormal.Schema.Ontology
import ArgonFormal.Schema.WorldAssumption
import ArgonFormal.Locality.Locality

variable {CN RN IN : Type} [DecidableEq CN] [DecidableEq RN] [DecidableEq IN]

/-! ## Σ-Domain -/

/-- The Σ-concept-domain: individuals appearing in a concept assertion about a Σ-concept. -/
def sigmaDomain (O : Ontology CN RN IN) (σ : Signature CN RN) : Finset IN :=
  (O.abox.biUnion fun a =>
    match a with
    | .conceptAssertion c i => if c ∈ σ.concepts then {i} else ∅
    | .roleAssertion _ _ _ => ∅)

/-! ## CWA Conclusions -/

/-- A CWA conclusion: "individual a is NOT of concept C." -/
structure CwaConclusion (CN : Type) (IN : Type) where
  concept : CN
  individual : IN

/-- Whether a CWA conclusion holds: C is closed, a is in the domain, and O ⊭ C(a). -/
def cwaConclusionHolds [DLEntails CN RN IN]
    (O : Ontology CN RN IN) (ω : WorldAssumptionMap CN)
    (cc : CwaConclusion CN IN) : Prop :=
  ω cc.concept = WorldAssumption.closed ∧
  cc.individual ∈ O.domain ∧
  ¬ DLEntails.entailsConcept O cc.concept cc.individual

/-! ## Σ-Scoped CWA-Conservativity -/

/-- The module preserves CWA conclusions about Σ-concepts for Σ-reachable individuals. -/
def sigScopedCwaConservative [DLEntails CN RN IN] [BotLocality CN RN]
    (M : LocalityModule CN RN) (O : Ontology CN RN IN)
    (ω : WorldAssumptionMap CN) : Prop :=
  ∀ (cc : CwaConclusion CN IN),
    cc.concept ∈ M.fixSig.concepts →
    cc.individual ∈ sigmaDomain O M.fixSig →
    (cwaConclusionHolds (RN := RN) O ω cc ↔
     cwaConclusionHolds (RN := RN) ⟨M.module, O.abox⟩ ω cc)

/-! ## Strong CWA-Conservativity -/

/-- The module preserves CWA conclusions about Σ-concepts for ALL individuals. -/
def strongCwaConservative [DLEntails CN RN IN] [BotLocality CN RN]
    (M : LocalityModule CN RN) (O : Ontology CN RN IN)
    (ω : WorldAssumptionMap CN) : Prop :=
  ∀ (cc : CwaConclusion CN IN),
    cc.concept ∈ M.fixSig.concepts →
    cc.individual ∈ O.domain →
    (cwaConclusionHolds (RN := RN) O ω cc ↔
     cwaConclusionHolds (RN := RN) ⟨M.module, O.abox⟩ ω cc)
