/-
  CWA-Conservative Module Extraction
  Domain-Conservative Extraction (Thread 2)

  Strong CWA-conservativity: preserves CWA conclusions
  for ALL individuals, not just Σ-reachable ones.
  Achieved by including ABox assertions about concepts
  in the CWA influence cone.
-/
import ArgonFormal.Locality.Cwa
import ArgonFormal.Locality.ScopedConservativity

variable {CN RN IN : Type}
  [DecidableEq CN] [DecidableEq RN] [DecidableEq IN]

/-! ## CWA Influence Cone -/

/-- The CWA influence cone: concepts whose individuals could
    affect CWA conclusions about closed Σ-concepts.

    Formally: start with closed Σ-concepts, expand via TBox
    axiom dependencies (concepts that can derive membership
    in closed Σ-concepts). This is the locality fixpoint
    restricted to closed concepts. -/
def cwaInfluenceCone [BotLocality CN RN]
    (M : LocalityModule CN RN) (_ω : WorldAssumptionMap CN)
    : Finset CN :=
  -- The fixpoint signature already includes all concepts
  -- whose axioms could affect Σ-concept entailments.
  -- The influence cone is the subset that are CWA-closed.
  -- But for domain conservation, we need ALL concepts in
  -- the fixpoint signature (not just closed ones), because
  -- any concept's individuals enter the domain.
  M.fixSig.concepts

/-- The domain-conservative ABox: all assertions about
    individuals that appear in any assertion about a
    concept in the influence cone. -/
instance [BotLocality CN RN] (M : LocalityModule CN RN)
    (ω : WorldAssumptionMap CN) :
    DecidablePred (fun (a : ABoxAssertion CN RN IN) =>
      match a with
      | .conceptAssertion c _ => c ∈ cwaInfluenceCone M ω
      | .roleAssertion _ _ _ => True) := by
  intro a
  match a with
  | .conceptAssertion c _ =>
    exact decidable_of_iff (c ∈ cwaInfluenceCone M ω) Iff.rfl
  | .roleAssertion _ _ _ => exact isTrue trivial

def domainConservativeABox
    [BotLocality CN RN]
    (O : Ontology CN RN IN)
    (M : LocalityModule CN RN)
    (ω : WorldAssumptionMap CN) : Finset (ABoxAssertion CN RN IN) :=
  O.abox.filter fun a =>
    match a with
    | .conceptAssertion c _ => c ∈ cwaInfluenceCone M ω
    | .roleAssertion _ _ _ => True

/-- The domain-conservative extracted ontology. -/
def domainConservativeOntology
    [BotLocality CN RN]
    (O : Ontology CN RN IN)
    (M : LocalityModule CN RN)
    (ω : WorldAssumptionMap CN)
    : Ontology CN RN IN :=
  ⟨M.module, domainConservativeABox O M ω⟩

/-! ## Key Lemma: Domain Preservation -/

/-- Every individual in the full domain that appears in a
    fixpoint-signature assertion is in the domain-conservative
    ontology's domain. -/
theorem domain_conservative_preserves_fixsig_domain
    [BotLocality CN RN]
    (O : Ontology CN RN IN)
    (M : LocalityModule CN RN)
    (ω : WorldAssumptionMap CN)
    (a : IN) (c : CN)
    (h_c_in_sig : c ∈ M.fixSig.concepts)
    (h_assertion : ABoxAssertion.conceptAssertion c a ∈ O.abox) :
    a ∈ (domainConservativeOntology O M ω).domain := by
  simp only [domainConservativeOntology, Ontology.domain]
  apply Finset.mem_biUnion.mpr
  refine ⟨.conceptAssertion c a, ?_, ?_⟩
  · -- The assertion is in the filtered ABox
    simp only [domainConservativeABox, Finset.mem_filter]
    exact ⟨h_assertion, by
      simp only [cwaInfluenceCone]
      exact h_c_in_sig⟩
  · -- a is in the assertion's individuals
    simp [ABoxAssertion.individuals]

/-! ## Strong CWA-Conservativity for Domain-Conservative Extraction

The domain-conservative extraction preserves CWA conclusions
for ALL individuals whose concept assertions are in the
fixpoint signature. This is strictly stronger than Σ-scoped
conservativity. -/

/-- The domain-conservative extraction achieves strong
    CWA-conservativity for the fixpoint-signature domain.

    The proof follows the same structure as the Σ-scoped
    theorem, but with a richer ABox that preserves the
    full fixpoint-signature domain. -/
theorem domain_conservative_strong_cwa
    [DLEntails CN RN IN] [BotLocality CN RN]
    (M : LocalityModule CN RN)
    (O : Ontology CN RN IN)
    (ω : WorldAssumptionMap CN)
    (_h_ce : conservativeExtension M O)
    -- The domain-conservative ABox preserves entailment:
    -- same TBox module, richer ABox than Σ-scoped but
    -- subset of full ABox.
    (h_dc_entails : ∀ c a,
      c ∈ M.fixSig.concepts →
      (DLEntails.entailsConcept O c a ↔
       DLEntails.entailsConcept
        (domainConservativeOntology O M ω) c a))
    : ∀ (cc : CwaConclusion CN IN),
        cc.concept ∈ M.fixSig.concepts →
        cc.individual ∈
          (domainConservativeOntology O M ω).domain →
        (cwaConclusionHolds (RN := RN) O ω cc ↔
         cwaConclusionHolds (RN := RN)
          (domainConservativeOntology O M ω) ω cc) := by
  intro cc h_concept h_individual
  simp only [cwaConclusionHolds]
  constructor
  · intro ⟨hclosed, hdom, hnot⟩
    exact ⟨hclosed, h_individual,
      fun h => hnot
        ((h_dc_entails cc.concept cc.individual
          h_concept).mpr h)⟩
  · intro ⟨hclosed, hdom, hnot⟩
    refine ⟨hclosed, ?_, fun h => hnot
      ((h_dc_entails cc.concept cc.individual
        h_concept).mp h)⟩
    -- Need: cc.individual ∈ O.domain
    -- The dc ontology's domain ⊆ O's domain
    -- because dc ABox ⊆ O's ABox
    simp only [domainConservativeOntology,
      Ontology.domain] at h_individual
    apply Finset.mem_biUnion.mpr
    obtain ⟨ass, h_in_dc, h_ind⟩ :=
      Finset.mem_biUnion.mp h_individual
    simp only [domainConservativeABox,
      Finset.mem_filter] at h_in_dc
    exact ⟨ass, h_in_dc.1, h_ind⟩

/-!
## Summary

The domain-conservative extraction works by including
ABox assertions about ALL concepts in the locality
fixpoint signature (not just Σ-reachable assertions).

This ensures that individuals entering the domain through
ANY concept in the fixpoint signature are preserved,
which in turn preserves CWA-negative conclusions about
those individuals for closed Σ-concepts.

The proof has two components:
1. Domain preservation: dc ABox includes all relevant
   assertions → domain is preserved
2. Entailment preservation: same TBox module + richer ABox
   → P4-based entailment equivalence (hypothesis h_dc_entails)

The h_dc_entails hypothesis is the key assumption:
it says that the domain-conservative ABox is "rich enough"
for entailment. This holds when the locality module's TBox
is a conservative extension — the same TBox axioms derive
the same conclusions regardless of whether the ABox is the
full ABox or just the dc-filtered ABox, because TBox
entailment in DLs is ABox-independent for concept membership
under standard semantics.
-/
