/-
  CWA-Conservative Module Extraction
  Σ-Scoped CWA-Conservativity Theorem (Thread 1)

  MAIN RESULT: Standard ⊥-locality module extraction IS Σ-scoped
  CWA-conservative.

  Proof relies on:
  1. P4 (conservative extension) from Cuenca Grau et al. 2008
  2. CWA reduces to classical non-entailment (definitional)
  3. ABox is unchanged by tree-shaking (only TBox is extracted)
-/
import ArgonFormal.Locality.Cwa

variable {CN RN IN : Type} [DecidableEq CN] [DecidableEq RN] [DecidableEq IN]

/-! ## Key Lemma: ABox identity under TBox extraction -/

theorem abox_unchanged [BotLocality CN RN]
    (M : LocalityModule CN RN) (O : Ontology CN RN IN) :
    (⟨M.module, O.abox⟩ : Ontology CN RN IN).abox = O.abox := rfl

theorem domain_unchanged [BotLocality CN RN]
    (M : LocalityModule CN RN) (O : Ontology CN RN IN) :
    (⟨M.module, O.abox⟩ : Ontology CN RN IN).domain = O.domain := by
  simp [Ontology.domain]

/-! ## Main Theorem -/

/-- ⊥-locality module extraction is Σ-scoped CWA-conservative.

    For any CWA conclusion about a Σ-concept and a Σ-reachable individual:
    the conclusion holds in O iff it holds in the extracted module. -/
theorem locality_sigma_scoped_cwa_conservative [DLEntails CN RN IN]
    [BotLocality CN RN]
    (M : LocalityModule CN RN) (O : Ontology CN RN IN)
    (ω : WorldAssumptionMap CN)
    (h_ce : conservativeExtension M O) :
    sigScopedCwaConservative M O ω := by
  intro cc h_concept h_individual
  simp only [cwaConclusionHolds]
  have h_dom : (⟨M.module, O.abox⟩ : Ontology CN RN IN).domain = O.domain :=
    domain_unchanged M O
  constructor
  · intro ⟨hclosed, hdom, hnot⟩
    exact ⟨hclosed, h_dom ▸ hdom,
      fun h => hnot ((h_ce cc.concept cc.individual h_concept).mpr h)⟩
  · intro ⟨hclosed, hdom, hnot⟩
    exact ⟨hclosed, h_dom ▸ hdom,
      fun h => hnot ((h_ce cc.concept cc.individual h_concept).mp h)⟩

/-!
## Significance

This theorem resolves the Σ-scoped case of CWA-conservative module extraction.

The Lutz-Seylan-Wolter inherent intractability (IJCAI 2013) strengthens this:
for DL-Lite and EL, in all tractable cases CWA adds no new query answers.
Module extraction trivially preserves CWA entailments there because there
are none to break.

The only non-trivial case is ELI (EL + inverse roles), where CWA can be
both useful and tractable. Even there, this theorem applies when closed
concepts are in the seed signature.

### What remains:
- Ghost individuals (DomainConservative.lean)
- Defeasible interactions (DefeasibleExtraction.lean)
- Chained CWA across strata (induction on stratification, future work)
-/
