/-
  CWA-Conservative Module Extraction
  ⊥-Locality Module Extraction: Definition and Properties

  Formalizes syntactic locality (Cuenca Grau et al. 2008, JAIR)
  and the conservative extension property P4.
-/
import ArgonFormal.Schema.Signature
import ArgonFormal.Schema.Ontology
import ArgonFormal.Schema.WorldAssumption

variable {CN RN IN : Type} [DecidableEq CN] [DecidableEq RN] [DecidableEq IN]

/-! ## ⊥-Locality (Abstract) -/

/-- An axiom is ⊥-local w.r.t. a signature Σ if replacing all
    non-Σ concept names with ⊥ makes it tautological.
    We abstract this as a decidable predicate. -/
class BotLocality (CN RN : Type) [DecidableEq CN] [DecidableEq RN] where
  isLocal : TBoxAxiom CN RN → Signature CN RN → Prop
  isLocal_dec : ∀ (α : TBoxAxiom CN RN) (σ : Signature CN RN),
    Decidable (isLocal α σ)
  local_of_sig_sub : ∀ (α : TBoxAxiom CN RN) (σ : Signature CN RN),
    α.sig ⊆ σ → isLocal α σ
  local_mono : ∀ (α : TBoxAxiom CN RN) (σ₁ σ₂ : Signature CN RN),
    σ₁ ⊆ σ₂ → isLocal α σ₁ → isLocal α σ₂

/-! ## Locality Module (Abstract Specification) -/

/-- A ⊥-locality module: the fixpoint of iterated non-local axiom collection. -/
structure LocalityModule (CN RN : Type) [DecidableEq CN] [DecidableEq RN]
    [BotLocality CN RN] where
  seed : Signature CN RN
  tbox : Finset (TBoxAxiom CN RN)
  /-- The extracted TBox module. -/
  module : Finset (TBoxAxiom CN RN)
  /-- The fixpoint signature (seed expanded to include all non-local axiom signatures). -/
  fixSig : Signature CN RN
  /-- The module is a subset of the TBox. -/
  module_sub : module ⊆ tbox
  /-- The fixpoint signature contains the seed. -/
  seed_sub : seed ⊆ fixSig

/-! ## Entailment (Abstract) -/

/-- Abstract entailment relation for a DL. -/
class DLEntails (CN RN IN : Type) [DecidableEq CN] [DecidableEq RN] where
  /-- Does ontology O entail that individual a is of concept C? -/
  entailsConcept : Ontology CN RN IN → CN → IN → Prop

/-! ## Conservative Extension (Property P4) -/

/-- Property P4: The full ontology is a Σ-conservative extension of the module.
    For any concept C in Σ and any individual a:
    O entails C(a) iff the module entails C(a). -/
def conservativeExtension [DLEntails CN RN IN] [BotLocality CN RN]
    (M : LocalityModule CN RN) (O : Ontology CN RN IN) : Prop :=
  ∀ (c : CN) (a : IN),
    c ∈ M.fixSig.concepts →
    (DLEntails.entailsConcept O c a ↔
     DLEntails.entailsConcept (⟨M.module, O.abox⟩ : Ontology CN RN IN) c a)
