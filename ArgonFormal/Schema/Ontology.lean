/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArgonFormal.Schema.Signature

/-!
# Ontologies, TBox, and ABox

TBox axioms (signature-only abstraction; internal structure not needed for
the locality / module-extraction proofs), ABox assertions, and the
`Ontology` structure that pairs them.

The choice to abstract TBox axioms by their signature alone is deliberate:
the locality and CWA-conservativity theorems in
`ArgonFormal.Locality.*` only need to know which symbols an axiom
mentions, not the axiom's internal logical shape.
-/

/-- An individual name. -/
abbrev Individual (IN : Type) := IN

/-- A TBox axiom (abstract — we don't need internal structure for the
module extraction theorem, only the signature). -/
structure TBoxAxiom (CN RN : Type) [DecidableEq CN] [DecidableEq RN] where
  /-- The signature of symbols mentioned in this axiom. -/
  sig : Signature CN RN

/-- An ABox assertion: an individual is asserted to be of a concept, or a
role assertion between two individuals. -/
inductive ABoxAssertion (CN RN IN : Type) where
  | conceptAssertion : CN → IN → ABoxAssertion CN RN IN
  | roleAssertion : RN → IN → IN → ABoxAssertion CN RN IN

namespace ABoxAssertion

variable {CN RN IN : Type} [DecidableEq CN] [DecidableEq RN]

/-- The concept names mentioned in an ABox assertion. -/
def concepts : ABoxAssertion CN RN IN → Finset CN
  | conceptAssertion c _ => {c}
  | roleAssertion _ _ _ => ∅

/-- The individual names mentioned in an ABox assertion. -/
def individuals [DecidableEq IN] : ABoxAssertion CN RN IN → Finset IN
  | conceptAssertion _ a => {a}
  | roleAssertion _ a b => {a, b}

end ABoxAssertion

/-- An ontology consists of a TBox and an ABox. -/
structure Ontology (CN RN IN : Type) [DecidableEq CN] [DecidableEq RN] where
  tbox : Finset (TBoxAxiom CN RN)
  abox : Finset (ABoxAssertion CN RN IN)

namespace Ontology

variable {CN RN IN : Type} [DecidableEq CN] [DecidableEq RN] [DecidableEq IN]

/-- The signature of an ontology: union of all axiom signatures. -/
def sig (O : Ontology CN RN IN) : Signature CN RN where
  concepts := O.tbox.biUnion (fun α => α.sig.concepts)
  roles := O.tbox.biUnion (fun α => α.sig.roles)

/-- The domain of an ontology: all individuals mentioned in ABox assertions. -/
def domain (O : Ontology CN RN IN) : Finset IN :=
  O.abox.biUnion ABoxAssertion.individuals

/-- Subontology relation. -/
instance : HasSubset (Ontology CN RN IN) where
  Subset O₁ O₂ := O₁.tbox ⊆ O₂.tbox ∧ O₁.abox ⊆ O₂.abox

end Ontology
