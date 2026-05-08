/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union

/-!
# Signatures and Symbols

The basic vocabulary structure for Argon's knowledge-representation
proofs. A `Signature` is a finite set of concept names and role names;
ontologies are built on top.

This file is the schema-level alphabet. The full ontology + ABox
structure lives in `ArgonFormal.Schema.Ontology`; world-assumption maps
in `ArgonFormal.Schema.WorldAssumption`.
-/

/-- A symbol is either a concept name or a role name. -/
inductive Symbol (CN RN : Type) where
  | concept : CN → Symbol CN RN
  | role : RN → Symbol CN RN
deriving DecidableEq, Repr

/-- A signature is a finite set of symbols. -/
structure Signature (CN RN : Type) [DecidableEq CN] [DecidableEq RN] where
  concepts : Finset CN
  roles : Finset RN

namespace Signature

variable {CN RN : Type} [DecidableEq CN] [DecidableEq RN]

/-- Union of signatures. -/
instance : Union (Signature CN RN) where
  union σ₁ σ₂ := ⟨σ₁.concepts ∪ σ₂.concepts, σ₁.roles ∪ σ₂.roles⟩

/-- Subset relation on signatures. -/
instance : HasSubset (Signature CN RN) where
  Subset σ₁ σ₂ := σ₁.concepts ⊆ σ₂.concepts ∧ σ₁.roles ⊆ σ₂.roles

/-- Empty signature. -/
instance : EmptyCollection (Signature CN RN) where
  emptyCollection := ⟨∅, ∅⟩

/-- A concept name is in a signature. -/
def hasConcept (σ : Signature CN RN) (c : CN) : Prop := c ∈ σ.concepts

/-- A role name is in a signature. -/
def hasRole (σ : Signature CN RN) (r : RN) : Prop := r ∈ σ.roles

end Signature
