/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fintype.Basic
import ArgonFormal.Foundation.MetaValue

/-!
# TypeGraph

The finite-DAG model over which Argon's Domain 1 decidability proofs
evaluate refinement predicates. Concepts form a finite type with
decidable specialization; each (concept, axis) pair carries a
`MetaValue` (IS / CAN / NOT).

The decidability proofs in `ArgonFormal.Decidability.Domain1.*`
operate over this structure.
-/

/-- A finite type graph: the model over which Domain 1 predicates are
evaluated.

`C` is the concept type (finite, with decidable equality).
`A` is the axis type (finite, with decidable equality).
The `specializes` relation forms a DAG (not enforced in the structure,
but required by the Argon specification).
`metaProp` assigns a `MetaValue` to each (concept, axis) pair. -/
structure TypeGraph (C A : Type) [Fintype C] [DecidableEq C]
    [Fintype A] [DecidableEq A] where
  /-- The specialization relation (concept c₁ specializes concept c₂). -/
  specializes : C → C → Prop
  /-- Specialization is decidable. -/
  specializes_dec : DecidableRel specializes
  /-- Meta-property assignment: maps each (concept, axis) pair to a `MetaValue`. -/
  metaProp : C → A → MetaValue

attribute [instance] TypeGraph.specializes_dec
