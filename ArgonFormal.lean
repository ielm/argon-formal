/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

-- Foundation
import ArgonFormal.Foundation.MetaValue
import ArgonFormal.Foundation.Truth4
import ArgonFormal.Foundation.LatticeContext
import ArgonFormal.Foundation.Projection

-- Schema
import ArgonFormal.Schema.Signature
import ArgonFormal.Schema.Ontology
import ArgonFormal.Schema.WorldAssumption
import ArgonFormal.Schema.TypeGraph

-- Reasoning
import ArgonFormal.Reasoning.State
import ArgonFormal.Reasoning.Stratification
import ArgonFormal.Reasoning.Rule
import ArgonFormal.Reasoning.Fixpoint
import ArgonFormal.Reasoning.Stability
import ArgonFormal.Reasoning.Composition
import ArgonFormal.Reasoning.Necessity
import ArgonFormal.Reasoning.Parametric
import ArgonFormal.Reasoning.Diagnostics

-- TypeSystem
import ArgonFormal.TypeSystem.NarrowPred
import ArgonFormal.TypeSystem.NarrowEnv
import ArgonFormal.TypeSystem.Judgment
import ArgonFormal.TypeSystem.Monotonicity
import ArgonFormal.TypeSystem.Soundness.CrossStratum
import ArgonFormal.TypeSystem.Soundness.CwaOwa
import ArgonFormal.TypeSystem.Soundness.Defeasibility
import ArgonFormal.TypeSystem.Soundness.FlowTyping

-- Standpoint
import ArgonFormal.Standpoint.Stratification
import ArgonFormal.Standpoint.Federation
import ArgonFormal.Standpoint.Consistency
import ArgonFormal.Standpoint.BackwardCompat

-- Decidability
import ArgonFormal.Decidability.Fragment
import ArgonFormal.Decidability.Domain1.TC
import ArgonFormal.Decidability.Domain1.Eval
import ArgonFormal.Decidability.Domain1.Decidability
import ArgonFormal.Decidability.Domain2.Theories
import ArgonFormal.Decidability.Domain2.Decidability
import ArgonFormal.Decidability.CrossDomain.Staging
import ArgonFormal.Decidability.CrossDomain.Decidability
import ArgonFormal.Decidability.Complexity.Bounds

-- Locality
import ArgonFormal.Locality.Cwa
import ArgonFormal.Locality.ChainedCwa
import ArgonFormal.Locality.Locality
import ArgonFormal.Locality.ScopedConservativity
import ArgonFormal.Locality.SheafEquivalence
import ArgonFormal.Locality.DomainConservative
import ArgonFormal.Locality.Seminaive
import ArgonFormal.Locality.DefeasibleExtraction

/-!
# Argon — Formal Verification Workspace

Umbrella module. Importing this module brings in every Argon proof in the
workspace, organized by the seven top-level conceptual areas: Foundation,
Schema, Reasoning, TypeSystem, Standpoint, Decidability, Locality.

See `README.md` for the area-by-area breakdown and `lakefile.toml` for the
workspace structure.
-/
