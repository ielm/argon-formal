/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Stratification

Topological ordering of axes by dependency. Existence of a stratification
is equivalent to acyclicity of the axis dependency graph.

The fixpoint computation processes axes in stratum order; rules at
stratum `n` only read from already-completed strata `< n`. This is the
classical stratified-Datalog discipline applied to the meta-property
calculus.
-/

/-- A stratification assigns each axis to a stratum number.

Valid iff: whenever axis `a` depends on axis `b`, `strat b < strat a`.
Existence of a stratification is equivalent to acyclicity of the
dependency graph. -/
structure Stratification (A : Type) where
  /-- The stratum number for each axis. -/
  strat : A → Nat
  /-- The number of strata (1 + max stratum). -/
  numStrata : Nat
  /-- All strata are within bounds. -/
  bounded : ∀ a, strat a < numStrata

/-- The axis dependency relation is acyclic if a stratification exists. -/
def HasStratification (A : Type) (dep : A → A → Prop) : Prop :=
  ∃ s : Stratification A, ∀ a b, dep a b → s.strat b < s.strat a
