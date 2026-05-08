/-
Copyright (c) 2026 Ivan Leon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# World Assumptions

Per-concept world-assumption declarations. A `WorldAssumption` is the
choice between OWA (absence = unknown) and CWA (absence = false) for a
specific concept name.

In Argon, world assumptions are declared per-standpoint via
`[standpoints.<name>]` manifest entries. The `WorldAssumptionMap`
structure here is the internal representation those declarations lower
to. RFD-0036 also adds a per-standpoint *consistency policy* (`strict` /
`paraconsistent`) layered on top — that lives in
`ArgonFormal.Standpoint.Consistency`.
-/

/-- A world assumption for a predicate: either open or closed. -/
inductive WorldAssumption where
  /-- Absence of evidence is not evidence of absence (OWA). -/
  | open : WorldAssumption
  /-- Absence of evidence is evidence of absence (CWA). -/
  | closed : WorldAssumption
deriving DecidableEq, Repr

/-- A world assumption map assigns a world assumption to each concept name. -/
def WorldAssumptionMap (CN : Type) := CN → WorldAssumption
