# argon-formal

Argon's Lean 4 mechanical-proof workspace. One library, deep hierarchy. Each subdirectory of `ArgonFormal/` covers one conceptual layer of Argon's formal content.

```
argon-formal/
├── lakefile.toml             # one [[lean_lib]] entry: ArgonFormal
├── lean-toolchain            # leanprover/lean4:v4.29.0
├── ArgonFormal.lean          # umbrella: imports every area module
└── ArgonFormal/
    ├── Foundation/           # truth values, bilattice, lattice contexts, projection
    ├── Schema/               # signatures, TBox/ABox, ontologies, type graph,
    │                         # world-assumption maps
    ├── Reasoning/            # state, rules, fixpoints, stratification, AFT operators
    ├── TypeSystem/           # narrowing predicates + flow-typing soundness theorems
    ├── Standpoint/           # per-standpoint composition, federation, consistency
    │                         # policy, RFD-0016 backward-compat
    ├── Decidability/         # per-fragment decidability + complexity bounds
    └── Locality/             # CWA / locality / sheaf-equivalence
```

Cross-area imports are explicit (`import ArgonFormal.Foundation.Truth4` from a `TypeSystem/` file is the natural shape). One namespace root keeps collisions from arising at the import surface; one `lake build` builds everything.

## Build

```sh
lake build
```

Builds the umbrella `ArgonFormal` target plus every area module. 786 jobs at present; full build takes a few minutes cold and seconds incrementally.

## What each area proves

### `ArgonFormal.Foundation`

The algebraic substrate Argon's truth-value semantics rides on (see [RFD-0036](https://argon-book.vercel.app/rfd/0036-aft-grounded-truth-value-semantics.html)).

- `MetaValue.lean` — Kleene strong three-valued type ($\mathsf{K3}$): `is`, `not`, `can`. Information ordering with `can` as bottom; `is` and `not` incomparable.
- `Truth4.lean` — Belnap-Dunn four-valued bilattice ($\mathsf{FDE}$): `is`, `not`, `can`, `both`. Two orderings (truth + information), four core operations (∧_t, ∨_t, ¬, ⊗, ⊕), all bilattice algebraic laws.
- `LatticeContext.lean` — K3 / FDE / Boolean as type-level constraints. K3-closure theorems; the `is ⊕ not = both` escape witness; bidirectional `MetaValue ↔ K3-fragment-of-Truth4` isomorphism.
- `Projection.lean` — fail-closed FDE → K3 projection with policy parameters (`collapseToUnknown`, `treatAsError`, `preferIs`, `preferNot`); round-trip soundness.

### `ArgonFormal.Schema`

Knowledge-representation primitives.

- `Signature.lean` — `Symbol`, `Signature`, signature union / subset / hasConcept / hasRole.
- `Ontology.lean` — `TBoxAxiom`, `ABoxAssertion`, `Ontology`, signature + domain projections, sub-ontology relation.
- `WorldAssumption.lean` — `WorldAssumption` (open / closed) + `WorldAssumptionMap`.
- `TypeGraph.lean` — finite concept DAG with `MetaValue` labeling. The model over which Domain 1 decidability proofs evaluate refinement predicates.

### `ArgonFormal.Reasoning`

Rules, fixpoints, and the stratified-Datalog-style operators that drive the meta-property calculus.

- `State.lean` — assignment state `C → A → MetaValue`, pointwise information ordering, single-position `refine` update.
- `Stratification.lean` — topological ordering of axes by dependency.
- `Rule.lean` — `MonotoneRule` (Cat 1, positive propagation), `NafRule` (Cat 2, negation-as-failure), `ConstraintCheck` (Cat 3), `StratifiedRuleSet`. Composition + bounded fixpoint iteration helpers.
- `Fixpoint.lean` — `cat1Fixpoint`, `cat2Apply`, `processStratum`, `stratifiedFixpoint`. Theorem 1.1 (termination); Theorem 1.2 (uniqueness — axiomatized, classical); Theorem 1.3 (stability — axiomatized, classical); least-fixpoint uniqueness; `monotone_inflationary_fixpoint_finite` (proved); `cat1Fixpoint_is_fixpoint` (proved); axis-locality and commutation lemmas; rule-set extension monotonicity (proved).
- `Stability.lean` — Theorem 5: CAN-stability. `extension_monotone` (proved, via cat2 sublist-monotonicity).
- `Composition.lean` — Theorem 4: package composition preserves convergence.
- `Necessity.lean` — Theorem 2: acyclicity is necessary for the fixpoint.
- `Parametric.lean` — parametric propagation via expansion equivalence (lazy = eager).
- `Diagnostics.lean` — Theorem 3: constraint-check determinism (proven; uses `List.Perm.foldl_eq'` over `Finset.union_right_comm`).

### `ArgonFormal.TypeSystem`

Argon's flow-typing / occurrence-typing soundness theorems.

- `NarrowPred.lean` — narrowing predicates (`isIs`, `isNot`, `isDetermined`); upward-closure under information ordering (`holds_mono`).
- `NarrowEnv.lean` — narrowing environments + `satisfiedBy` predicate; `satisfiedBy_mono` lifts upward-closure to environments.
- `Judgment.lean` — judgment forms.
- `Monotonicity.lean` — monotonicity lemmas for the narrowing layer.
- `Soundness/CrossStratum.lean` — narrowings survive Cat 2 application + the full stratified fixpoint; handler-resolution preservation.
- `Soundness/CwaOwa.lean` — CWA → OWA boundary preservation; `isCwa` completeness preservation under information increase.
- `Soundness/Defeasibility.lean` — counterexamples showing defeasible overrides invalidate narrowings; restricted `strict_narrowing_sound` result.
- `Soundness/FlowTyping.lean` — the headline theorem: under Argon's structural conditions, occurrence-typing narrowing is sound.

### `ArgonFormal.Standpoint`

Cross-standpoint composition + the AFT-grounded truth-value framework.

- `Stratification.lean` — `StandpointOperator` abstraction; cross-standpoint fold + narrowing preservation (Vennekens-Gilis-Denecker stratification lifted to standpoints).
- `Federation.lean` — federation as AFT info-join; classification theorem (`federate = both` iff sources disagree); single-standpoint reduction.
- `Consistency.lean` — `ConsistencyPolicy` (strict / paraconsistent); strict-policy soundness theorems; multi-source append fold.
- `BackwardCompat.lean` — RFD-0016 K3 special case recovered: single-standpoint, strict-policy round-trips through Truth4 are identity; `D113_fidelity` theorem.

### `ArgonFormal.Decidability`

Decidability of Argon's refinement-predicate fragment.

- `Fragment.lean` — inductive grammar of the refinement-predicate language.
- `Domain1/TC.lean` — transitive closure decidability on finite types: `transGenDecidable` instance via bounded `iterReachable`. Soundness and saturation (`iterReachable_saturates`) both proved.
- `Domain1/Eval.lean` — finite-domain evaluation semantics for Domain 1 predicates.
- `Domain1/Decidability.lean` — Theorem 1: Domain 1 decidability.
- `Domain2/Theories.lean` — Domain 2 theory inclusion (axiomatic; satisfaction relation + decidability witnesses cited from primary sources).
- `Domain2/Decidability.lean` — Theorem 2: Domain 2 decidability.
- `CrossDomain/Staging.lean` — staging semantics; `stage_correct` (proven via structural induction on `MixedPred`).
- `CrossDomain/Decidability.lean` — Theorem 3: cross-domain decidability via staging + the `stagedDecidable` recursor.
- `Complexity/Bounds.lean` — per-fragment complexity bounds (axiomatic; cited).

### `ArgonFormal.Locality`

CWA / locality / sheaf-equivalence theorems for module composition.

- `Cwa.lean` — `sigmaDomain`, `CwaConclusion`, `cwaConclusionHolds`; sigma-scoped + strong CWA conservativity.
- `ChainedCwa.lean` — chained-CWA conservativity at a stratum (uses `StratumIndex` to disambiguate from `Reasoning.Stratification`).
- `Locality.lean` — locality property.
- `ScopedConservativity.lean` — scoped conservativity result.
- `SheafEquivalence.lean` — `ModuleDAG`, belief assignments, bridge eval, local fixpoints, equilibria, global sections; sheaf-style equivalence.
- `DomainConservative.lean` — domain conservativity.
- `Seminaive.lean` — seminaive evaluation.
- `DefeasibleExtraction.lean` — defeasible-rule extraction from a CWA module.

## Cross-area dependency graph

The areas form a clean DAG:

```
        Foundation                    Schema
            │                            │
            └──────────┬─────────────────┘
                       │
                  Reasoning
                       │
            ┌──────────┴──────────┐
            │                     │
       TypeSystem            Decidability
            │                     │
       Standpoint              Locality
```

`Standpoint` consumes `TypeSystem`'s narrowing infrastructure (it depends on `NarrowEnv` from `TypeSystem` plus `Foundation/{Truth4, LatticeContext, Projection}`); `Locality` is structurally independent.

## RFD references

Argon's design RFDs live in `argon/rfd/` of the orca-mvp tree. The proofs here are the mechanical witnesses for those RFDs:

- [RFD-0016](https://argon-book.vercel.app/rfd/0016-refinement-under-owa-is-three-valued.html) — superseded by RFD-0036; recovered as the K3 special case in `ArgonFormal/Standpoint/BackwardCompat.lean` (`D113_fidelity` theorem).
- [RFD-0036](https://argon-book.vercel.app/rfd/0036-aft-grounded-truth-value-semantics.html) — AFT-grounded truth-value semantics. The full `ArgonFormal/Foundation/{Truth4, LatticeContext, Projection}.lean` + `ArgonFormal/Standpoint/{Stratification, Federation, Consistency, BackwardCompat}.lean` constellation is this RFD's mechanical witness.

Future RFDs land as new top-level subdirectories or files within existing areas: RFD-0034 composition-pipeline proofs would land as `ArgonFormal/Composition/`; RFD-0035 binary-format proofs as `ArgonFormal/BinaryFormat/`; etc.

## Axioms used

Eight axioms total. Run `#print axioms <theorem>` from any downstream theorem to inspect what it actually depends on.

### External mathematical facts (6 axioms)

Results from external systems / well-known classical theorems we depend on but don't reprove.

- `Decidability/Domain2/Theories.lean` — `d2Sat`, `qfliaDecidable`, `gnfoDecidable`, `d2CombinedDecidable` (4 axioms): the satisfaction relation for Domain 2 predicates and the decidability witnesses for QF-LIA and GNFO fragments. Decidability is classical: Ginsburg-Spanier 1966 for QF-LIA; Bárány-ten Cate-Segoufin 2015 for GNFO.
- `Decidability/Complexity/Bounds.lean` — `qfliaNP`, `gnfo2ExpTime` (2 axioms): complexity classifications cited from primary sources.

### Argon proof obligations (2 axioms)

Classical results we're confident hold but whose Lean mechanizations require introducing a read-locality structural invariant on rules. Each carries a full proof outline in its docstring.

- `Reasoning/Fixpoint.lean`:
  - `stratified_fixpoint_unique` — topo-sort independence of the fixpoint (Apt-Blair-Walker 1988). Requires a purely combinatorial topo-sort swap chain plus read-locality between same-stratum axes for `processStratum_commute`.
  - `stratified_fixpoint_stable` — fixpoint witness (Knaster-Tarski applied per stratum). Requires read-locality so cat1 rules don't re-fire after cat2 adds NOT values, and so cat2 rule firing is determined by strictly-lower strata that don't change later.

The infrastructure for closing both is in place: `processStratum_only_modifies_axis`, `processStratum_commute` (under explicit read-independence), `composeMonotone_fixpoint_each_rule`, and the various per-component axis-locality lemmas. The remaining work is (a) the combinatorial topo-sort swap argument, and (b) introducing read-locality as a structural field on `MonotoneRule` / `NafRule` (or as a side condition on `StratifiedRuleSet`).

## License

Apache 2.0 — see individual files for full notice.
