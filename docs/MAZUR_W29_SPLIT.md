# W29: normalization pullback of the divisor module

The W27 and W28 geometric contracts remain unchanged. Every new Lean module
has a whole-file cap of 240 lines. The first comparison is split before
implementation; its local proof uses the fact that normalization is an open
immersion over each torus and that the boundary divisor misses the nodes.
This avoids requiring normalization to be flat at the endpoints.

| Leaf | Proposed module | Proof design | Validation status |
|---|---|---|---|
| D04b.4a | IdealModulePullback | Pull back the actual ideal inclusion; transpose along the module adjunction and use `le_map_comap` and `ideal_ker_le` to show it vanishes in the quotient. Lift through the kernel. Compare with open restriction and the unit ideal. | Build, individual lint and 11-declaration axiom audit passed (121/240 lines). |
| D04b.4b | IdealModulePullbackRestrict | Cancel the target ideal inclusion. Use naturality of `modulePullbackRestrictIso` and its structure-module compatibility. Deduce local invertibility from invertibility in a commuting open square. | Build, individual lint and 12-declaration axiom audit passed (126/240 lines). |
| D04b.4c | PolygonIdealModulePullback | On the torus use the identity square; off the divisor use the unit-ideal comparison. Cover normalization using its torus and endpoints, with node nonsmoothness excluding marked support. | Build, individual lint and 7-declaration axiom audit passed (113/240 lines). |
| D04b.4d.1 | ModuleSheafDualInternalHom | Identify the common linear subfunctor, prove linearity, and retain actual tensor evaluation and its naturality. | Prototype and clean foreground build passed (129/240). |
| D04b.4d.2 | ModuleSheafDualPullback | Pull back tensor evaluation, curry, and compare with the intrinsic dual; prove evaluation on arbitrary sections and pullback-unit sections and naturality. | Prototype and clean foreground build passed (135/240). |
| D04b.4d.3a | ModuleSheafDualPullbackUnit | Compare with the explicit unit isomorphism through the tensor unitor; transport to globally trivial modules; retain dual sections and evaluation through a module isomorphism. | Prototype and clean foreground build passed (161/240). |
| D04b.4d.3b | Pending dual restriction coherence | Prove the canonical dual comparison commutes with open restriction, then apply local triviality and open-cover isomorphism detection. | Unproved; precise square in `W29_DUAL_LOCAL_CONTRACT.lean`. |
| D04b.4e.1 | PolygonDivisorLineComparison | Use the actual negative ideal isomorphism to construct the positive comparison morphism, retaining pairing and canonical-section compatibility. | Prototype and clean foreground build passed (75/240); invertibility is unproved. |

The first three leaves identify the negative ideal module. The dual leaves
construct the positive comparison and control its pairing and canonical
section; identification as an isomorphism still requires D04b.4d.3b. D04b.5, D04c.2 and D05–D10 retain the exact targets in
`MAZUR_W28_SPLIT.md`; one-gon self-incidence and both two-gon nodes remain in scope.

## Remaining dual restriction square

Let `g = f ∣_ U` and `V = f ⁻¹ᵁ U`. The source isomorphism is
`modulePullbackOpenIso f U (moduleSheafDual M)` followed by pullback of
`moduleSheafDualRestrictIso M U`. The target isomorphism is
`moduleSheafDualRestrictIso ((pullback f).obj M) V` followed by the inverse
of the dual isomorphism induced by `modulePullbackOpenIso f U M`.
The required equality is restriction of `moduleSheafDualPullbackHom f M`,
followed by the target isomorphism, equals the source isomorphism followed
by `moduleSheafDualPullbackHom g (M.restrict U.ι)`.

Local triviality of the two objects alone does not prove that this specific
morphism is invertible. `moduleSheafDualPullbackHom_isIso_of_trivial` applies
on each chart once this square commutes. Then open-cover isomorphism detection
can give the general rank-one result. No new rank-one predicate, assumed
invertibility field or admission replaces that proof.

## Negative ideal-module validation

Checked 2026-10-03 14:43 UTC: the three promoted modules passed individual
foreground builds and sequential individual lints with `LEAN_NUM_THREADS=2`.
The originating-declaration audit covers all 30 declarations, including the
reassociation lemmas, and admits only `propext`, `Classical.choice`, `Quot.sound`.
`W29_CONSUMER_CONTRACT.lean` checks the one-gon, an arbitrary branch of the
two-gon, and the actual inclusion identity, with empty output.
The evidence is in the untracked `GOAL_MAZUR_W29_*` build, lint, axiom and
consumer logs. The positive divisor line is not yet identified.

## Full W29 validation and scope

Checked 2026-10-03 15:12 UTC: all seven modules passed individual foreground
builds and individual `lake exe runLinter MODULE` runs with `LEAN_NUM_THREADS=2`.
There are 860 new Lean lines; every whole-file count is below 240. All 75
originating declarations, including generated declarations, passed the axiom
audit with only `propext`, `Classical.choice`, and `Quot.sound`.

The final consumer contract passes with empty output. It checks the negative
ideal isomorphism for the one-gon and both two-gon indices, the actual inclusion
identity, the positive comparison on both two-gon branches, and canonical-section
transport on the one-gon. These checks do not assert positive invertibility.

Reproduce source scope, caps, imports and validation-log checks with
`python3 W29_CHECK_SOURCE.py`. Audit and consumer evidence is retained untracked
in `GOAL_MAZUR_W29_ALL_AXIOMS.txt` and `GOAL_MAZUR_W29_CONSUMER_CONTRACT.txt`.
The precise local square is type-checked separately by
`lake env lean W29_DUAL_LOCAL_CONTRACT.lean`; its equality is not proved.

D04b.4 remains incomplete at the isomorphism requirement. D04b.5/D04c.2,
D05–D10, and the later generalized-curve/moduli/Mazur producers remain unproved.
Source inspection still finds `Mazur_statement` in `FLT/Assumptions/Mazur.lean`
and `mazur_W` in `FLT/Assembly/ExistingInputs.lean`; W29 does not remove them.
No fresh final-theorem axiom audit is claimed.
