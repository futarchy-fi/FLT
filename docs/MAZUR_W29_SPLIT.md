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
| D04b.4d | ModuleLineBundleDualPullback | Construct the dual pullback comparison from the genuine evaluation pairing and prove it invertible on rank-one trivializations. | Requires a further checked split before promotion. |
| D04b.4e | PolygonDivisorLinePullback | Combine the ideal comparison, dual pullback comparison and W28 ideal equality; prove evaluation and canonical-section compatibility. | Depends on preceding leaves. |

The first three leaves only address the negative ideal module. They do not
identify the positive divisor line until the dual comparison and its pairing
compatibility are proved. D04b.5, D04c.2 and D05–D10 retain the exact targets in
`MAZUR_W28_SPLIT.md`; one-gon self-incidence and both two-gon nodes remain in scope.

## Dual comparison refinement

The positive-line comparison needs the following additional leaves before
promotion. All retain the 240-line cap; these are proposed proof designs,
not completed results.

- D04b.4d.1 `ModuleSheafDualInternalHom`: identify the existing dual (morphisms
  on open subschemes) with the existing internal Hom into the structure module
  (morphisms on slice sites), using their common linear subfunctor. This retains
  the actual evaluation pairing.
- D04b.4d.2: pull back the evaluation pairing through `tensorIso` and
  `modulePullbackUnitIso`, then curry it to the canonical comparison into the
  dual of the pulled-back ideal.
- D04b.4d.3: prove this comparison invertible for locally free rank-one modules,
  with restriction naturality. Pairing compatibility is required, not just an
  uncharacterized isomorphism between locally trivial sheaves.
- D04b.4e: specialize to the polygon ideal isomorphism and identify the
  canonical section, which is the dual of the ideal inclusion.

## Negative ideal-module validation

Checked 2026-10-03 14:43 UTC: the three promoted modules passed individual
foreground builds and sequential individual lints with `LEAN_NUM_THREADS=2`.
The originating-declaration audit covers all 30 declarations, including the
reassociation lemmas, and admits only `propext`, `Classical.choice`, `Quot.sound`.
`W29_CONSUMER_CONTRACT.lean` checks the one-gon, an arbitrary branch of the
two-gon, and the actual inclusion identity, with empty output.
The evidence is in the untracked `GOAL_MAZUR_W29_*` build, lint, axiom and
consumer logs. The positive divisor line is not yet identified.
