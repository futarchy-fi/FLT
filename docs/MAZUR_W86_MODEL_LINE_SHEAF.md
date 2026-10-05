# A line sheaf on the finite intersection model

## Construction

`exists_finite_line_sheaf_model` starts with a genuine locally free rank-one
sheaf on a compact separated scheme locally of finite presentation over
`Spec A`. It supplies a finite-type integer subalgebra, the descended affine
intersection diagram, and a concrete rank-one sheaf on its explicit gluing.
The scheme recovers by the actual cartesian square over the coefficient map;
all coordinate transition units recover under the supplied tensor equivalences.

The construction uses these independently reusable steps:

- `OpenImmersionSectionComparison`: global sections of an open chart identify
  with ambient sections on its image, compatibly with chart restriction.
- `IntersectionGluingSections`: union labels are ambient intersections;
  both all charts and the original singleton charts cover the colimit.
- `AffineIntersectionGluingSections`: the model coordinate ring identifies
  with ambient chart sections, naturally under diagram maps and restriction
  to any smaller open.
- `IntersectionUnitCocycle`: indexed units and their multiplication laws
  construct a cocycle on singleton charts. Cancellation proves normalization.
- `AffineIntersectionModelSheaf`: transport units through the section
  equivalences, construct the cocycle sheaf, prove its chart trivializations
  and local rank one, and identify its transitions with the coordinate units.
- `AffineIntersectionGluedModelSheaf`: transfer the cocycle to W84's explicit
  glue-data scheme. The sheaf is the actual pullback along the comparison
  isomorphism, and still has local rank one.
- `OpenImageSectionPullback`: section comparisons commute with arbitrary
  commuting chart squares, including non-open coefficient projections.
- `IntersectionUnitCocycleRecovery`: singleton reconstruction of the original
  intersection units recovers the original transitions on every subopen.

## Remaining boundary

The model sheaf is constructed from the descended units, not an arbitrary
rank-one sheaf. Nevertheless, identifying its pullback with the given sheaf
still requires a geometric compatibility proof. Neither the existence theorem
nor the construction asserts that missing identification.

The next step is to apply `openImageSectionIso_pullback` to the chart squares
of the coefficient projection and the recovered source atlas. Combine it with
`affineIntersectionModelCocycle_unit_eq` and coefficient recovery to identify
the inverse-image cocycle with the original cocycle. Then use
`Cocycle.pullbackIso` and the existing genuine-cocycle recovery isomorphism.
Account explicitly for the singleton-cover equalities and for the comparison
between the categorical colimit and the explicit glued model.

Properness and fiber descent remain subsequent tasks. The proper-only
approximation target has not acquired a local finite presentation hypothesis.
No ampleness, Noetherian L2, approximation transfer, A7–A8 coherence, or
exact-order rational-point bridge is claimed here.

## Verification interface

Build each named module with `LEAN_NUM_THREADS=2 lake build MODULE`, then
lint it separately with `lake exe runLinter MODULE`. Audit each declaration
against `propext`, `Classical.choice`, and `Quot.sound`. The campaign's endpoint
axiom audit is separate from these local correctness checks.
