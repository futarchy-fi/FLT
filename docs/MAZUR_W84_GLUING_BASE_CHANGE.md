# W84: gluing base change and compatible unit descent

This increment closes the first open item in the W83 handoff: the pullback
of the glued coefficient model is identified with the original covered
scheme, compatibly with its map to the affine base. It also supplies
algebraic descent of compatible unit families and multiplication laws.
It does not finish L1 or remove `Mazur_statement` from the FLT endpoint.

## Global scheme recovery

`AffineIntersectionProjection` constructs the tensor-inclusion projection
on the full spectrum diagram. Its naturality squares are cartesian, and
each component is the coefficient base-change square.

`EquifiberedSchemeGluing` proves that the map of colimits has cartesian
chart squares. `EquifiberedGluingBaseChange` uses these squares and locality
on an open cover to prove a global base-change criterion, both for chosen
colimits and for arbitrary colimit cocones.

`AffineIntersectionGluingBaseChange` applies that criterion to the actual
W83 glue data. The theorem `affineIntersectionGluing_isPullback` uses
`affineIntersectionGluedToBase` on both sides. The resulting
`affineIntersectionGluingPullbackIso` retains both pullback projections.

`FiniteIntersectionScalarGluingOver` proves that W83's recovery isomorphism
is over `Spec A`. Composing it with the inverse base-change identification
gives `finiteIntersectionModelPullbackIso`, whose structural compatibility
is `finiteIntersectionModelPullbackIso_over`.

`FiniteIntersectionSchemeDescent` constructs a global cartesian model
square from a finite affine cover of a separated scheme locally finitely
presented over `Spec A`. `CompactSchemeIntegerDescent` obtains the finite
affine cover from compactness. Both allow a prescribed finite set of base
coefficients. Neither theorem claims properness of the model.

## Unit descent on fixed coordinate presentations

`IntegerModelMarkedExtension` enlarges an existing coefficient stage to
contain finitely many marked elements or units of a fixed presentation.
The inverses of the units are constructed after enlargement.

`FiniteIntegerModelUnits` chooses one common stage for unit families in
different coordinate rings. `FiniteIntegerModelElementRelations` makes
finitely many recovered element equations hold at a common later stage.
Neither result assumes that quotient-model recovery is injective.

`FiniteDiagramUnitDescent.exists_finite_diagram_unit_model` combines these
results. For a finite diagram with fixed model arrows, it constructs units
whose recovered values are the specified original units, whose restrictions
agree along every transported arrow, and whose prescribed multiplicative
laws hold. The final arrows are transports of the initial arrows, so the
existing transport lemmas retain identity and composition laws. The
restriction-index maps need no extra functoriality assumptions for this
statement. They specify precisely which unit equations are descended.

## Remaining work, in order

1. Apply the unit-diagram theorem to transition units from a finite affine
   trivializing cover of an actual invertible sheaf. Identify ambient-open
   sections with the section algebras used by the intersection diagram.
   Include restrictions to triple intersections and the cocycle equations.
   Retain the open-immersion and cartesian-square laws after enlarging the
   model, then construct the model sheaf and its pullback identification.
2. Descend properness and the required fiber data. The proper-only 0D2S
   target still needs inverse-system approximation; the local finite
   presentation used above is only an intermediate case, not a new
   hypothesis on that target.
3. Descend an ample fiber presentation, prove L2 / 0D2N over a Noetherian
   base, and transfer it through approximation.
4. Complete A7–A8: compatible level isomorphisms, quotient/presheaf
   coherence, and the exact-order rational-point/subgroup bridge.

Parallel lanes D and G2 are outside this increment.

## Validation

The untracked `MAZUR_W84_DONE.md` records the checked source revision,
per-module builds and individual lints, originating-declaration axiom
audits, and the post-merge root build. `python3 W84_CHECK_SOURCE.py` checks
those recorded results against the current source hashes and git state.
Run the builds and audit again after any source change.
