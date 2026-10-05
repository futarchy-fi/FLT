# W77: finite affine diagrams over integer coefficient rings

This increment advances L1 / Stacks 0D2S. It does not prove global
approximation, the ample-neighborhood theorem L2 / 0D2N, or A7–A8.

## Proved contracts

All declarations below are in `FLT.Mazur.Approximation`.

| Module | Result |
| --- | --- |
| `CommonRelationIntegerModel` | Simultaneous vanishing of finitely many polynomials in finitely many presentation models. |
| `FiniteArrowIntegerModel` | Simultaneous algebra maps, with source relations checked and arbitrary additional finite polynomial equations retained. |
| `FiniteDiagramIntegerModel` | A finite category of algebra maps descends with identities, compositions, and natural tensor-product recovery. |
| `FiniteDiagramCoverModel` | Finite principal open covers on every object descend along with that diagram. |
| `PrincipalOpenIntegerModel` | Localizing a model constructs an open immersion whose scalar extension recovers the original principal chart. |
| `IntegerModelTransition` | Enlarging the coefficient ring gives maps of fixed presentation models, compatible with scalars and recovery. |
| `IntegerModelEventualEquality` | Finite vanishing data and equalities of maps from finite-type integer algebras hold after a common enlargement. |
| `FixedTargetIntegerModel` | Maps lift to later stages of a specified target presentation. |
| `ScalarCompatibleIntegerModel` | Such lifts can be chosen to respect the old coefficient ring before recovery. |

Each new module has at most 240 lines. Only sorted imports are added to
existing Lean code. No theorem assumes that a quotient model embeds into
the original algebra, or that extension from the coefficient subring is
faithfully flat.

## How the finite diagram is constructed

Choose finite presentations for all objects. Represent arrow images of
generators by polynomials. Add ideal-membership witnesses for the source
relations, identity laws, and composition laws to the coefficient set.
Polynomial coefficient inclusions are injective, so those witness identities
remain valid in the coefficient ring. Passing to the quotient gives actual
algebra maps satisfying the diagram laws at that stage.

`exists_integer_model_diagram` accepts an additional finite family of
vanishing polynomials at each object. It returns vanishing for **every**
coefficient lift of each supplied polynomial. This allows the caller to
use polynomial substitutions without matching a particular choice of lift.
Every presentation model has Mathlib's `tensorModelOfHasCoeffsEquiv`; the
returned arrows commute with these equivalences on `1 ⊗ b`, hence on the
whole scalar extension by linearity.

`exists_integer_model_diagram_covers` also chooses lifts of the functions
specifying each finite principal cover. A finite linear combination equal
to one is descended with the diagram, proving the basic opens cover the
model itself. The conclusion is stronger than covering only after scalar
extension.

`principalIntegerModelEquiv` identifies the scalar extension of a
localization of the model with the corresponding localization of the
original algebra. Its compatibility theorem identifies the chart maps;
`principalIntegerModel_isOpenImmersion` and
`principalIntegerModel_isPullback` supply the geometric properties.

## Enlarging a fixed model

`integerModelTransition` is induced by polynomial coefficient inclusion.
Its recovery and scalar formulas allow repeated enlargements to preserve
existing data. `exists_integer_model_eventual_zero` includes the coefficients
of vanishing witnesses and generators of the old coefficient ring.
`exists_integer_model_eventual_hom_eq` applies this to differences on finitely
many source generators.

`exists_fixed_target_integer_model_hom` constructs a lift by descending
source relations in the chosen target presentation. The scalar-compatible
version then equalizes the two maps from the old coefficient ring using
`exists_integer_model_eventual_hom_eq`. Its conclusion includes the scalar
formula at the later stage, not just its image after recovery.

## Still required for L1

1. Descend general overlap open immersions. The principal-open construction
   does not show that an arbitrary arrow returned by finite-diagram descent
   is an open immersion. Compare the overlap model with principal
   localizations and preserve these comparisons after common enlargement.
2. Assemble the affine gluing diagram, including the needed pullback
   identifications and triple-overlap conditions. Diagram composition laws
   alone do not supply geometric overlap or sheaf cocycle data.
3. Descend compatible transition units, glue the family and invertible
   sheaf, and identify their pullbacks.
4. Descend properness and fiber data. The proper-only form of 0D2S needs
   inverse-system approximation; a finite-presentation hypothesis is not
   an acceptable replacement.
5. Descend an ample fiber presentation, prove the Noetherian ample
   neighborhood (L2), and transfer it through approximation. Then do A7–A8.

Next bounded leaf: compare a descended overlap map with finitely many
principal localizations, using scalar-compatible lifts and eventual
map equality to preserve the inverse comparisons at a common stage.

## Validation

Build each new module with `LEAN_NUM_THREADS=2 lake build MODULE` and lint
with `lake exe runLinter MODULE`, one module at a time. Audit all originating
declarations, including generated declarations, against the allowlist
`propext`, `Classical.choice`, `Quot.sound`. The root build after merging
`origin/main` checks coexistence with other workers' declarations.
The untracked `MAZUR_W77_DONE.md` records checked results and evidence paths.
