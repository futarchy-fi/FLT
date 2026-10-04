# Tensor-power section rings and pullback

The full section direct sum now has its actual ring structure. For a locally
free rank-one sheaf it is commutative, and its homogeneous submodules give
Mathlib's `GradedAlgebra` instance. All degrees and all sections are included.

## Interface

For `L : X.Modules` and `U : X.Opens`:

- `SectionGradedSum.Sections L U` is the existing direct sum over all natural degrees.
- `SectionGradedSum.sectionRing` uses the existing bilinear `product`;
  `mul_eq_product` proves that agreement on arbitrary finite sums.
- `SectionGradedSum.lineSectionCommRing` supplies `CommRing` when
  `[Fact (LocallyFreeRankOne L)]` is available.
- `SectionGradedSum.grade L U n` is the range of the actual degree inclusion.
  `sectionGradedAlgebra` supplies its internal grading, with an explicit
  inverse to recomposition and the original structure-sheaf scalar action.
- `restrictRingHom` preserves the unit and multiplication.
- `SectionGradedPullback.gradedRingHom f L` pulls all global tensor degrees
  back along any scheme morphism, using the existing adjunction unit and
  `tensorPowerIso`. No flatness hypothesis is needed for this homomorphism.
- `LinePowerSectionBaseChange.degreeIso_tmul_mul` proves that the existing
  flat affine degree comparisons preserve products of scalar tensors of
  arbitrary sections. `degreeIso_tmul_one` checks the unit.

The usual `AlgebraicGeometry.Proj (SectionGradedSum.grade L U)` is therefore
well-typed for a line bundle. This supplies its input algebra; it does not
construct a morphism from `X` to that Proj.

## Proof method

`SectionGradedUnit` proves right-unit compatibility as an equality of
sheaf morphisms, by induction on tensor degree. `SectionGradedAssociativity`
uses four-factor sheaf-morphism extensionality and explicit degree transports.
These proofs apply to arbitrary sections on any open.

`SectionGradedCoordinates` identifies multiplication with scalar
multiplication under an actual trivialization. `SectionGradedLocalCoordinates`
proves the corresponding statement for ambient sections on an open chart,
using the existing tensor restriction comparisons. `SectionGradedCommutativity`
then detects equality of the two sheaf multiplication maps on a trivializing
cover. It does not assume that powers of global sections span.

`SectionGradedPullback` proves multiplicativity at the level of adjoint
sheaf morphisms. Induction uses `tensorIso_adj_pure`, the actual unit
comparison, and the sheaf tensor's universal property.

## Remaining construction

1. Promote the full module isomorphism `SectionGradedBaseChange.sectionsIso`
   to an algebra isomorphism with its structural base scalars. The proved
   homogeneous scalar-tensor formula supplies multiplicativity on generators;
   the tensor-product algebra structures and extension to arbitrary sums
   still need to be assembled.
2. Construct the canonical map on generator opens by degree-zero homogeneous
   localization ratios, prove independence of coordinates and agreement on
   overlaps, and glue under a positive-power generation hypothesis.
3. Identify the flat base-change square of that map. Prove the section-ampleness
   open-immersion criterion, then use fpqc descent of open immersions to obtain
   relative ampleness descent (D4c–d, D5).
4. Complete the component-degree/support and ample-degree results, the
   arbitrary-base fibre-to-neighborhood criterion, and A7–A8.

No canonical Proj morphism or ampleness descent theorem is claimed here.
`Mazur_statement` has not been removed from the Fermat endpoint.

## Verification

Build each of the ten new modules separately with `LEAN_NUM_THREADS=2 lake
build MODULE`; lint each with `lake exe runLinter MODULE`, sequentially.
The untracked `W62_VALIDATE.py` runs those checks and audits every originating
declaration, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
`W62_CONSUMER.lean` checks the ring, algebra, internal grading, commutative
ring, and Proj interfaces. `W62_CHECK_SOURCE.py` checks the source scope,
line caps, logs, commit, merged main ancestry, and endpoint audit, and prints
a UTC check timestamp. The root build is run after merging `origin/main`.
