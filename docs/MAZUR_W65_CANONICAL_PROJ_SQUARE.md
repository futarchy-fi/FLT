# Canonical section-ring Proj base change

W65 identifies W64's transported Proj structural map with the intrinsic
structural map and proves the square of actual canonical Proj maps Cartesian.
It also proves fpqc descent of open immersion for these canonical maps,
exact inverse images of positive homogeneous basic opens, and the implication
from canonical open immersion to section-open ampleness.

## Contracts

`GradedProjStructuralNaturality.map_toSpecBase` proves structural naturality
for a graded map compatible with a map between possibly different scalar rings.
`GradedProjUnitChartMap` proves the corresponding homogeneous-fraction formula
and naturality of unit-coordinate chart morphisms.

`SectionGradedProjGrading.iso` identifies the structural and structure-sheaf
presentations of the original section grading by the identity ring map. Its
structural-map and chart compatibilities are proved.
`SectionGradedProjIntrinsicSquare.toSpecBase_eq` identifies the transported
structural map with the intrinsic map of the pulled-back line bundle.

`SectionGradedBaseChangePullback.sectionsAlgEquiv_one_tmul` identifies the
full section-algebra comparison on every original section with actual
pullback. `SectionGradedProjPullbackEvaluation` compares homogeneous fractions
using the numerator-denominator equation in the pulled-back tensor power;
line coordinates on the two domains need not be chosen compatibly.
`SectionGradedProjNaturality.toProj_map` glues this compatibility and derives
positive-power generation after arbitrary pullback.

`SectionGradedProjBaseChangeProjection` proves that the section-pullback map
induces a global Proj map under W64's flat affine base-change hypotheses, and
identifies it with the transported projection. The actual canonical maps
commute by `SectionGradedProjCanonicalSquare.toProj_projection`; their square
is Cartesian by `SectionGradedProjCanonicalSquare.isPullback`.

`SectionGradedProjFpqcDescent.isOpenImmersion_iff` checks open immersion of the
canonical map after a flat surjective change between affine bases. It requires
positive-power generation on the original line bundle, compact separated
source, and local rank one. It assumes neither a Cartesian canonical square
nor its commutativity. The section-algebra comparison inherited from W64 is
for `Scheme.{0}`; the generic graded-ring lemmas remain universe-polymorphic.

`SectionGradedProjOpens.toProj_preimage_basicOpen` identifies each positive
homogeneous basic open's inverse image with the actual section generator open.
`GradedProjPositiveBasis` supplies positive homogeneous affine neighborhoods
inside any Proj open. These prove
`SectionGradedProjAmpleOfOpenImmersion.ample`: for a compact source and a
positively generated line bundle, canonical open immersion implies ampleness.

## Remaining mathematics

The converse, ampleness implying canonical open immersion, is not proved.
It needs the actual homogeneous-localization-to-functions comparison on
an affine generator open to be an isomorphism. Existing section-extension
lemmas supply numerators, but their nested tensor powers must be identified
with the graded ring, and vanishing sections must be killed by powers of the
denominator to prove injectivity. W64's flat tensor-localization injectivity
is a different assertion and cannot substitute for this sheaf statement.

Fpqc ampleness descent still needs that converse and the descent of enough
positive-power generators. Relative assembly, the arbitrary-base fibre
criterion, and A7–A8 remain. W65 does not remove `Mazur_statement` from FLT.
