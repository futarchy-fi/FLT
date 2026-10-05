# Flat base change for Proj and full section rings

The generic comparison is `FlatGradedProjBaseChange.isPullback`: for an
internally graded commutative `R`-algebra `A` and a flat commutative
`R`-algebra `B`, the square from `Proj (B ⊗[R] A)` to `Proj A` over
`Spec B → Spec R` is Cartesian. Neither finite generation nor generation
in degree one is required.

The proof uses the actual extended homogeneous submodules
`fun n ↦ (𝒜 n).baseChange B`. Their positive degrees are generated as an
ideal by the original positive degrees, so the graded inclusion defines
a globally defined Proj projection. The inverse image of `D₊(f)` is
`D₊(1 ⊗ f)`, and the projection commutes with the structural maps.

On each chart, `HomogeneousLocalizationBaseChange.comparison` extends the
map on homogeneous fractions to a `B`-algebra map. Every target numerator
is a finite sum of homogeneous tensors, proving surjectivity without
flatness. `FlatHomogeneousLocalizationBaseChange.equiv` proves injectivity
under flatness: tensoring the inclusion into ordinary localization remains
injective, and ordinary localization commutes with base change. These
ring equivalences give Cartesian affine charts; the scheme open-cover
criterion then proves the global Cartesian square.

For actual tensor-power section rings:

- `SectionGradedBaseChangeGrading` gives the internal structural grading
  and proves its scalar extension equals W63's extended degree ranges.
- `SectionGradedProjStructuralMap.toProj_toBase` proves the canonical
  section-ring morphism lies over its affine base.
- `SectionGradedProjBaseChangeEquiv.iso` identifies the Proj of the actual
  pulled-back section ring with Proj of the internally graded scalar
  extension, using the full W63 algebra equivalence.
- `SectionGradedProjBaseChangeSquare.isPullback` transports the generic
  Cartesian square through that actual section-ring isomorphism.

The section-ring results retain the existing universe-zero comparison,
compact and separated source, affine bases, flat base map, and locally
free rank-one bundle assumptions. The generic results are universe-polymorphic.
The algebra structure on a homogeneous localization retains Mathlib's
existing scalar action; it is a scoped instance.

## Still required for ampleness descent

The transported structural map in the final square must be identified
with the intrinsic structural map of the pulled-back section ring. The
canonical source-to-Proj maps must then be shown to commute with the
section-ring comparison; W63's fixed-target pullback naturality does not
by itself prove this statement.

The inverse-image formula for the canonical section-ring morphism on all
basic opens, the localization/functions isomorphism on affine generator
opens (including denominator killing), and the section-ampleness/open-
immersion criterion remain unproved. Only after those comparisons can
fpqc open-immersion descent yield fpqc ampleness descent. The arbitrary-
base fibre criterion and A7–A8 remain downstream work. These results do
not remove `Mazur_statement` or `sorryAx` from the final FLT theorem.
