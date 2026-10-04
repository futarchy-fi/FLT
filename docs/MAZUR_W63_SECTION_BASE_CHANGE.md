# Full section-algebra base change and homogeneous chart evaluation

The modules in this step extend the actual tensor-power section ring from
W62. They use all global sections in every nonnegative tensor degree.

## Full algebra base change

`SectionGradedStructuralAlgebra` gives `sectionModule f L` its section-ring
structure and an algebra structure over the original base's global functions.
`structural_smul` identifies this action with the original structural module
action; `structural_algebraMap` inserts pulled-back functions in degree zero.
The scalar extension carries the usual tensor-product ring and algebra.
These structures retain the module actions used by `sectionsIso`.
The comparison retains the existing universe-zero `Scheme` signature;
the independent Proj construction is universe-polymorphic.

`SectionGradedBaseChangeAlgebra.sectionsAlgEquiv` promotes the existing
`sectionsIso` to an algebra equivalence. Its hypotheses are exactly the
existing flat affine comparison: a cartesian square, compact separated
source, affine base and new base, flat base morphism, and a locally free
rank-one sheaf. Products and units are proved from the degreewise comparison,
using direct-sum and tensor-product induction. No conclusion is an input.

`SectionGradedBaseChangeDegrees` defines the homogeneous submodules using
the structural base scalars. The equivalence maps the range of each extended
degree inclusion onto its target degree, and reflects membership in that
range. Thus the comparison retains the entire grading as well as the algebra.

## Homogeneous fractions

`SectionGradedCoordinateEvaluation` sums tensor-power coordinates to obtain
a homomorphism from the full section ring to regular functions in a chosen
line trivialization. When the image of a denominator is a unit, this extends
to its degree-zero homogeneous localization. Evaluation multiplied by the
denominator coordinate equals the numerator coordinate.

`SectionGradedCoordinateIndependence` proves that the latter map is
independent of the trivialization. Its proof uses the actual scalar equation
on arbitrary sections of equal tensor degree. It does not require powers of
degree-one global sections to span the section ring.

## Canonical morphism to Proj

`GradedProjUnitChart` constructs the scheme map associated with an invertible
positive-degree coordinate. It proves compatibility with the standard
homogeneous localization transition, independence of the chosen invertible
denominator, and naturality in the target ring of functions.

`SectionGradedProjChart` applies this to the actual pullback of the original
full section ring. Coordinate independence holds on any fixed trivializing
domain, with no assumption that global degree-one sections span higher degrees.

`SectionGradedProjGeneratorChart` derives the unit-coordinate condition from
the actual generator open of a tensor-power section. It constructs the map
on each trivializing subopen of that generator open.

`SectionGradedProjChartNaturality` proves that fraction evaluation and the
local Proj maps commute with further scheme pullback. The proof transports
the intrinsic scalar equation by the actual pullback composition isomorphism;
it does not assume compatible tensor-power coordinate choices.

`SectionGradedProjChartPullback` proves that unit homogeneous coordinates
remain units after pullback, and provides the induced line trivialization.
`SectionGradedProjGluing` proves agreement on the actual fibre-product
overlaps, glues the maps, and proves independence of the generating cover.
Its `fromCover_comp` identifies the map on any further trivializing domain
with an invertible positive-degree section.

`SectionGradedProjConstruction.PositivePowerGenerated` says that every point
lies in the generator open of some global positive-power section. The module
constructs a generating trivializing cover from this pointwise hypothesis
and local rank one, then defines the canonical morphism

```lean
SectionGradedProjConstruction.toProj L h : X ⟶ Proj (SectionGradedSum.grade L ⊤)
```

`toProj_eq_fromCover` proves independence of all cover choices;
`toProj_comp` gives the chart formula after arbitrary pullback, and
`toProj_generatorChart` identifies it on actual generator subopens.
Every ample line bundle satisfies the positive-power generation hypothesis.
No quasi-compactness, separatedness, or affine-source condition is imposed
on this Proj construction itself.

## Remaining construction

D4a–b's full algebra base-change comparison and the canonical Proj morphism
are supplied. The square comparing this morphism with the canonical map
for the pulled-back line bundle is not yet proved cartesian. Naturality on
trivializing domains is a distinct, proved statement with the original
section ring as the fixed target.

Next identify Proj of the scalar-extended graded algebra with the scheme
base change, including the structural base morphisms and the homogeneous
localization comparisons. Then prove the section-ampleness/open-immersion
criterion: identify the homogeneous localizations with functions on affine
generator opens, using extension and denominator-killing results. The
existing fpqc open-immersion descent machinery can then be applied.

Fpqc ampleness descent, the fibre criterion, and A7–A8 remain unproved here.
The theorem `PNat.pow_add_pow_ne_pow` has not been changed by these modules.
