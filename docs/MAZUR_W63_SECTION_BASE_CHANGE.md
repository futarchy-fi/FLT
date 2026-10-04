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

## Remaining construction

D4a–b's full algebra base-change comparison is now supplied. This comparison
alone does not construct the global canonical map to Proj or its base-change
square. Local Proj maps, overlap compatibility across scheme restrictions,
gluing under positive-power generation, the ampleness/open-immersion
criterion, fpqc descent, the fibre criterion, and A7–A8 are separate steps.
The theorem `PNat.pow_add_pow_ne_pow` has not been changed by these modules.
