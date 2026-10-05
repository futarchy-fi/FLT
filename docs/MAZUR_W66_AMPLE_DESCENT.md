# W66: the canonical Proj criterion and fpqc ampleness descent

This wave implements D4c–d and D5 of the W65 handoff. It does not establish
the A6 fibre criterion, A7–A8, or removal of `Mazur_statement`.

## Exact contracts

`SectionGradedPowers.of_tensorPower` identifies pure powers in nested tensor
powers with powers in the actual full graded section ring, using the existing
exponent-multiplication isomorphism. It includes exponent zero.
`SectionGradedChartExtension.numerator` transports the existing chart-extension
section through that isomorphism and proves its restriction equals the given
function times the actual ring power of the denominator.

`SectionGradedChartKernel.exists_pow_mul_eq_zero` proves the missing sheaf
kernel statement: on a finite affine cover by degree-`d` generator sections,
a global section of degree `d * n` which vanishes on one chart is annihilated
in the actual section ring by some power of that chart's generator. Scalar
ratios on each affine chart reduce this to principal-localization kernels;
one common exponent works over the finite cover. The proof works over nonreduced rings and handles kernels of restriction.

`SectionGradedChartComparison.toFunctions` is an actual ring homomorphism
from the homogeneous localization of the global section ring to functions
on a generator subopen. It restricts the graded ring, then inverts the scalar
identification of the localized restricted ring. This identification is proved
from generating section morphisms, including exponent zero.

`SectionGradedChartIsomorphism.ringEquiv` proves this comparison bijective on
each chart of a finite affine generator cover. Extension proves surjectivity;
the kernel theorem proves injectivity. `SectionGradedChartRatios` identifies
the comparison with genuine section ratios and proves restriction naturality.
`SectionGradedChartEvaluation.toFunctions_evaluation` compares it with actual
pullback and coordinate evaluation. `SectionGradedChartMorphism.toProjOn_eq`
identifies its scheme morphism with W65's globally constructed canonical map.

`SectionGradedProjOfAmple.isOpenImmersion` proves that an ample line bundle's
canonical Proj map is an open immersion. The affine chart comparisons give
local open immersions; the previously proved exact inverse images of positive
basic opens give global injectivity. `ample_iff` combines this with W65's
reverse criterion on a compact source with positive-power generation.

`SectionGeneratorSpan.sectionGeneratorOpen_le_of_mem_span` proves that a
linear combination generates only in the union of the original generator
opens. Combined with actual flat-base-change section expansions, it proves
`SectionGradedAmpleDescent.positivePowerGenerated`: an ample faithfully flat
pullback gives positive-power generation downstairs. The generator-open statement is proved from scalar spans.

`SectionGradedAmpleDescent.ample_iff` gives absolute ampleness descent for a
Cartesian square with compact separated original source, affine bases, flat
surjective base change, and an original line bundle. Generation downstairs
is derived. The previously proved canonical Cartesian square descends open
immersion, and the reverse criterion yields ampleness.

`RelativeAmple.of_fpqc_affineBase` refines an arbitrary fpqc cover of an affine
base to an affine faithfully flat witness. `RelativeAmple.of_fpqc` restricts
to affine opens of an arbitrary base and assembles the project's closed-power
presentation predicate. Both assume the original family is proper and the
original sheaf is locally free of rank one. They use the existing proper
ample converse to pass between closed-power presentations and ordinary
relative ampleness.

`GeneralizedEllipticCurve.FiniteSubgroup.isAmple_of_baseChange` applies the
result to the actual subgroup divisor and its canonical divisor-line pullback
isomorphism, assuming the original ideal is Cartier.
`IsCyclic.isAmple_baseChange_iff` discharges that Cartier hypothesis with the
existing cyclic-subgroup Cartier theorem. This is fpqc invariance of the
project's `H.IsAmple` predicate.

The affine section-base-change infrastructure still uses `Scheme.{0}`.
The generic ring, tensor, and section lemmas retain their universe parameters.
Each new module is below the 240-line cap. No existing Lean module is edited
except the sorted imports in `FLT.lean`.

## Validation and remaining boundary

Recheck each new module separately with `LEAN_NUM_THREADS=2 lake build MODULE`
and `lake exe runLinter MODULE`. The untracked W66 handoff records the checked-at
time, originating-declaration axiom audit, independent consumer, local commit,
main merge, and final root build. No whole-library lint is required.

The next missing mathematics is the A6 fibre criterion: effective divisor
length/support versus component degree, the ample-degree criterion on proper
curves, and the arbitrary-base fibre-to-neighborhood theorem. The Stacks
contracts 0B5Y and 0D2S and foundational split in `MAZUR_W52_SPLIT.md` remain
relevant. The Noetherian-only fibre theorem cannot replace 0D2S.
A7's ample-level quotient/presheaf construction and A8's exact-order rational
point to finite étale subgroup, ample level, and generator invariance remain.
