# W26: divisor sections and powers toward ampleness

The input is `PREV_W25M_BLOCKED.md`; the W26-named previous handoff in
BRIEF.md is absent. The W25 support theorem concerns the actual marked ideal.
The target remains a positive tensor power of its actual `divisorLineBundle`
with `ProjectiveSpace.RelativeVeryAmple`; support is not a substitute definition.

## Proof leaves

| Module | Cap | Construction and check |
| --- | ---: | --- |
| `DivisorLineBundlePower` | 160 | Induct on powers, using the existing divisor-sum isomorphism and empty-divisor comparison. `W26_POWER_PROOF.lean` compiled before promotion. |
| `DivisorCanonicalSection` | 180 | Dualize the actual ideal inclusion. Evaluate on affine ideal sections, recover the local regular equation, and check restriction and divisor-sum compatibility. `W26_SECTION_PROOF.lean` compiled before promotion. |
| `DivisorPowerVeryAmple` | 160 | Transport the existing very-ample presentation along the power comparison, without assuming or asserting that a presentation exists. `W26_VERY_AMPLE_PROOF.lean` compiled before promotion. |

Every cap is at most 240 lines, including headers and documentation. Builds
and individual-module lints run sequentially in the foreground with
`LEAN_NUM_THREADS=2`. An originating-declaration audit checks definitions,
theorems and generated helpers for the three permitted axioms.

## Unproved producer

A presentation still requires an actual projective morphism, its closed
immersion proof, and a coefficient isomorphism to the hyperplane sheaf.
The existing `relativeVeryAmple_pullbackOOne` constructs the affine-open
presentations once these geometric data are proved. The new power comparison
only identifies the coefficient that those data must describe.

The direct polygon route needs sections of O(mD) on the normalization whose
values match at each node, a proof that they generate everywhere, and affine
chart calculations showing the resulting projective map is a closed immersion.
It must handle the one-gon and two-gon as well as longer polygons, in arbitrary
characteristic. No complete checked prototype or <=240-line decomposition of
these geometric proofs is claimed here.

The general 0B5X/0B5Y route additionally needs degree for invertible sheaves on
components and the positivity-to-ampleness theorem. Finite locally free rank
of the divisor subscheme does not provide that theorem. Relative Serre
vanishing consumes an existing very-ample presentation and cannot construct
one from the support condition.

Generalized curves with group action, compatible morphisms and coherent
pullback, level generators and descent, geometric ampleness and isomorphism
classes remain required before the moduli presheaf. These prerequisites are
not supplied by packaging the boundary example in a record.

## Boundary of the checked result

The canonical-section nonvanishing theorem is local on a Cartier chart.
Every line bundle is locally trivial, so this result alone cannot establish
ampleness or global generation. `DivisorPowerVeryAmple` proves an equivalence
of the two existing presentation targets and a conditional embedding adapter;
it proves no positive-power existence assertion.
