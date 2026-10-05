# Ampleness and degree on proper integral curves

`ampleLineBundle_iff_curveSheafDegree_pos` proves Stacks 0B5X for a proper
integral scheme over a field with topological Krull dimension exactly one.
The forward implication requires dimension one: a zero-dimensional proper
scheme can have an ample line of degree zero. The reverse implication,
`ampleLineBundle_of_curveSheafDegree_pos`, only requires dimension at most one.
Both use the existing Euler-characteristic degree and affine-section-open
ampleness predicates.

## From ideal cohomology to affine section neighborhoods

`ampleLineBundle_of_ideal_h1_vanishing` applies to any proper scheme over a
field, without integrality or a dimension bound. Its hypothesis is that each
actual ideal sheaf I has some positive exponent n with H¹(I ⊗ Lⁿ) = 0.
It constructs the affine section cover rather than assuming it.

For a closed point x in an affine trivializing neighborhood U, take I to be
the ideal of X minus U and J to be the reduced ideal of x. Their supports
are disjoint, so I + J = O. The modules and maps of

    0 → I ∩ J → I → O/J → 0

are constructed in `ComaximalIdealSequence`. The kernel proof uses local
sections of the actual intersection ideal; affine comaximality proves the
quotient map is an epimorphism. Tensor exactness and the actual cohomology
connecting map then lift all global sections of (O/J) ⊗ Lⁿ.

The closed subscheme J is finite over the field, so its pulled-back line
is trivial. Lift its unit through the line projection formula. The
`idealReduction_projection` identity proves that reduction of the lifted
section is its actual pullback. Exact pullback of generator opens proves
that the resulting section generates at x. Its ideal multiple bounds its
open by U; a trivialization identifies that open with an affine principal
open. Finally a closed subset of a compact scheme has a closed point, so
these opens cover every point.

This bypasses an explicit residue-field coordinate identification: the
finite closed subscheme's line trivialization provides the same generator,
with its projection and pullback compatibility proved.

## From ampleness to positive degree

Choose an ample positive-power section generating at the generic point.
Its map O → Lⁿ is injective and has coherent finite-support cokernel Q.
The cokernel is nonzero: otherwise the section generates everywhere, so
its affine generator open is the whole curve. A proper affine scheme over
a field is finite, contradicting dimension one.

`FiniteSupportEulerPositive` proves that a nonzero coherent finite-support
sheaf has positive Euler characteristic. Closed descent and affine section
reconstruction show H⁰ detects zero; positive cohomology vanishes.
Additivity gives deg(Lⁿ) = χ(Q) > 0, and tensor-power degree gives deg(L) > 0.

## Progress toward finite-surjective descent

`AmpleLineBundle.coherent_vanishing` proves full Serre vanishing over a
Noetherian coefficient ring. A positive line power has a very ample
presentation. Projective vanishing for the finitely many residual twists,
combined with quotient and remainder of exponents, supplies one bound for
all large exponents and all positive cohomological degrees.

`finitePushforward_ample_coherent_vanishing` transports this along a finite
morphism g when g*L is ample. For every coherent M on the source it proves
eventual vanishing of H^q(X, g_*M ⊗ Lⁿ), using the actual line projection
formula and affine direct-image cohomology comparison.

This is not finite-surjective ampleness descent. The remaining proof must
extend vanishing from direct-image coefficients to all target ideals.
Stacks 0B5V does so using the support dévissage of 01YM (30.12.8), finite
surjective witnesses of 01YO (30.13.1), and ideal/direct-image compatibility.
The existing `GenericRankOneWitness` demands residue dimension one and a
`TwoOutOfThree` property. A finite cover's generic residue extension can
have larger dimension. Also, positive-cohomology vanishing alone does not
supply the left clause of `TwoOutOfThree`: H¹ of a kernel additionally
requires surjectivity on H⁰. Those hypotheses must not be silently assumed.
The new ampleness criterion is over a field; the general Noetherian-base
version of 0B5U also remains for the full scope of 0B5V.

Subsequent ordered work remains: 0B5Y, F3 on smooth and polygon fibres,
arbitrary-base L1–L2 with 0D2S, and A7–A8. These modules do not remove
`Mazur_statement` from the Fermat endpoint.

## Verification

`W73_MODULES.txt` lists the new modules. Each builds separately with
`LEAN_NUM_THREADS=2 lake build MODULE`. `python3 W73_VALIDATE.py` runs
one-module lint commands sequentially and audits every originating
declaration against only propext, Classical.choice, and Quot.sound.
No whole-library lint is used. `W73_CHECK_SOURCE.py` checks source hashes,
line caps, admission-token absence, imports, validation artifacts, commit
ownership, and the final merged-main/root-build evidence. Those scripts
and validation logs remain untracked outside FLT/ and docs/.
