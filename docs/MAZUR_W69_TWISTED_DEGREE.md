# Finite divisor twists and Euler-characteristic powers

This layer extends the finite-divisor comparison from W68. It does not prove
positive-degree ampleness or remove the Mazur axiom.

## Contracts

Let `f : X ⟶ Spec k` be proper, let `I` define a finite effective Cartier
divisor D, and let L be locally free of rank one. The cohomological statements
use `Scheme.{0}`, matching the proper coherent-cohomology finiteness API.
The dual and tensor isomorphisms retain arbitrary universes.

| Module | Result |
| --- | --- |
| `LineSheafDualEvaluation` | The actual dual evaluation L∨ ⊗ L → O is invertible, by local triviality. |
| `FiniteSchemeLineCohomology` | A line on a finite scheme has H⁰ dimension equal to the scheme length; its closed pushforward has no positive cohomology. |
| `DivisorTwistedSequence` | Tensor the canonical divisor sequence by L and identify the quotient with the pushforward of the pullback of O(D) ⊗ L. |
| `DivisorTwistedDegree` | χ(O(D) ⊗ L) = χ(L) + length(D); positive-degree cohomology transition maps are surjective. |
| `DivisorPowerEulerCharacteristic` | χ(O(D)^n) = n length(D) + χ(O); degree of O(nD) is n degree(O(D)); positive length gives unbounded H⁰ dimensions. |
| `TensorPowerDistribution` | Actual tensor isomorphism M^n ⊗ N^n ≅ (M ⊗ N)^n. |
| `DivisorPowerTwistDegree` | χ(O(D)^n ⊗ L) = χ(L) + n length(D); an actual presentation O(D) ⊗ L ≅ O(E) gives χ(L^n) = n degree(L) + χ(O). |

Here χ means `curveEulerCharacteristic`, namely dim H⁰ − dim H¹, and degree
means `curveSheafDegree`. No geometric vanishing outside these two degrees is
needed for the twist formula: vanishing H¹ of its actual quotient makes the
six-term cohomology sequence end surjectively.

The quotient comparison is a global isomorphism of actual module sheaves,
constructed by tensoring `divisorCokernelClosedIso`, applying the closed
projection formula, and using tensor compatibility of pullback. A global
trivialization of L is not a hypothesis. On the finite divisor, the new dual
evaluation isomorphism supplies the inverse needed by the existing semilocal
Picard-triviality argument.

The divisor-presentation hypothesis in `DivisorPowerTwistDegree` is an
isomorphism of sheaves, not a numerical degree formula. Its existence for an
arbitrary invertible sheaf has not been proved. The theorem therefore cannot
be used unconditionally for the arbitrary line in Stacks 0B5X.

## Remaining route to F2

The [Stacks 0B5X proof](https://stacks.math.columbia.edu/tag/0B5X) uses the
power formula for an arbitrary invertible sheaf on an integral proper curve,
then produces a nonzero positive-power section with affine nonvanishing open.
It proves eventual H¹ vanishing for ideal twists using surjective transition
maps and eventual annihilation of each cohomology class.

The new results provide the effective-divisor twist formula, and the arbitrary
line power formula when a finite divisor presentation has been constructed.
They do not provide:

1. A finite effective-divisor presentation for every invertible sheaf on an
   integral proper curve, or an alternative proof of tensor-degree additivity
   through generic ideal embeddings and finite-support quotients.
2. The required affine nonvanishing section and eventual annihilation on the
   ideal-twist cohomology system.
3. The cohomological criterion that converts that vanishing to the repository's
   affine-section-open definition of `AmpleLineBundle`.
4. Finite-surjective ampleness descent (0B5V) and the component criterion (0B5Y).

The generic-ideal route has existing inputs in `GenericIdealInjection` and
`GenericIdealSupport`. To use it, one still has to prove invariance under line
twists for arbitrary coherent finite-support quotients and identify the
rank-one generic comparison for L. The present finite-scheme theorem treats
line coefficients, not arbitrary coherent torsion coefficients.

After F2, the ordered obligations remain F3 (smooth and polygon fibers),
L1–L2 (arbitrary-base fiber-to-neighborhood ampleness, 0D2S), A7 (compatible
ample cyclic-level isomorphisms, quotient and presheaf coherence), and A8
(exact-order rational points, finite étale subgroups and generator invariance).
No conclusion for those obligations follows from these numerical lemmas alone.
