# Global Selmer contracts after the C1 audit

Source inspection: 2026-10-04. Recheck with the source paths below and
`rg -n 'Proposition 4.5|Corollary 4.7|Theorem 10.1' Scratch/kw-proofs.txt`.
The source is Khare–Wintenberger II, author manuscript
<https://www.math.ucla.edu/~shekhar/papers/proofs.pdf>, §§4 and 10.
These are proof obligations, not implemented theorems or assumptions to add
as fields. Every eventual Lean module must be at most 200 lines.

## The ring distinction must be preserved

The existing `Deformation.WittCoefficients.flatObject` is a quotient of the
continuous **framed** universal object and retains a specified quotient row
at two. KW II §10.1 defines its global framed ring by a completed tensor
product with the selected local rings. It then defines the **image of the
unframed universal ring** inside that ring. Theorem 10.1 proves finiteness
as a Zp-module for this image, not for the full framed ring. Corollary 4.7
passes from an unframed characteristic-zero point to a framed one using
formal smoothness and allows a finite coefficient extension.

Consequently, do not assert that the current framed HR quotient is finite
as a p-adic module by citing Theorem 10.1. Construct the appropriate
unframed image and prove its comparison to our functor, including how the
specified row is recovered by a frame choice. Noetherianity of a framed
ring and module finiteness of an unframed image are different gates.

W64 constructs `hardlyTraceImageObject`, the closed-kernel presentation of
the actual universal trace-ring image inside `hardlyFlatObject`, with its
original residue field. `hardlyTraceImageEquiv` identifies it with the closed
trace subalgebra. `exists_hardlyTraceImageLift_with_row` constructs a descended
representation and a strict frame recovering the original HR representation
and its row at two. The descended representation has the original determinant
and is unramified away from 2p (`HardlyRamifiedTraceArithmetic`).

This is not yet the comparison with KW II's completed tensor product or a
proof of finite-flat descent to the smaller image ring. W68 proves
Noetherianity of both actual rings; p-adic module finiteness is still missing. The generic theorem
`ProartinianCat.imageObject_isNoetherian` requires a Noetherian **source**;
Noetherianity of a framed target would not imply Noetherianity of its subring.
Check the saved W64 evidence with `python3 Scratch/LiftsW64/check.py`.

`DeSmitLenstra/FramedCompletion` proves Noetherianity with a **finite group**
parameter. `ProfiniteUniversalLift` constructs a limit over finite quotients;
Noetherianity does not follow by taking this limit. W67/W68 instead supply
arithmetic control of the continuous tangent space and a power-series presentation.

W65 proves the finite counting part of the arithmetic tangent strategy.
`finite_representations_discr_bdd` applies Hermite to the **actual kernel
fields**, then counts the finite possible coefficient functions on each
finite Galois group. `HardlyRamifiedFramedParameters` and
`HardlyRamifiedFiniteParameters` inject parameter maps into these continuous
representations and prove uniform degree bounds and pointwise inertia
triviality. Both give finiteness conditional on a uniform discriminant bound.
`HardlyRamifiedParameterComparison` uses the specialized recovery frame to
identify kernel fields for a framed map and its trace restriction. It does
not show all trace-image maps extend to the framed quotient.

W66 proves the selected-inertia comparison for the exact parameter fields:
`HardlyRamifiedParameterUnramified` gives arithmetic unramifiedness outside
{2,p}, over both the integers of Q and Z, and vanishing different exponents.
`FinitePrimeDiscriminantBound` and `HardlyRamifiedParameterBounds` now reduce
the uniform discriminant estimate to bounds for normalized different
exponents at 2 and p. This is a conditional reduction, not Noetherianity.

`DiscreteValuationRing.UniformizerDifferentBound` proves the local estimate
`v(different) ≤ v(e) + e - 1` for a totally ramified uniformizer power basis,
and proves that rank times a base uniformizer lies in the different of a
finite totally ramified DVR extension without a chosen basis as input.
`HenselianDifferentBound` constructs the unramified coefficient ring and
uses different transitivity to remove the total-ramification hypothesis.
`Padics.DifferentBound` proves that p^(N+1) belongs to the different of every
finite Henselian DVR extension of Zp with integral rank at most N.

W67 instantiates this bound on the full completed integer rings.
`NumberField.Completion.RankBound` bounds the local integral rank by the
global degree. `Completion.UniformDifferentBound` uses the proved
Henselianity and the original p-adic base isomorphism; the different remains
over that original base. `UniformDifferentExponent` compares local and
global exponents at every prime above a rational prime.
`HardlyRamifiedParameterFiniteness` proves the explicit bound
`(2*p)^((N+1)*N)` and unconditional finite coefficient parameters for each
finite discrete test ring, with `N = Nat.card (GL (Fin 2) A)`.

`DualNumberTest` constructs the finite test object with the original residue
field. `ContinuousTangent` identifies its parameter maps with continuous
coefficient-linear Leibniz functionals at the specified residue map.
`HardlyRamifiedTangentFinite` applies the arithmetic counting theorem to
prove finite dimension of these tangent spaces for both the actual framed
HR quotient and, under irreducibility, its trace image.

W68 closes the topology and Noetherianity gap. `FiniteTangentSeparation`
uses cotangent duality only after killing the coefficient maximal ideal in
a discrete quotient. `ContinuousTangentAdic` compares the common continuous
tangent kernel with the closed relative-square ideal. Compact Nakayama and
finite quotient representatives give actual maximal-ideal generators.
`PowerSeriesPresentation` constructs a surjection from a finite-variable
power-series algebra over the original coefficient ring, complete for the
variable ideal. Generators include coefficient directions, so the original
coefficient ring need not be complete. `HardlyRamifiedNoetherian` proves
Noetherianity and adic completeness of both actual HR rings independently;
no Noetherianity assertion about the unrestricted trace source is made.
The G0/G1 Selmer identification and D3 module finiteness remain separate.
Check saved evidence with `python3 Scratch/LiftsW68/check.py`.

## Required arithmetic objects

Start with the original finite residual field k, odd prime p, and rank-two
HR representation rho. Use its proved absolute irreducibility, oddness and
cyclotomic-restriction irreducibility; do not add them as new unexplained
premises or route them through an unavailable numerical weight API.

Use the actual maximal extension of Q unramified outside {2,p,infinity}.
Construct its profinite Galois group G_S and prove rho and the required
arithmetic deformations factor through it. Local maps into G_S must be
induced by the chosen embeddings of algebraic closures. Independence of
these choices is by conjugation, not an equality of arbitrary embeddings.

Construct the k-module M = trace-zero endomorphisms of V, with action
`g • a = rho(g) a rho(g)^(-1)`. For odd p, the trace pairing identifies
M's linear dual with M; prove nondegeneracy rather than assume it. The Tate
dual is `Hom_k(M,k)(1)` with its actual cyclotomic action. Do not replace it
with an abstract carrier named `CartierDual` without the action comparison.

## Gates and acceptance artifacts

| Gate | Required construction and checkable conclusion | Existing inputs / missing bridge |
|---|---|---|
| G0a | Continuous H^0, H^1, H^2 of G_S and each local group on M and its Tate dual; k-linear restriction maps and independence of embedding choices. | `LocalClassFieldTheory/ContinuousCochainComplex`, `ContinuousRestrictionCohomology` provide general complexes/restriction. Construct the actual arithmetic group/actions and prove finite-dimensionality. |
| G0b | For each place, identify the tangent image L_v of the **specified local deformation functor** in H^1(Q_v,M); prove invariance under strict equivalence and exact compatibility with framing. | At p use the integral finite-flat/crystalline comparison, not merely weights. At two retain the fixed lifted unramified quadratic quotient, including when rho is unramified. Away from 2p use unramified classes. At infinity use oddness and the correct p-odd local convention. |
| G0c | Construct local Tate pairings into k and prove perfectness for these finite modules. Define L_v-perp as the actual annihilator under these pairings. | Existing Kummer/Artin comparisons are not a proof of local duality for the full adjoint module. Prove the coefficient and trace-pairing comparisons. |
| G0d | Define H^1_L as the kernel of localization to the product H^1(Q_v,M)/L_v, and likewise for the dual. Prove arithmetic finiteness, Poitou–Tate exactness and the Greenberg–Wiles dimension identity. | `PoitouTateData.orderFormula` is an input field; `greenbergWilesOrderFormula` projects it. Neither supplies this gate. Prove the sequence and derive the identity, including the infinity correction. |
| G1a | Identify the global deformation tangent space with the actual Selmer group, and construct the obstruction to lifting across every small Artin extension. Vanishing must produce a compatible lift. | Must cover determinant and all local conditions simultaneously. An arbitrary vector space with the expected dimension is insufficient. |
| G1b | Construct the surjection from the completed tensor product of local framed rings with g power-series variables to the global framed ring, and bound the minimal relation count by dual Selmer dimension. | KW II Lemmas 4.4/4.6; construct the pairing on J/mJ and prove injectivity. Do not put a presentation or relation bound into a record. |
| G1c | Combine the local dimension bounds and G1b to obtain the absolute-dimension lower bound for the **correct unframed image**. | KW II Proposition 4.5. Track framing dimensions, local scalar automorphisms and the image-ring comparison explicitly; the conclusion is dimension >= 1. |
| M0 | Construct the residual modular seed and auxiliary totally real fields, and prove the exact local/disjointness hypotheses of Theorems 6.1/8.2 and Propositions 9.2/9.3. | This is residual arithmetic, not potential modularity of an assumed desired characteristic-zero HR lift. Numerical weight extraction is still an S0 gate. |
| D3 | Apply the source-matched modularity comparison to prove p-adic module finiteness of the unframed image from §10.1. | Needs M0 and the local deformation rings of Theorem 3.1. No formal consequence of prorepresentability or Noetherianity gives this finiteness. |
| D4 | Prove p nonnilpotent using D3 and G1c; extract a prime avoiding p and its finite characteristic-zero domain quotient. | If a finite Zp-module ring has nilpotent p, it is Artinian and has dimension zero. Use `LiftPrimeAvoidingP` and `LiftDomainFree` only after this contradiction is established. |
| I0 | Recover a continuous representation over a finite local p-adic order with **original** residue field k; prove finite freeness, HR at every open quotient, and exact tensor-conjugacy with rho. | Normalizing a point's coefficient domain can enlarge its residue field. Use the actual image/order or prove descent; do not assert an algebra from the larger residue field to k. |

The sequence G0a–G1c is the Selmer gate. The conclusion required from it is
a proved dimension bound on the matched ring, not a characteristic-zero
point supplied as input. D3 is a separate global modularity gate. Together
they feed D4 and I0, which can finally discharge the original `lifts`
existential. Each comparison must use the same rho, determinant, local
quotient and coefficient maps.

## Earlier gates that remain ahead of global assembly

1. S0a2/S0a3: W59 constructs general local normality and finite-model
   uniformizer transfer. A power relation in a common residue field does not
   permit cancelling a noninvertible exponent. Niveau-two, non-peu branches,
   normalization independence and actual symmetric-power composition
   factors remain. No numerical Serre-weight evaluation is available here.
2. R1: W63 constructs the actual quotient-twisted Hopf algebra, tensor
   comparison, triple-overlap cocycle, Hopf-compatible scalar recovery and
   finite-flat model. `GroupScheme.OrdinaryUnramifiedUnitClass` transports
   the ordinary filtration and proves the unit class and independent peu
   condition for finite residual coefficients, small ramification, an
   unramified quotient and a whole-local cyclotomic Hom character. The
   whole-local/inertia comparison needed for general S0a3 remains. Check
   `python3 Scratch/LiftsW63/check.py` for saved source and validation evidence.
3. Lp0: prove the integral PD-envelope universal property for arbitrary PD
   targets, with p-compatibility, not just minimality within A_inf[1/p].
   `DividedPowerHull`/`ComplexDividedPowerHull` only prove the latter. Prove
   Frobenius stability, p-adic completion and B_cris, its map into the exact
   `ComplexBDeRham`, tensor-invariant comparison, and recovery of the original
   integral lattice at every level. Frobenius does not preserve the theta
   ideal; the source's actual theta-generator computation forbids using a
   theta-adic extension in place of the crystalline construction.
4. The finite coefficient order: W68 proves arithmetic Noetherianity and
   adic completeness. The order carrying a lift still needs the selected-local
   comparison, integral finite-flat descent and D3/D4/I0. Do not report the
   candidate Eisenstein coefficient rings of W58 as that order.

These unresolved inputs are mathematical gaps, not a request for permission.
The lifting admission and its dependency at the FLT endpoint remain until
the exact integral assembly is proved.
