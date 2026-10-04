# Lifting gates after W47

The listed proofs are checked by serial module builds, individual module lint,
and `#print axioms` for every named declaration. Saved receipts, source hashes,
checked-at time and the merged-root build are recorded in the untracked
`LIFTS_W47_RESULT.md` and `Scratch/LiftsW47/`. No lifting endpoint is claimed.

## R1b3: integral points and the normalized difference

`IntegralModelPoints` constructs `FF.integralPoints` from the existing generic
point equivalence and tensor restriction. It proves addition, Galois action and
naturality for the specified integral morphisms. This is evaluation on integral
coordinate rings with values in the algebraic closure, not a claim that those
values lie in the base valuation ring.

`OrdinaryModelFiberPoints` applies that construction to the actual closure and
contracted quotient in `ordinaryModelExtension`. Both integral maps evaluate to
the original injection/projection. The tensor-product fibre at an integral
quotient point is equivalent to vectors over its corresponding quotient value.
The point equivalence is constructed; none is supplied as a comparison premise.

`OrdinaryNormalizedDifference` reuses W42's `cocycleOf_spec`. It proves that the
actual Hopf inverse/convolution difference is evaluation of vector subtraction.
For the fibre points corresponding to w and beta(g)^-1 g(w), the evaluated
inverse-torsor difference, restricted to middle coordinates, equals evaluation
of the injected Hom-cocycle coefficient at 1. Its two point-restriction premises
specify those vectors; they are not assumptions of a cocycle comparison theorem.
The previous module supplies the fibre equivalence for constructing such points.

Still required before the integral Kummer argument closes:

1. Identify the integral kernel as the appropriate multiplicative group scheme,
   and construct the compatible basis required by W46. Schematic closure alone
   does not establish this classification, especially for non-prime coefficients.
2. Construct the integral quotient point above the chosen ordinary quotient
   vector. A point with values in the generic algebraic closure is insufficient.
3. Transfer the evaluated multiplicative root ratio through the actual kernel
   coefficient map, proving equality with the continuous Hom class. The new
   middle-coordinate identity does not construct that root coefficient map.
4. Prove the integral construction respects the unramified twist and descends
   through residual coefficient extension. W42's abstract class identities remain
   reusable but do not by themselves establish integral descent.

## S0a2 and S0a3

`FiniteCoefficientWildKernel` proves that units of every finite field of
characteristic p have order prime to p. Consequently every character from the
actual finite DVR inertia group to such units kills the actual uniformizer
character kernel. It derives the ordinary line action identity over those
coefficients without identifying the DVR residue field with F_p.

This removes W46's prime-field coefficient restriction for the wild-kernel
identity. It does not construct the absolute-inertia comparison or prove
surjectivity of a specified niveau-one character. Larger-residue tame character
comparisons, niveau-two data and the non-peu branch remain open. S0a3 still needs
the symmetric-power composition-factor comparison specified by
`LIFTS_NUMERICAL_WEIGHT_CONVENTION.md`; there is no numerical Serre-weight
implementation or arbitrary-p Raynaud classification hidden in these modules.

## L20/D1a: the actual universal ring and constructed framing

`UniversalLocalQuotient` instantiates W46's closed matrix ideal on the actual
`profiniteFramedLimitObject` and `profiniteUniversalLift`, restricted along a
specified local group homomorphism. The residual row proves properness via the
actual residue map. Its quotient classifies continuous framed lifts satisfying
that row, using `profiniteFramedLimitHomEquiv`.

`OrdinaryAdaptedFrame` derives a frame from exactness of the residual filtration
and a vector above one, with no equivariant-splitting hypothesis. It proves that
the second coordinate is the original quotient and computes the matrix row.
`OrdinaryFramedRepresentation` constructs that matrix representation and proves
continuity from the original orbit maps, including its inverse matrices.

`OrdinaryUniversalQuotient` selects a quotient lift, applies that frame and
constructs the actual universal quotient object and classification equivalence.
Its residual-row obligation is now a theorem. `OrdinaryQuadraticUniversalQuotient`
further supplies the fixed sign lift of the residual quadratic quotient, proves
its reduction, and instantiates the object/equivalence with that character. No
nonzero characteristic-zero solution, arbitrary quotient line in a deformation,
or proper-ideal premise is an input to these last constructions.

This is a specified quotient in the constructed frame. Applying it to the
intended arithmetic local restriction still requires the actual residual
filtration and quadratic quotient action; this work does not derive those
from the full local hardly-ramified hypothesis. Closedness of an existential
unframed quotient condition is not proved. The other local ideals, determinant
conditions, simultaneous effectivity and global dimension gates remain open.

## Lp0: reuse the family period objects

The family lane's `PADIC_COMPARISON_FOUNDATIONS.md` and existing modules already
construct the tilt, theta, B_dR, the logarithmic period t and the fixed-field
theorem for the original action. W47 imports these objects without copying them.
`ComplexDeRhamEigenperiods` proves that every eigenvector with character chi^n,
for integer n, is a unique Q_p multiple of t^n, by dividing by t^n and applying
the existing fixed-field theorem. It proves the converse transformation law.
For the covariant Tate twist Q_p(1), invariant coefficients have character
chi^-1 and hence use t^-1; the weight convention remains -1.

This is a rank-one de Rham period calculation. B_cris, its Frobenius and map to
B_dR, the crystalline comparison, filtered tensor invariants and their rank
statements, coefficient naturality, integral classification (including p=2),
and lattice/finite-flat recovery remain required by
`LIFTS_W46_CRYSTALLINE_CONTRACTS.md`. Eigenperiods alone do not discharge C0 or Lp0.
