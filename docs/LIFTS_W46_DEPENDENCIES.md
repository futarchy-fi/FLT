# Lifting gates after W46

The formal scope below is checked by building the named modules, linting each
module separately, and printing the axioms of every named declaration.
The untracked `Scratch/LiftsW46/validate.py` implements those checks; the final
handoff records their receipts and checked-at time. No endpoint lifting result
is claimed by these local leaves.

## R1b2: coefficient projectors and strong grading

`CoactionBasisProjectors` constructs a degree coefficient as the tensor
coefficient of a coaction. Coassociativity implies homogeneity and orthogonal
idempotence. Counitality implies the finite sum of projectors is the identity.
`GroupAlgebraCoactionBasis` identifies the diagonal and augmentation with the
standard group-algebra comultiplication and counit, and verifies its
multiplicative basis. `CoactionBasisMultiplication` proves how coefficients shift under multiplication
by a homogeneous element. These are structural coalgebra statements, without
a supplied grading decomposition or strong-grading conclusion.

`CoactionDescentLaws` transfers the coassociativity and counit equations from
middle Hopf coordinates. `HopfPointFiberCoactionLaws` proves the needed
compatibility for W44's actual `pointFiberCoaction`; equality on middle
coordinates determines a linear map from the whole fibre.
`HopfPointFiberProjectors` constructs the actual fibre projectors, proves their
homogeneous images and orthogonality, and proves the two decomposition formulas.

`CoactionTorsorGrading.one_mem_opposite_product` applies the inverse torsor
comparison to `1 tensor b_i`, projects its two factors to degrees i^-1 and i,
and multiplies. The resulting element is one. `HopfPointFiberStrongGrading`
uses the actual canonical `pointFiberTorsorEquiv`, not a newly supplied
comparison. It proves both opposite-component invertibility and
H_i H_j = H_(ij). `HopfPointFiberGradedGenerator` then constructs the local
homogeneous unit, its spanning equality, its unique integral power parameter,
and its actual evaluated Hopf-difference ratio.

The inputs still include a basis b of the integral augmentation-kernel algebra
indexed by a finite group, b_1=1, b_(ij)=b_i b_j, and compatibility of the
diagonal comultiplication with the actual quotient map out of the middle Hopf
algebra. The sum-to-identity projector theorem additionally checks compatibility
with the actual Hopf counit. A cyclic multiplicative kernel is a special case.
No `hstrong`, generator, parameter, evaluation identity, or conclusion-assuming
record field is an input to these new fibre constructions.

**Remaining R1a2:** construct this integral multiplicative-kernel basis and the
constant quotient identification for the intended arithmetic ordinary model.
The W46 theorem eliminates the subsequent strong-grading obligation; it does
not identify an arbitrary integral kernel with mu_p. These structural inputs
must be produced by the integral model, not moved into an assumed lifting record.

## R1b3/R1c: the missing comparison is still arithmetic

The constructed unit now gives an integral parameter and an evaluated Hopf
root ratio without `hstrong`. Identifying that ratio with W42's class still
requires the actual integral-to-generic rank-one identifications. Specifically:

1. Identify points of the integral fibre with vectors in the actual residual
   ordinary filtration above the chosen quotient vector.
2. Prove that the Hopf difference corresponds to the injected-line difference
   of the quotient-normalized Galois translate. W42 uses the beta^-1 normalized
   section orbit in `OrdinaryFiltration.cocycleOf`; an unnormalized Galois
   translate does not supply this comparison when beta is nontrivial.
3. Transport the root-valued cocycle through the actual Hom coefficient map,
   then prove equality in `ContinuousClass` and independence of the section.
4. Prove the resulting class respects the unramified twist and descends through
   the residual coefficient extension. Existing abstract twist equalities do
   not by themselves identify this constructed integral class.

No comparison isomorphism or cocycle equality has been introduced as a field
standing in for these proofs.

## S0a2/S0a3: a genuine finite ramification leaf

`FiniteInertiaExponent` starts with a finite faithful action on a DVR of residue
characteristic p, a uniformizer, and an actual identification of its residue
field with F_p. It defines theta from reduction of g(pi)/pi. The existing
`uniformizerCharacter_ker_isPGroup` theorem and coprimality with p-1 prove
kernel containment for every prime-field line character. Consequently the
W45 filtered-action obligation is proved for this finite model.

If this actual theta is surjective, the normalized exponent and its actual
character equation follow. Surjectivity is an explicit hypothesis, not proved
for every finite model. This leaf does not assert that the kernel of the
absolute niveau-one character is a p-group: it generally is not.

Remaining: construct the finite model through which the intended absolute
ordinary representation factors and compare its tame character with the
specified absolute character; address residue fields larger than F_p;
construct actual niveau-two data; identify the non-peu cyclotomic branch; prove
the symmetric-power composition-factor comparison. No Serre-weight evaluation
or arbitrary-p Raynaud classification API is assumed.

## L20/D1a: a specified framed quotient condition

`FramedQuotientIdeal` forms the closed ideal generated by the matrix equations
rho(g)[q,j] = chi(g) delta_(q,j). A continuous parameter map kills it exactly
when the chosen coordinate projection has that quotient character. The row
condition survives coefficient changes; an actual nonzero solution proves
properness. The closed quotient classifies precisely these equations.

`FixedResidualQuotientIdeal` uses W45's constructed `fixedQuotientGaloisRep`
as the target. It gives the corresponding subfunctor of framed parameter maps,
its explicit equations, and the quotient factorization equivalence.
This is a quotient coordinate specified by the framing. It does not prove
that every deformation has a quotient line, or that an existential unframed
quotient condition is closed. The parameter ring U and its matrix representation
must still be instantiated with the intended universal framed deformation and
local restriction. Properness must then come from its residual solution.
Simultaneous arithmetic conditions still need their own ideal classifications.

## Lp0

`LIFTS_W46_CRYSTALLINE_CONTRACTS.md` specifies period objects, integral
Barsotti–Tate models with coefficient action, recovery of the given lattice,
finite-flat reduction comparisons, and deformation effectivity. It states
Hodge–Tate signs, coefficient-degree heights, and the separate p=2 scope.
These are implementation contracts; no crystalline comparison theorem has
been proved or postulated by W46.
