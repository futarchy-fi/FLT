# P13: constructing the divisor representative

This is a proof design and leaf order, not a representability theorem.
Each proposed Lean module has a 240-line cap; split it further if necessary.
Use actual ideals, quotient rings, schemes and universal maps throughout.

## Proof source and chosen route

Use the Hilbert scheme of points construction in the Stacks Project,
[Section 44.2, tag 0B94](https://stacks.math.columbia.edu/tag/0B94):

- Lemma 44.2.1: descent of actual finite locally free closed subschemes.
- Lemma 44.2.3: imposing an ambient closed immersion gives closed equations.
- Lemma 44.2.5: affine Hilbert charts from multiplication constants and a
  prescribed basis of the quotient algebra.
- Proposition 44.2.6: glue these charts when finite sets in a fiber lie in an
  affine open of the ambient scheme.
- Remark 44.2.7: relative ampleness is one sufficient source of that hypothesis.

These statements were read from the live source on 2026-10-08. They are proof
sources, not imported Lean results. In particular Proposition 44.2.6's affine
neighborhood hypothesis must be proved for the intended curve application.
Coordinate that geometric input with G1; do not assume it from smoothness.

The broader Hilbert algebraic-space theorem in Stacks, *Quot and Hilbert Spaces*,
`proposition-hilb`, does not by itself provide a scheme. The chosen construction
uses explicit affine charts and scheme gluing instead of invoking that theorem.

## Why permutation invariance is insufficient

The ordered family has an invariant ideal, but this does not supply descent
along its map to a representative. Even for the affine line, the full overlap
of the ordered-root map contains more than the permutation graphs.
For example, over `k[e]/(e²)`, the tuples `(e,-e)` and `(0,0)` both yield `t²`.
They cannot become permutations of one another after faithfully flat extension:
faithful flatness preserves the nonzero element `e`.
Thus the permutation-orbit fpqc sheaf is not the Hilbert functor on arbitrary
nonreduced test schemes. A categorical invariant-ring quotient and a sheaf
quotient must not be conflated.

`SymmetricAffineLineParameters` supplies coefficient coordinates and unique
factorization of invariant polynomial maps. Its `parameterMap` is an actual
scheme map. That result alone supplies neither a universal finite divisor nor
classification of all divisors. Use the Hilbert construction below for the
latter, with the affine-line coefficient calculation as a comparison.

## Next leaves in dependency order

1. **HilbertChartEquations.** For a base ring `R`, generators `i : I`, and
   quotient dimension `d`, introduce polynomial variables `c(k,l,m)`, `b(l)`,
   and `x(i,l)`. Define the ideal of commutativity, associativity and unit
   equations. Associativity uses sums over the intermediate basis index;
   it is not an equality of single products of structure constants.
2. **HilbertChartAlgebra.** On `Fin d → Q`, for the actual equation quotient
   `Q`, construct multiplication and the unit vector from those constants.
   Prove the commutative-ring and `Q`-algebra laws coordinatewise. Its underlying
   module is the actual free coordinate module, including `d = 0`.
3. **HilbertChartGeneratorMap.** Construct the evaluation homomorphism from
   `MvPolynomial I R` to the universal algebra. Prove its coordinate formula.
   No surjectivity is assumed or claimed at this stage.
4. **HilbertChartBasisRelations.** For a prescribed list of `d` polynomials
   `w(j)`, quotient by the coordinates of `eval(w(j)) - e(j)`. Base-change the
   algebra, prove those equalities, then prove evaluation is surjective.
5. **HilbertChartUniversalClosedFamily.** Take the spectrum of that algebra
   and construct the closed immersion into the actual affine base change.
   Its structure map is finite locally free of rank `d` by its explicit basis.
6. **HilbertChartClassification.** Given an arbitrary finite locally free
   quotient whose images of `w(j)` are a basis, read off its multiplication,
   unit and generator coordinates. Prove the defining equations, construct
   the parameter map, and prove inverse identities and uniqueness.
7. **HilbertChartBasisOpen.** For any family, the locus where `w(j)` form a
   basis is the actual determinant-invertibility open. Prove compatibility
   with arbitrary base change and the corresponding factorization property.
8. **HilbertAffineChartCover.** Extract a basis from the images of ambient
   functions at each residue-field fiber; lift it to a neighborhood. This
   covers every quotient family, including families not given as section sums.
9. **HilbertAffineChartGluing.** Construct overlap maps from classification,
   prove cocycles using uniqueness, glue the schemes and universal ideals,
   and prove the resulting representing equivalence is natural in the base.
10. **HilbertAmbientRelations.** Impose generators of an arbitrary ambient
    affine ideal through coordinates in the free quotient algebra. Prove the
    closed factorization criterion and classification for a general affine
    scheme. Infinite sets of generators are allowed; finite presentation is
    a separate conclusion when the ambient presentation is finite.
11. **HilbertSupportOpen.** For an ambient open `U`, remove the finite image
    of the divisor's part outside `U`. Prove that this is the precise base
    open on which the whole divisor lies in `U`, with base-change compatibility.
12. **HilbertCurveRepresentative.** Apply the separately proved common-affine
    neighborhood input, glue the affine Hilbert representatives using the
    support opens, and prove classification of all finite locally free closed
    divisors. Then prove the Cartier condition for these divisors on a smooth
    relative curve; do not replace that implication by a record field.
13. **OrderedHilbertClassifyingMap.** Apply the representing equivalence to
    the actual ordered family. Recover its ideal by universal pullback and
    prove permutation invariance by uniqueness. This supplies its classifying
    map without pretending that permutation invariance proves representability.

Each numbered entry may require several leaves; the cap is a source-file limit,
not a claim about the size of missing foundations. The first construction to
implement is the explicit equation ideal in item 1.

## Acceptance boundary

The P13 exit theorem must quantify over arbitrary test schemes and arbitrary
finite locally free effective divisors, not just tuples split into sections.
It must provide an actual representing scheme, its actual universal divisor,
a natural classification equivalence, and the ordered-family pullback identity.
Only then proceed to P14's Abel fibers and Riemann--Roch work.
