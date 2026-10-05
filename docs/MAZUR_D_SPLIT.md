# Mazur track D: extension and local arithmetic

## D-W13: nodal label descent and a component bound

C1.5a.x.10 now has proofs of label addition for E₀ translations, equal-depth
opposite strict branches and two midpoint points. Equal labels are equivalent
to equal actual E/E₀ classes. The canonical `nodeComponentLabel` is an
injective function into Z/nZ preserving zero and negation, and the actual
component quotient is finite with cardinality at most n. Full additivity,
cyclicity and attainment of all n labels remain open.

Checked 2026-10-05 03:56 UTC: all 12 new modules passed foreground
`LEAN_NUM_THREADS=2 lake build MODULE` and individual `lake exe runLinter MODULE`
runs, warning-free. They have 76–99 physical lines each, cap 240. Evidence:
`Scratch/MazurDW13/*-build.log` and `*-lint.log`. The theorem audit and required
post-merge root build are recorded below after completion.

This replaces the general Néron-model prerequisite in the older C1 rows below.
For an elliptic curve over a complete DVR with perfect residue field, use a
minimal integral Weierstrass equation W and the actual subgroup E₀(K) of
points whose primitive projective reduction is nonsingular. The rational
component quotient means E(K)/E₀(K), not the geometric component group.
The applications use finite residue fields. Discriminant orders below are
normalized additive valuations, so n = ord(Δ) is a positive integer in the
multiplicative case. No general Néron mapping property is needed for these
local point-group assertions.

Each planned new module has cap 240 physical lines. Implementation order is
the table order; a case calculation and exhaustiveness are separate proofs.
Consumer labels describe dependencies, not completed downstream theorems.

| Leaf | Module / cap | Exact output | Consumer |
| --- | --- | --- | --- |
| C1.0 | Existing `EllipticReductionKernel` | `ellipticE0` is the nonsingular-reduction subgroup, for any integral equation over a valuation subring. Specialize it to a minimal equation over the complete DVR. | A1-C1; S1/S2 and C2/C3/Cp through C1.1. |
| C1.1 | `EllipticComponentQuotient` / 240 | Actual quotient E(K)/E₀(K), surjective quotient homomorphism, kernel E₀, and equal-class criterion by smooth reduction of P−Q. | A1-C1; S1/S2, C2/C3/Cp. |
| C1.2 | `EllipticGoodComponent` / 240 | Smooth special cubic implies E₀=E and trivial quotient; connect this to Mathlib's minimal-model `HasGoodReduction`. | Good branch of A1-C1; C2/C3 through good-reduction point counts. |
| C1.3 | `EllipticSingularDivisibility` / 240 | For integral coordinates x,y in an ideal I, a₃,a₄ in I and the curve equation imply a₆ in I². This is the point-exclusion calculation in the type II branch. | Additive bound A1-C1 via C1.6; S1 and C2/C3. |
| C1.4a.i | `EllipticNormalizedSingularity` / 240 | For a₃=a₄=a₆=0 over a field, prove the origin is the unique singular affine point, also in characteristics 2 and 3. Identify the coefficients after translating a supplied singular point. | Every bad-reduction branch of A1-C1; S1/S2, C2/C3/Cp. |
| C1.4a.ii | `EllipticNormalizedTypeII` / 240 | Combine C1.3 and C1.4a.i: a₃,a₄,a₆ in the maximal ideal and a₆ outside its square imply E₀=E and trivial quotient. This is the normalized type II calculation, before proving general normal-form existence. | C1.6a and additive A1-C1; S1, C2/C3. |
| C1.4a.iii.1 | `EllipticSingularVariableChange` / 240 | Transport singular affine points through arbitrary admissible variable changes. | Normal-form existence for all branches. |
| C1.4a.iii.2 | `EllipticSingularSmallChar` / 240 | Rational singular-point existence over perfect fields in characteristics 2 and 3, using the standard normal forms. | C1.4a.iii.3. |
| C1.4a.iii.3 | `EllipticRationalSingularity` / 240 | Prove Δ=0 iff a rational singular affine point exists over a perfect field, including the explicit short-equation formula away from 2 and 3. | C1.4a.iii.4. |
| C1.4a.iii.4 | `EllipticIntegralSingularTranslation` / 240 | Lift the singular residue coordinates and translate integrally with u=1; a₃,a₄,a₆ enter the maximal ideal, while Δ and c₄ are unchanged. | All bad-reduction branches. |
| C1.4a.iii.5 | `EllipticCuspTangent` / 240 | Identify the tangent cone, prove its repeated direction rational over a perfect field, and shear a normalized cusp to y²=x³. | C1.4a.iii.6. |
| C1.4a.iii.6 | `EllipticIntegralCuspNormalization` / 240 | Δ,c₄ in the maximal ideal imply an integral u=1 change putting all five coefficients in that ideal. | Initial additive normalization; higher valuation tests remain in C1.6. |
| C1.4a.iii.7 | `EllipticNodeTangent` / 240 | Identify the node polynomial with the scaled tangent quadratic; splitting and c₄≠0 yield a shear with a₁≠0 and a₂=a₃=a₄=a₆=0. | C1.4a.iii.8. |
| C1.4a.iii.8 | `EllipticIntegralNodeNormalization` / 240 | Lift the split tangent shear: a₁ is a unit and a₂,a₃,a₄,a₆ lie in the maximal ideal. | Initial split multiplicative normalization for C1.5. |
| C1.4b.i | `EllipticVariableChangeSmoothness` / 240 | Transform the two partial derivatives and prove nonsingularity invariant without assuming a smooth cubic. | Bad special fibers in C1.4b.iii. |
| C1.4b.ii | `EllipticVariableChangeIntegrality` / 240 | Integral unit coordinate changes preserve integrality of x and of the coordinate pair. | Infinity chart in C1.4b.iii. |
| C1.4b.iii | `EllipticVariableChangeReduction` / 240 | Integral and nonintegral affine charts together prove smooth reduction invariant. | C1.4b.iv. |
| C1.4b.iv | `EllipticComponentVariableChange` / 240 | Integral unit variable changes induce generic point-group equivalences carrying E₀ onto E₀, hence additive equivalences of E/E₀ commuting with the quotient maps. | Transport all branch calculations to A1-C1; S1/S2, C2/C3/Cp. |
| C1.5a.i | `EllipticNodeDepthStep` / 240 | Integral translations deepen a₃,a₄ from Iᵏ to Iᵏ⁺¹, preserve a₁, and change a₆ only in I²ᵏ, in every characteristic. | C1.5a.ii. |
| C1.5a.ii | `EllipticNodeDepthNormalization` / 240 | Iterate translations to any finite depth and compose with the initial split-node normalization. No completeness hypothesis. | C1.5a.iv. |
| C1.5a.iii | `EllipticNodeDiscriminantDepth` / 240 | Modulo deep a₃,a₄, Δ is a₆ times a unit; identify their ideal-adic depths. | C1.5a.iv. |
| C1.5a.iv | `EllipticSplitDepthModel` / 240 | Construct an integral u=1 model with a₃,a₄ in mⁿ⁺¹ and a₆ of exact depth n from the exact depth n of Δ. | Point-branch calculations. |
| C1.5a.v | `EllipticSplitOrderOne` / 240 | Prove E₀=E and the actual E/E₀ quotient trivial when split multiplicative Δ has order one; transport from the deep model. | Order-one case of C1.5. |
| C1.5a.vi | `EllipticNodeScaledEquation` / 240 | Cancel the common coordinate factor; identify the two tangent factors, exclusive branches below the midpoint, and unit factors at the midpoint. | C1.5a.ix. |
| C1.5a.vii | `EllipticNodePointDepth` / 240 | The actual integral equation bounds common coordinate depth by n/2 when a₆ has exact depth n. | C1.5a.viii. |
| C1.5a.viii | `EllipticNodeCoordinateFactor` / 240 | Extract primitive coordinates at some depth k≤n/2 for a principal maximal ideal; construct the scaled coefficient factors. | C1.5a.ix. |
| C1.5a.ix | `EllipticNodePointBranches` / 240 | Derive tangent branches from the deep coefficients below/at n/2, and identify smooth reduction exactly with common depth zero. | C1.5a.x. |
| C1.5a.x.1 | `EllipticNodeCoordinateUnique` / 240 | Primitive factorizations fix the depth and both quotients. | C1.5a.x.10. |
| C1.5a.x.2 | `EllipticNodeBranchLabel` / 240 | Signed depth labels; zero and midpoint rules; independence of factorization. | C1.5a.x.10. |
| C1.5a.x.3 | `EllipticNodeBranchInverse` / 240 | The actual inverse coordinate exchanges the strict tangent branches. | C1.5a.x.10. |
| C1.5a.x.4 | `EllipticNodePointCoordinates` / 240 | Unique primitive witnesses for actual generic points; existence outside E₀. | C1.5a.x.10. |
| C1.5a.x.5 | `EllipticNodeComponentLabel` / 240 | A function on actual generic points with zero fiber exactly E₀; no additivity assumed. | C1.5a.x.10. |
| C1.5a.x.6 | `EllipticNodeComponentInverse` / 240 | Actual generic negation negates the label, including smooth and midpoint cases. | C1.5a.x.10. |
| C1.5a.x.7 | `EllipticNodeSecantSlope` / 240 | Integral secant slopes at unequal depths and their reduced tangent directions. | C1.5a.x.10. |
| C1.5a.x.8 | `EllipticNodeSecantReduction` / 240 | Actual addition at an integral nodal tangent slope has singular reduction. | C1.5a.x.10. |
| C1.5a.x.9 | `EllipticNodeUnequalDepthAddition` / 240 | Positive unequal depths cannot sum into E₀ and give distinct actual E/E₀ classes. | C1.5a.x.10. |
| C1.5a.x.10.a | `EllipticNodeOppositeSlope` / 240 | Cancel the actual equal-depth slope; opposite strict branches exclude both nodal tangents. | C1.5a.x.10.m. |
| C1.5a.x.10.b | `EllipticNodeOppositeAddition` / 240 | Actual opposite-branch sums reduce smoothly in vertical, integral and nonintegral slope charts. | C1.5a.x.10.m. |
| C1.5a.x.10.c | `EllipticNodeOppositeLabels` / 240 | Label addition and opposite actual classes for equal-depth opposite strict branches. | C1.5a.x.10.m. |
| C1.5a.x.10.d | `EllipticNodeEqualDepthSlope` / 240 | Cancel the second actual slope identity and reduce it, including the tangent chart. | C1.5a.x.10.m. |
| C1.5a.x.10.e | `EllipticNodeMiddleAddition` / 240 | Unit tangent factors at the midpoint force smooth sums. | C1.5a.x.10.m. |
| C1.5a.x.10.f | `EllipticNodeMiddleLabels` / 240 | Midpoint label addition, annihilation by two and equality of all actual midpoint classes. | C1.5a.x.10.m. |
| C1.5a.x.10.g | `EllipticNodeLabelSeparation` / 240 | Equal signed labels determine depth; opposite strict labels detect opposite tangent tests. | C1.5a.x.10.m. |
| C1.5a.x.10.h | `EllipticNodeLabelFibers` / 240 | Equal labels imply equal actual component classes. | C1.5a.x.10.m. |
| C1.5a.x.10.i | `EllipticNodeSameBranchSlope` / 240 | The second divided denominator is a unit on the first strict branch, making slopes integral. | C1.5a.x.10.m. |
| C1.5a.x.10.j | `EllipticNodeSameBranchAddition` / 240 | Equal strict depths on the same branch cannot sum into E₀, including doubling. | C1.5a.x.10.m. |
| C1.5a.x.10.k | `EllipticNodeLabelDescent` / 240 | Actual component classes and nodal labels have exactly the same fibers. | C1.5a.x.10.m. |
| C1.5a.x.10.l | `EllipticNodeComponentBound` / 240 | Canonical quotient injection into Z/nZ, finite cardinality at most n, and all E₀ translation laws. | C1.5a.x.10.m. |
| C1.5a.x.10.m | Further leaves / ≤240 each | Compute the label of the remaining singular sums: unequal depths, equal strict depth on the same branch, and one midpoint plus a shallower point. Then package the additive map with kernel E₀. | C1.5a, C1.5b/c. |
| C1.5a | `EllipticSplitComponentClasses` / 240 | In split multiplicative normal form, construct a class map to Z/nZ and prove its kernel is E₀ by the valuation branches of point addition. | Split branch of A1-C1; C2/C3/Cp. |
| C1.5b | `EllipticSplitComponentOrder` / 240 | Lift all n classes over the complete DVR and obtain E/E₀ ≃+ Z/nZ; thus cyclic of order ord(Δ). | A1-C1; C2/C3/Cp. |
| C1.5c | `EllipticNonsplitComponents` / 240 | Compare E₀ under the unramified quadratic splitting extension, inject rational classes into geometric classes, and prove Galois acts by negation. Deduce cardinality at most 2. | A1-C1; nonsplit exclusions in C2/C3/Cp. |
| C1.6a | `EllipticTateTypeII` / 240 | Normalized type II: C1.3 excludes any singular reduction, so E/E₀ is trivial. | Additive branch A1-C1; S1, C2/C3. |
| C1.6b | `EllipticTateTypesIIIIV` / 240 | Normalized types III and IV: classify point cosets and bound their number by 2 and 3 respectively, including residue characteristics 2 and 3. | Additive branch A1-C1; S1, C2/C3. |
| C1.6c | `EllipticTateTypeIStar` / 240 | Normalized Iₙ* branches: iterate the valuation tests, prove termination, and bound point cosets by 4. Subdivide the iteration proof further if needed. | Additive branch A1-C1; S1, C2/C3. |
| C1.6d | `EllipticTateDualTypes` / 240 | Normalized IV*, III*, II*: bound cosets by 3, 2, 1 respectively from the remaining coefficient tests. | Additive branch A1-C1; S1, C2/C3. |
| C1.7 | `EllipticTateExhaustion` / 240 | Prove the Tate-algorithm branches exhaust minimal additive equations; the final rescaling alternative contradicts minimality. Combine to obtain finite E/E₀ of order at most 4. | A1-C1; S1, C2/C3; S2 before/after base change. |
| C1.8 | `EllipticSmoothSpecialGroups` / 240 | Parametrize the smooth singular cubic: additive group for a cusp, multiplicative group for a split node, norm-one group for a nonsplit node; prove compatibility with reduction addition. | S1, C2/C3/Cp; S2 after semistable base change. |
| S1 | `PrimeTorsionSemistabilityAway` / 240 | For a prime-order point with prime ≥17 away from residue characteristic, the component bound forces it into E₀; the additive smooth group and F3 then exclude additive reduction. | A1-S1, then C2/C3 and A2. |
| S2a | `EllipticSemistableExtension` / 240 | At the torsion prime ≥17 construct a semistable extension of ramification degree ≤6 from the minimal-equation cases. | A1-S2, then Cp. |
| S2b | `EllipticTorsionClosure` / 240 | Construct the finite-flat order-p closure and its generic/special-fiber comparisons over that extension; apply proved rigidity with e<p−1. Split construction into further leaves as needed. | A1-S2, then Cp and A2. |
| C2/C3/Cp | Original named modules / ≤240 each | Apply the quotient bounds, explicit smooth-group orders, F3 specialization and S1/S2 to the local prime-order point; retain the separate 2, 3 and p cases. | A1 component conclusions, then A2. |
| A2 | Further leaves / ≤240 each | Combine local component conclusions with G1/G2 cusp comparison and odd-prime abelian specialization at every bad prime. | Global Mazur argument; depends on the separate G1/G2 workers. |

Neither a Kodaira label with a supplied cardinality field nor a finite-group
bound assumed as a hypothesis proves C1.5–C1.7. The normal forms, quotient
comparisons, branch coverage and cardinality bounds must all be proved.
The existing elliptic E₀ specialization theorems do not supply the abelian
specialization required by A2. G1 (wt-r5a) and G2 (wt-r1e) retain their scopes.

### D-W13 implementation boundary

The first open subleaf is C1.5a.x.10.m. E₀ translation invariance and exact
component fibers are now proved; do not repeat their constructions. For two
strict equal-depth points on the same branch, the sum is proved singular,
but its exact depth and branch still need calculation. Unequal-depth sums
and a midpoint plus a shallower point also need exact labels. Opposite strict
equal-depth sums, midpoint pairs and all smooth translations are complete.

The bound at most n is unconditional under `SplitNodeDepth`; it requires
neither completeness nor a perfect residue field. It does not establish that
the canonical component injection is additive or surjective. Uniformizer
and model-change comparison of labels also remain open.

The later ordered work remains C1.5b/c (class lifting, cyclic order and
nonsplit comparison), C1.6/7 (additive branches and exhaustiveness), then
smooth special groups, S1/S2, C2/C3/Cp and A2 with the separate G1/G2 work.
No Mazur conclusion is claimed in this batch.
