# Mazur track D: extension and local arithmetic


## D-W29: concrete integral charts and subgroup coordinate maps

Eight new leaves implement the first geometric constructions from W28:

| Leaf | Module | Lines/cap | Output |
| --- | --- | --- | --- |
| Chart algebra | `WeierstrassIntegralChart` | 97/240 | Cubic quotient, universal coordinates, evaluation. |
| Integral cover | `EllipticIntegralChartCover` | 82/240 | Every primitive generic point has Y or Z a unit; integral normalization. |
| Point comparison | `EllipticIntegralChartEvaluation` | 91/240 | Generic and residue evaluations; equality with actual projective reduction. |
| Ambient overlap | `WeierstrassChartOverlap` | 118/240 | Explicit inverse algebra maps between the localized standard charts. |
| Subgroup closure | `EllipticSubgroupChartClosure` | 90/240 | Actual subgroup coordinate map, kernel quotient, torsion-freeness and DVR flatness. |
| Finite interpolation | `FinitePointAlgebraInterpolation` | 67/240 | A separating map to a finite function algebra is surjective. |
| Generic comparison | `EllipticSubgroupChartGeneric` | 74/240 | Closure generic-fiber equivalence and generic rank by chart point count. |
| Transported subgroup | `EllipticExtensionChartClosure` | 75/240 | Instantiate at `ellipticExtensionPointHom`; projective subgroup order p. |

Validation is recorded in the untracked `Scratch/MazurDW29/` receipts; run
`python3 Scratch/MazurDW29/check.py` to recheck caps, module build/lint logs,
axiom sets, root build and the merged-main relation. The final W29 handoff
records the timestamp and commits. These constructions do not complete S2b.

The next leaf is compatibility of the **closure ideals** under the already
constructed ambient overlap equivalences. This needs restriction to the
subgroup points lying in both generic charts, followed by localization of
both kernel quotients. Glue those closures and prove global finiteness.
The two standard affine chart closures must not simply be assumed finite:
a generic point can belong to a chart while its specialization leaves that
chart, so the normalized generic coordinate may have a denominator. W29's
flatness and generic comparison deliberately require no such integrality.

After gluing and finiteness, construct integral group operations on the good
model and the relevant smooth multiplicative model, prove preservation of
the subgroup closure, and finish the Hopf and special-fiber group comparisons.
The proved chart evaluation comparison supplies the pointwise reduction part,
but does not prove these group-scheme comparisons. Apply rigidity only after
those obligations. C2/C3/Cp, A2 and final axiom removal remain downstream.

## D-W28: integral closure construction (historical ordered split)

The four steps below are proof obligations, not hypotheses to add to a model
record. Each Lean leaf has cap 240 lines. Good and multiplicative reduction
must both be covered; the admitted general good-reduction flatness theorem
is excluded.

1. **Affine closure algebra.** For an integral chart algebra A and its map
   f into the generic finite etale subgroup algebra B, use A / ker(f),
   identify it with the image, and prove torsion-freeness and flatness over
   the DVR. Recover the generic algebra when the generic chart map is onto.
   This step does not require A itself to be finite or a Hopf algebra.
2. **Finiteness and rank.** Prove integrality of the chart generators using
   the actual torsion-point bounds, then finite generation plus integrality
   gives a finite module. Recover rank p from the generic comparison.
   Good reduction needs charts including the identity: affine x,y have
   poles there. Multiplicative reduction additionally needs the Tate/node
   chart and a proof that the chosen charts cover the subgroup closure.
3. **Hopf operations.** Prove that product closures embed into the generic
   product using flatness over the DVR. Restrict the integral ambient group
   law to the closure, then descend comultiplication, counit and antipode.
   Product flatness alone does not extend a rational group law across a
   node: the Weierstrass smooth locus or a suitable group model is needed.
4. **Specialization.** Prove the chart evaluation maps commute with residue
   reduction and agree with actual elliptic point reduction. Glue the chart
   comparisons, then apply finite-flat rigidity with the S2a ramification
   bound. Continue S2b, C2/C3/Cp, A2 and the final axiom removal in that order.

The original first leaf was the affine quotient/image construction. W29 above
now supplies normalized integral point charts and ambient overlap maps; closure
ideal gluing and global finiteness remain. F3 is not assumed to imply integrality
of every coordinate on the full standard generic chart.

### W28 algebraic progress and geometric boundary

`AffineGenericClosure` (103/240 lines) proves the quotient/image description,
torsion-freeness, Dedekind flatness and generic comparison without an ambient
finite-flat or Hopf hypothesis. `AffineClosureFiniteness` (61/240 lines) proves
finiteness from integral images of finitely many algebra generators, then
identifies the rank with the generic dimension over a PID. Both are in commit
`982e3da6`; these are algebraic lemmas, not an elliptic torsion model.

Checked 2026-10-05 12:18 UTC: individual builds and individual module linters
pass; all eleven new theorem/map declarations use only propext,
Classical.choice and Quot.sound. Re-run the two module builds, their individual
`lake exe runLinter MODULE` commands, and `lake env lean
Scratch/MazurDW28/Axioms.lean`; receipts are in `Scratch/MazurDW28/`.

The first unproved geometric obligation is to instantiate the coordinate map
for the actual subgroup and cover its integral closure with compatible affine
charts. Primitive integral projective representatives already exist in
`EllipticProjectiveReduction`; they do not give a single affine coordinate
algebra for the whole subgroup, which includes the point at infinity.

The strongest F3 kernel theorem in `EllipticUnramifiedTorsion` assumes that the
maximal ideal is generated by the annihilator. `EllipticLocalValuation` only
excludes nonzero torsion with parameter deeper than that annihilator. Neither
statement supplies the requested ramified chart construction from S2a.

There is also a separate multiplicative-reduction obligation. The full nodal
Weierstrass cubic is not a group scheme; the actual reduction homomorphism in
`EllipticReductionKernel` has domain E0, the smooth-reduction subgroup.
Consequently product flatness cannot by itself induce Hopf operations on an
arbitrary closure in the nodal cubic. Prove that this particular subgroup
stays in the smooth group model, or construct a suitable group model and
compare its point reduction. This is not a field to assume in a new record.
The good-reduction branch likewise still needs the concrete chart gluing,
integral group operations and point-reduction comparison.

S2b and the downstream C2/C3/Cp, A2 and axiom-removal tasks remain open.

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
`Scratch/MazurDW13/*-build.log` and `*-lint.log`.

Checked 2026-10-05 03:58 UTC: all 37 new theorems and the descended label
function use only propext, Classical.choice and Quot.sound. Re-run
`LEAN_NUM_THREADS=2 lake env lean Scratch/MazurDW13/Axioms.lean`; evidence:
`Scratch/MazurDW13/axioms.log` (38 declarations).
`python3 Scratch/MazurDW13/check.py` checks the module caps, build/lint logs,
axiom sets and sorted unique root imports.

Checked 2026-10-05 04:06 UTC: merged origin/main `df13140e` as `ec2f08cd`.
The required foreground `LEAN_NUM_THREADS=2 lake build FLT` passed all 12,842
jobs, including FLT and FermatsLastTheorem, with no declaration clashes.
Evidence: `Scratch/MazurDW13/root-build.log`; the checker also verifies this
result and `git merge-base --is-ancestor origin/main HEAD`.
The global axiom audit still lists `Mazur_statement` and `sorryAx` alongside
the standard three. Re-run `LEAN_NUM_THREADS=2 lake env lean
Scratch/MazurDW13/GlobalAxioms.lean`; evidence: `global-axioms.log`, checked
2026-10-05 04:06 UTC. The campaign goal is not complete.

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

### D-W11 historical validation

Validation commands and evidence are under `Scratch/MazurDW11/`: one
foreground `LEAN_NUM_THREADS=2 lake build FLT.Mazur.MODULE` and one
`LEAN_NUM_THREADS=2 lake exe runLinter FLT.Mazur.MODULE` for each entry in
`modules.txt`; `lake env lean Scratch/MazurDW11/Axioms.lean` audits all 26 new
theorems. The untracked `MAZUR_D_W11_DONE.md` records checked-at results and
commit IDs after validation and the required post-merge root build.
Checked 2026-10-05 02:43 UTC: all nine individual builds and linters passed
without warnings; all 26 theorem audits contain only propext, Classical.choice
and Quot.sound. Each module has 45–115 physical lines (cap 240).
Proof commit: `c88c88cb`. Fetched main at `a57f98ff`, merged in `f25d8e1c`.
Checked 2026-10-05 02:49 UTC: the foreground post-merge `lake build FLT`
passed all 12,743 jobs including FLT and FermatsLastTheorem, with no declaration
clashes. Evidence: `Scratch/MazurDW11/root-build.log`;
`python3 Scratch/MazurDW11/check.py` checks the recorded logs and module caps.

### D-W10 implementation boundary and evidence

The initial rational singular-point, cusp and split-node normalizations are
proved by C1.4a.iii.1–8. The proofs include residue characteristics 2 and 3.
C1.4b.i–iv transport the actual E₀ subgroup and E/E₀ quotient through an
integral variable change with unit u. Generic ellipticity is required for the
point-group isomorphism; the special cubic is allowed to be singular.

At the D-W10 boundary the first open leaf was C1.5a: construct the split multiplicative component
class map from the actual equation, then prove its kernel is E₀. The initial
normal form does not provide the deeper coefficient/valuation tests, class
surjectivity, the nonsplit comparison, or the additive branch bounds. Those
remain in C1.5–C1.7. No S1/S2, C2/C3/Cp or A2 conclusion follows yet.

Validation for this batch is recorded by the per-module foreground build and
lint logs under `Scratch/MazurDW10/`. Re-run each name in `modules.txt` with
`LEAN_NUM_THREADS=2 lake build FLT.Mazur.MODULE` and
`LEAN_NUM_THREADS=2 lake exe runLinter FLT.Mazur.MODULE`, one at a time.
`LEAN_NUM_THREADS=2 lake env lean Scratch/MazurDW10/Axioms.lean` audits every
new theorem and definition; `root-build.log` records the post-merge root build.
Checked 2026-10-05 02:19 UTC: all 12 module builds and individual linters
passed; all 39 theorems and 3 definitions use only propext, Classical.choice
and Quot.sound. Proof commits are `71ce44b7` and `f7060194`. Fetched main at
`4d046136`, merged in `f8f3ac20`; the foreground root build passed 12,702 jobs,
including FLT and FermatsLastTheorem, with no declaration clashes. Evidence:
`Scratch/MazurDW10/axioms.log`, per-module logs and `root-build.log`.

D-W9 (`ece0202d`) supplied C1.1–C1.3 and C1.4a.i–ii, including the normalized
type II quotient calculation. The older general Néron-model blocker below is
superseded for the local point-group route. It is not needed by this route.

## D-W4: formal addition construction leaves

Subdivision recorded before implementation; each new module has cap 240 lines.

| Item | Planned module | Output |
| --- | --- | --- |
| A1-F2b.i | EllipticFormalCoordinates | Substitution of the integral infinity series into multivariate parameters, with the chart equation and uniqueness. |
| A1-F2b.ii | EllipticFormalSecant | Integral secant slope and intercept, both line incidences, and zero constant coefficients. |
| A1-F2b.iii.1 | EllipticFormalCubic | Cubic coefficients and a third-root identity valid without cancellation. |
| A1-F2b.iii.2 | EllipticFormalIntersection | Integral third-intersection coordinates and their chart equation. |
| A1-F2b.iv.1 | EllipticFormalNegation | Integral normalized negation, its chart equation and involution. |
| A1-F2b.iv.2 | EllipticFormalSymmetry | Symmetry of the slope, intercept and third intersection. |
| A1-F2b.iv.3 | EllipticFormalAddition | Negation of the third intersection, identity and symmetry. |
| A1-F2b.iv.4 | EllipticFormalSubstitution | Substitution compatibility and representation by the two-variable series. |
| A1-F2b.iv.5 | EllipticFormalLinearTerms | Axis identities, symmetry and the two linear coefficients of the series. |
| A1-F2b.v | EllipticFormalGroupLaw | Associativity and the actual FormalGroup construction, with linear coefficients. |

F2c/F2d/F3 and later arithmetic leaves retain their previous order. The first
four construction leaves alone do not establish a formal group or its comparison
with actual point addition.

Audit checked 2026-10-04 against FLT `55366a69` and pinned Mathlib
`c32e1ec0d1eb5237ba344eee50162f45d5b0fc76`. This is the implementation order
for GOAL-MAZUR-D-W1. Every new module has a hard cap of 240 physical lines.
W74 in wt-r5a owns ampleness/moduli; no leaf below duplicates that work.

## Existing APIs and limits

- Mathlib `AlgebraicGeometry/ValuativeCriterion.lean` proves properness implies
  existence and separatedness implies uniqueness for valuation-ring squares.
  A DVR is a valuation ring, so G1-D1 needs an over-category adapter, not a
  new valuative criterion.
- `AlgebraicGeometry/Birational/RationalMap.lean` supplies
  `PartialMap.ofFromSpecStalk`, its restriction identity, and spreading out.
  `Morphisms/Separated.lean`, `ext_of_isDominant_of_isSeparated`, supplies
  uniqueness on a reduced base. `Scheme.OpenCover.glueMorphisms` is the
  actual gluing API. Local lifts must first be spread to open neighborhoods;
  spectra of local rings are not an open cover.
- `FLT/Mazur/OverPoints.lean` and `Contracts.lean` supply actual morphisms over
  the base. `IntegralBase.lean` supplies canonical maps of Z[1/(2p)]. The
  supplied `IntegralData.generic` must be identified with the canonical map.
- Mathlib elliptic `Reduction.lean` defines minimal, good, multiplicative and
  additive reduction. It does not construct Néron models or their components.
- `FLT/FreyCurve/Serre/GoodReduction.lean` proves prime-to-residue-characteristic
  torsion injectivity. `GoodReductionSpecialization.lean` constructs a
  surjective geometric specialization. Neither proves G2-D5: rational torsion
  of residue-characteristic order at odd unramified primes must be included.
- `FLT/GroupScheme/Raynaud*Rigidity.lean` provides finite-flat algebra tools;
  applicability to torsion in a constructed abelian scheme still needs proof.
  No general Néron special-fiber/component or elliptic formal-group endpoint
  was found by `rg` in FLT and Mathlib. Frey-specific semistability is not A1.

## Ordered leaves

Names in this table are planned modules under `FLT/Mazur/`; a name is not a
claim that its prerequisites or proof already exist. Split again before a
proof exceeds its cap. Sources: MAZUR_CONTRACTS G1-D/G2-D and
MAZUR_GOAL_LEDGER source table; [M] is Mazur (1977).

| Item | Proposed module | Cap | Exact output / prerequisites |
| --- | --- | ---: | --- |
| G1-D1 | ProperPointExtension | 160 | Unique extension of an actual K-point over any valuation ring R with fraction field K; hence every DVR. Proper structure map only. |
| G1-D2a | GenericSectionUniqueness | 160 | Restriction injectivity from a reduced base along a dominant map to a separated target; apply to canonical generic points. |
| G1-D2b | ProperStalkExtension | 240 | Spread the valuative lift at a point of an integral base with valuation stalk to an open neighborhood; preserve the generic point and base equation. |
| G1-D2c | ProperSectionGluing | 240 | Glue those neighborhoods by generic uniqueness; unique global section. |
| G1-D2d.i | DedekindPointExtension | 160 | Prove valuation stalks for Dedekind spectra; transport the extension to any specified fraction field. |
| G1-D2d.ii | IntegralPointExtension | 160 | Prove valuation-stalk/fraction-field hypotheses for Z[1/(2p)], identify the canonical generic map, conclude G1Extension. |
| A1-F1 | EllipticReductionKernel | 240 | Construct local minimal-model reduction and its kernel from actual rational points; requires the local model and group-law comparison. |
| A1-F2 | EllipticFormalParameter | 240 | Construct the formal parameter and multiplication series for that kernel, with integral coefficients. Depends F1. |
| A1-F3 | EllipticFormalTorsionBound | 240 | Prove valuation bounds for multiplication, including the small-prime exceptions. Depends F2; [M] III §5 Step 1. |
| A1-C1 | EllipticNeronComponents | 240 | Identify reduction modulo the identity component and prove the additive component order bounds. Requires a constructed Néron model and local fiber classification. |
| A1-S1 | PrimeTorsionSemistabilityAway | 240 | Exclude additive reduction away from the torsion prime for a rational point of prime order ≥17 using F3/C1. |
| A1-S2 | PrimeTorsionSemistabilityAtPrime | 240 | Exclude additive reduction at the torsion prime via finite-flat rigidity; requires the actual torsion closure and its rank/flatness. |
| A1-C2 | PrimeTorsionComponentsAtTwo | 200 | Small-prime component assertion at 2; retain split/nonsplit and formal-kernel hypotheses from [M] III §5 Steps 1–2. |
| A1-C3 | PrimeTorsionComponentsAtThree | 200 | Corresponding component assertion at 3; depends F3/C1/S1. |
| A1-Cp | PrimeTorsionComponentsAtPrime | 240 | Component assertion at p; depends S2 and finite-flat local model. |
| G2-D5a | AbelianTorsionClosure | 240 | Construct finite-flat closure of rational torsion in the good abelian model, with generic point and specialization comparison. |
| G2-D5b | OddPrimeTorsionRigidity | 240 | Prove trivial specialization kernel, including q-primary torsion, over the unramified odd local base. Depends D5a and proven rigidity, not a kernel assumption. |
| G2-D5c | OddPrimeTorsionSpecialization | 160 | Injectivity on actual rational torsion from D5a/b. [M] III §5 p.160 footnote. |
| G2-D6 | FiniteSectionSpecialization | 180 | Combine finite rational points, generic restriction injectivity and D5c to get G2Specialization. |

The arithmetic rows are source-level subdivisions with named foundation
prerequisites, not assertions that Néron theory fits in one 240-line module.
Implementation proceeds in order; a missing foundation is reported with the
exact missing theorem, never installed as a conclusion-bearing record field.
G1-D3–D6 (Néron reduction and cusp orientation) remain separate prerequisites
of the final cusp argument. Nothing here alone removes `Mazur_statement`.

## Validation

Each implemented module: foreground `LEAN_NUM_THREADS=2 lake build MODULE`,
then `lake exe runLinter MODULE` alone, then `#print axioms` for every new
theorem (allowed: propext, Classical.choice, Quot.sound only). Before handoff:
merge origin/main, build `FLT` once, check caps and declaration clashes.

## Implementation boundary (2026-10-04)

G1-D1 and G1-D2 are implemented by the six modules above.
`g1Extension_of_isProper` proves the actual contract for `p ≠ 0` and proper
`D.X.hom`. No canonical-map hypothesis is assumed: `IntegralBase.generic_unique`
proves every map from Spec Q to this base equals the canonical map. The modular
curve itself and its properness remain G1-C work.

The next leaf A1-F1 is not supplied by existing reduction APIs:
`WeierstrassCurve.reducePoint` in `EllipticCurve/PointReduction.lean:30` requires
`(W.map (residue A)).IsElliptic`; `reducePointHom` additionally uses an
algebraically closed generic field. Additive and multiplicative special fibers
are singular, and arbitrary rational points can meet singular points on a
minimal Weierstrass model. A1 needs the actual nonsingular-reduction subgroup
E₀(K), its reduction homomorphism and formal kernel E₁(K), then their comparison
with the Néron model. Sending all singular reductions to zero is not that map.
`Reduction.exists_isMinimal` constructs a minimal equation but does not prove
these subgroup, component, or formal multiplication assertions.

A concrete prerequisite subdivision for A1-F1 is: (i) define E₀(K) through
projective reduction and prove closure under addition/negation (cap 240),
(ii) construct its homomorphism to the smooth special cubic and characterize
E₁(K) by the formal parameter (cap 240), (iii) construct/compare the Néron
identity fiber and its component quotient (each further leaf cap 240). None
is marked implemented. Formal multiplication coefficients and local valuation
bounds must then be proved before any semistability/component corollary.

For G2-D5, `ThreeAdicPlan.ModelHom.surjective_of_padic_power` is an existing
odd-prime rigidity theorem for supplied finite-flat Hopf models. Its inputs
are actual `FF` models and a generically bijective `ModelHom`; it does not
construct the torsion closure in the abelian scheme or identify specialization.
The missing comparison cannot be replaced by assuming an injective reduction
map. A1, G2-D5 and `Mazur_statement` therefore remain open.

## Checked validation (2026-10-04 22:41 UTC)

Six module builds and six individual module linters passed. All 15 new theorems
and G1Extension were checked with `#print axioms`: only propext, Classical.choice
and Quot.sound. Each new module is 51–92 lines. After merging origin/main
`0d2a816c` in `a3ef538d`, `LEAN_NUM_THREADS=2 lake build FLT` passed all 12,505
jobs, including the root and FermatsLastTheorem. Root imports are sorted and
`git diff --check` passed. The guarded final theorem audit still includes
Mazur_statement and sorryAx; the arithmetic leaves above are not closed.

## D-W2: projective reduction foundation leaves

A1-F1 is larger than one 240-line module. Work first constructs actual projective
reduction, including singular reductions; it does not replace singular points by
infinity. The following leaves precede the subgroup and homomorphism assertions.

| Item | Module under `FLT/Mazur/` | Cap | Output |
| --- | --- | ---: | --- |
| A1-F1a.i | ValuationProjectiveNormalization | 240 | Every nonzero finite coordinate vector has an integral representative with a unit coordinate; primitive representatives equivalent over the fraction field differ by an integral unit. |
| A1-F1a.ii | EllipticProjectiveReduction | 240 | Choice-independent projective reduction on actual generic-fiber points, satisfying the reduced equation even at bad reduction. |
| A1-F1a.iii | EllipticSmoothReduction | 240 | Nonsingular-reduction locus, infinity fiber, and compatibility with negation; no claim of additive closure until proved. |
| A1-F1a.iv | EllipticReductionInfinityChart | 240 | Identify the infinity fiber by vanishing of the reduced Z coordinate; establish its integral formal-parameter chart. |
| A1-F1b.i | EllipticSmoothReductionAddition | 240 | Prove nonsingular-reduction locus closed under addition using integral group-law charts, including opposite reductions. |
| A1-F1b.ii | EllipticReductionKernel | 240 | Package the proved locus as E₀, its reduction homomorphism, and E₁ as the kernel; compare with formal coordinates. |

Formal multiplication, Néron components and the subsequent arithmetic leaves stay
in the order above. A set closed under negation alone does not close A1-F1.

### D-W2 implementation boundary

The four A1-F1a leaves above are implemented. `projectiveReduction` accepts actual
generic-fiber projective points of any integral Weierstrass equation over a
valuation subring, with no good-reduction or algebraic-closure assumption. Its
primitive reduced coordinates are nonzero and satisfy the special cubic. Singular
reductions remain singular projective classes. `SmoothReduction` and
`InfinityReduction` are predicates on these actual points, stable under negation;
`smoothReductionPoint` maps the former locus to actual smooth special-fiber points.
They have **not** been promoted to subgroups.

`infinityReduction_affine_iff` identifies the infinity fiber with the failure of
joint integrality of the affine coordinates. `exists_infinity_parameters` constructs
the actual integral coordinates t = -X/Y and s = -Z/Y in the maximal ideal and
proves s = t³ + a₁ts + a₂t²s + a₃s² + a₄ts² + a₆s³. It does not construct a power
series expressing s in terms of t or a formal multiplication law.

The first remaining statements are:

- `SmoothReduction A W P → SmoothReduction A W Q → SmoothReduction A W (P + Q)`.
- The reduction of that sum equals the sum of `smoothReductionPoint` values.

The generic projective addition formulas do not directly prove these statements:
Mathlib `Projective/Formula.lean`, `addXYZ_self`, gives the zero vector on coincident
inputs. Distinct generic points can have coincident reductions, so reducing their
secant formula can give zero rather than a primitive vector. `Projective.map_add`
only transports through field homomorphisms and does not apply to the residue map.
Integral group-law charts or explicit exceptional-denominator arguments still
need construction. Existing `PointReductionAddition`/`PointReductionKernel` APIs
package addition using an elliptic special fiber, so they cannot directly supply
these bad-reduction statements.

After those statements: package E₀ and the reduction homomorphism, define E₁ as
its kernel, then implement A1-F2/F3. A1-C1 (Néron model/components and bounds),
A1-S1/S2, A1-C2/C3/Cp, and G2-D5/D6 remain unimplemented here. No later arithmetic
leaf is closed by the projective-coordinate foundation.

Validation of these leaves: four foreground module builds and four individual
module linters pass; all 28 new theorems have only propext, Classical.choice and
Quot.sound in their axiom sets. Modules have 108, 135, 134 and 135 physical lines,
respectively, against the 240-line caps. Re-run the axiom checks with
`lake env lean Scratch/MazurDW2/Axioms.lean` (untracked validation artifact).

### D-W2 root verification (2026-10-04 22:59 UTC)

After commit `ba010248`, fetched origin/main (`baff6e10`) and ran
`git merge origin/main`: already up to date. The required foreground
`LEAN_NUM_THREADS=2 lake build FLT` passed all 12,519 jobs, including FLT and
FermatsLastTheorem, with no declaration clashes. Evidence:
`Scratch/MazurDW2/root-build.log`. The guarded global axiom audit still contains
Mazur_statement and sorryAx; these foundation leaves do not remove either.

## D-W3: additive closure subdivision

Before implementation, split A1-F1b.i into the following leaves (each cap 240
physical lines). These proofs retain bad reduction and arbitrary valuation
subrings; smoothness of individual reduced points is not good reduction.

| Item | Module under `FLT/Mazur/` | Cap | Output |
| --- | --- | ---: | --- |
| A1-F1b.i.1 | EllipticReductionRelation | 240 | Relate actual affine points via projective reduction; zero, integral, negation and uniqueness APIs. |
| A1-F1b.i.2 | EllipticReductionTranslation | 240 | Adding a nonintegral point to any integral affine point gives integral coordinates with the same residues; no elliptic special-fiber assumption. |
| A1-F1b.i.3 | EllipticReductionAffineAddition | 240 | Compatible addition when integral smooth reductions are not opposite, using the two slope charts. |
| A1-F1b.i.4 | EllipticReductionOpposite | 240 | Opposite smooth affine reductions sum to infinity; use integrality of the slope when the sum is integral to exclude that case. |
| A1-F1b.i.5 | EllipticSmoothReductionAddition | 240 | Full compatibility and smooth-locus closure, including the sum of two infinity-fiber points. |
| A1-F1b.ii | EllipticReductionKernel | 240 | E₀ subgroup, actual reduction homomorphism and E₁ kernel. |

The two-infinity case can be reduced to translation: if their sum were integral,
translation by its negative would contradict the known infinity reduction of the
other point. Later arithmetic leaves still follow the original order.

### D-W3 formal-series subdivision

A1-F2 also requires multiple capped leaves. After constructing E₀/E₁:

| Item | Module under `FLT/Mazur/` | Cap | Output |
| --- | --- | ---: | --- |
| A1-F2a | EllipticInfinityPowerSeries | 240 | Construct the integral solution s(T) of the infinity-chart equation, with s(T) = T³ times a unit of constant term one. |
| A1-F2b | EllipticFormalGroupLaw | 240 | Construct the two-variable integral addition law and prove its identities from the actual Weierstrass law; split again before exceeding the cap. |
| A1-F2c | EllipticFormalMultiplication | 240 | Multiplication series [n](T) with its linear coefficient and higher-order divisibility properties. |
| A1-F2d | EllipticFormalEvaluation | 240 | Identify convergent evaluation on the complete local base with actual E₁ addition and multiplication. |

F2a alone is not a multiplication law or the evaluation comparison. F3 requires
F2c/d, including the residue-characteristic-primary multiplication estimates.

F2a is further split before implementing the actual-parameter comparison:
`EllipticInfinityPowerSeries` (F2a.i, cap 240) constructs the universal integral
series; `EllipticInfinityParameter` (F2a.ii, cap 240) proves uniqueness of the
maximal-ideal chart and constructs an injective parameter on actual E₁ points.
Neither leaf substitutes for F2b's addition law or F2d's convergence proof.

### D-W3 implementation boundary (2026-10-04)

A1-F1b.i.1–5 and A1-F1b.ii are implemented. `SmoothReduction.add` proves closure
on actual projective points; `smoothReductionPoint_add` proves additivity.
`ellipticE0` and `ellipticE1` are actual subgroups, and `smoothReductionHom_ker`
identifies the reduction kernel with E₁ pulled back to E₀. The special cubic is
allowed to be singular, the valuation subring is arbitrary, and no algebraic
closure, lifting-surjectivity or closure assumption is added.

The exceptional cases are proved: `slope_mem_of_addX_mem` forces integral slope
from integral sum; `not_opposite_of_integral_slope` contradicts smoothness for
opposite reductions, including reduced order-two points. Translation by a point
reducing to infinity preserves arbitrary integral affine coordinates modulo the
maximal ideal. If a sum of two infinity-fiber points were integral, translation
by its negative would give the contradiction used in `reducesTo_add_zero`.

F2a.i and F2a.ii are implemented. `infinitySeries` is constructed over **any**
commutative coefficient ring, not postulated: a monic reciprocal cubic is Hensel
lifted in the T-adically complete power-series ring. The series satisfies the
infinity equation, has zero constant coefficient and cubic coefficient one,
is the unique zero-constant solution, and commutes with coefficient-ring maps.
`infinityParameter` is an injective function from actual E₁ points to the
valuation subring, with image in the maximal ideal, and vanishes exactly at zero.
`infinityChart_eq_cube_mul_unit` proves the actual relation s = t³ times a unit
of residue one. These are coordinate statements, not formal multiplication.

The next unimplemented statement is F2b: construct an integral two-variable
power series F_W(X,Y) for this Weierstrass curve and prove its formal-group
identities. In the t,s chart, a candidate uses the divided difference
λ = (s(X)-s(Y))/(X-Y), ν = s(X)-λX, and the third intersection of the line
s = λt+ν with the cubic, followed by Weierstrass negation. The divided difference,
unit denominators, group identities and comparison with actual addition still
need proofs; one-variable uniqueness by itself does not supply them. Subdivide
F2b further before a proof exceeds 240 lines.

After F2b: multiplication series F2c, convergent comparison F2d, valuation bounds
F3, the actual Néron model/component classification C1, semistability S1/S2,
components C2/C3/Cp, and abelian torsion closure/odd-prime specialization D5/D6.
No claim is made to finish those leaves or to remove `Mazur_statement`.

### D-W3 validation (2026-10-04 23:28 UTC)

All eight modules built in the foreground and passed separate one-module linters.
All 47 new theorems have only propext, Classical.choice and Quot.sound in their
axiom sets. Modules have 87–151 physical lines against caps of 240. The
implementation commits are `7be7c9f2` and `c0b96992`; no push was made.

Fetched origin/main at `988a75e5` and merged it in `280af779`. The required
foreground `LEAN_NUM_THREADS=2 lake build FLT` passed all 12,545 jobs, including
FLT and FermatsLastTheorem, with no declaration clashes. Root imports are sorted
and unique; `git diff --check` passes. Recheck evidence in
`Scratch/MazurDW3/root-build.log`, `*lint.log`, and `axioms.log`; re-run the 47
axiom checks with `lake env lean Scratch/MazurDW3/Axioms.lean`. The guarded global
theorem check still includes Mazur_statement and sorryAx. F2b onward remains open.

### D-W4 construction boundary and validation (2026-10-04 23:54 UTC)

The nine construction leaves A1-F2b.i through A1-F2b.iv.5 are implemented in
`f0aea5d4` and `ac1e7330`. They construct an integral two-variable addition
candidate over every commutative ring. Its constant coefficient is zero, both
linear coefficients are one, its axis restrictions are the identity, and it is
symmetric. The secant and third-intersection equations hold even on the diagonal;
only denominators with constant coefficient one are inverted. Formal negation
is an involution. The entire construction commutes with zero-constant formal
substitution.

A1-F2b.v remains open: the series has not been proved associative or packaged
as a `FormalGroup`. There is no comparison with actual E₁ addition or convergent
evaluation. F2c/F2d/F3 and every later arithmetic leaf remain open.

Read-only checks: all nine foreground module builds and nine separate module
linters passed (`Scratch/MazurDW4/*-lint.log`). All 59 new theorem axiom sets
contain only propext, Classical.choice and Quot.sound (`lake env lean
Scratch/MazurDW4/Axioms.lean`, captured in `axioms.log`). The modules have
65–127 physical lines against their 240-line caps. Root imports are sorted and
unique; `git diff --check` passes. No existing Lean module was edited except
the root imports.

Fetched origin/main at `3509f324` over authenticated HTTPS (SSH authentication
failed); `git merge origin/main` reported already up to date. The required
foreground `LEAN_NUM_THREADS=2 lake build FLT` passed all 12,563 jobs, including
FLT and FermatsLastTheorem, with no declaration clashes (`root-build.log`).
The final theorem audit still lists Mazur_statement and sorryAx, checked by
`lake env lean Scratch/MazurDW4/GlobalAxioms.lean` (`global-axioms.log`).


### D-W5 associativity and evaluation subdivision

Each new module retains the 240-line cap. These leaves extend A1-F2b.v,
then begin multiplication and convergent evaluation in the original order.

| Item | Module | Output |
| --- | --- | --- |
| A1-F2b.v.1 | EllipticFormalBaseChange | Naturality of all formal operations under coefficient-ring homomorphisms. |
| A1-F2b.v.2 | EllipticFormalProjective | Unit Z-partial derivative, actual projective chart points, and parameter injectivity. |
| A1-F2b.v.3 | EllipticFormalSecantComparison | Polynomial comparison with Mathlib's projective secant formula. |
| A1-F2b.v.4 | EllipticFormalAdditionComparison | Explicit scale relating projective addition to the normalized formal sum. |
| A1-F2b.v.5 | EllipticFormalFieldPoint | Injective field-valued points and addition comparison at distinct formal parameters. |
| A1-F2b.v.6 | EllipticFormalGenericParameters | Nondegeneracy of the four secants needed for generic associativity. |
| A1-F2b.v.7 | EllipticFormalAssociativity | Associativity over domains via their series fraction fields. |
| A1-F2b.v.8 | EllipticFormalGroupLaw | Universal coefficient specialization, associativity over every commutative ring, and a commutative FormalGroup. |
| A1-F2b.vi / F2c.i | EllipticFormalFirstOrder | Cubic coordinate divisibility and linear terms of all operations. |
| A1-F2b.vii | EllipticFormalInverse | Actual negation comparison and both formal inverse identities. |
| A1-F2c.ii | EllipticFormalMultiplication | Natural multiplication, scalar addition/composition, substitution/base change, and linear coefficient n with quadratic remainder. |
| A1-F2d.i | EllipticInfinityEvaluation | Convergent coordinate evaluation on complete valuation rings and reconstruction of actual E₁ representatives. |

The generic associativity proof uses four secants with distinct endpoints in
three independent variables. No tangent comparison is assumed: the resulting
three-variable identity specializes to arbitrary zero-constant parameters.
The inverse identity is first proved over the universal characteristic-zero
domain, then specialized and substituted; it holds also in characteristic two.

F2d.i reconstructs coordinates, not an additive equivalence with E₁. Still needed:
multivariate evaluation of the addition series, its comparison with actual
point addition (including coincident evaluated parameters), and the resulting
multiplication compatibility. F2c supplies natural scalars and the quadratic
remainder; stronger residue-characteristic coefficient divisibility, valuation
bounds F3, and the Néron/component and semistability leaves remain open.

### Checked validation (2026-10-05 00:29 UTC)

- All twelve new modules built in foreground `LEAN_NUM_THREADS=2 lake build MODULE`
  runs and passed individual `lake exe runLinter MODULE` runs. Logs:
  `Scratch/MazurDW5/*-build.log` and `*-lint.log`.
- All 61 new theorem declarations, plus `formalGroup` and its commutativity
  instance, were axiom-audited: only propext, Classical.choice and Quot.sound.
  Re-run `LEAN_NUM_THREADS=2 lake env lean Scratch/MazurDW5/Axioms.lean`;
  evidence: `Scratch/MazurDW5/axioms.log` (63 checks).
- Modules are 43–120 lines, each below 240. No sorry/axiom/admit declarations.
  `git diff --check` passes; FLT.lean imports are sorted and unique. All task
  Lean changes are new modules plus root imports; the upstream merge also
  brings its own unrelated modules.
- Merged origin/main at `5d03b585` in `c62e5dd4`. The required foreground
  `LEAN_NUM_THREADS=2 lake build FLT` passed all 12,612 jobs, including FLT
  and FermatsLastTheorem, with no declaration clashes. Evidence:
  `Scratch/MazurDW5/root-build.log`.
- Global audit still lists Mazur_statement and sorryAx alongside the standard
  three axioms. Re-run `lake env lean Scratch/MazurDW5/GlobalAxioms.lean`;
  evidence: `Scratch/MazurDW5/global-axioms.log`.
- No push, whole-library lint, fleet request, or G1/G2 work was performed.


## W14: full label additivity and cyclic component quotient

C1.5a.x.10.m is discharged. `nodePointLabel_add` proves addition on the
actual generic elliptic-curve group. `nodePointLabelHom` has kernel E₀;
`nodeComponentLabelHom` packages the already canonical quotient label as an
injective additive map into Z/nZ. The actual component quotient is therefore
cyclic, of order dividing n, and n times any generic point lies in E₀.

The proof first computes exact primitive coordinates for unequal opposite
branches, including a deeper midpoint. For same-branch wraparound, the
pairwise-product coefficient forces the line intercept to have at least
the sum of the two smallest depths. The first-branch tangent test gives one
extra power beyond the largest depth. Its square is therefore deeper than
the product of all three x-coordinates. Comparing the product coefficient
with the exact depth of a₆ gives k+j+r=n. The actual third intersection is
proved to be the negative sum; tangent/doubling charts are included.

`NodePointCoordinates.add_first_depth_le_middle` and
`NodePointCoordinates.add_first_depth_gt_middle` recover the exact common
depth and branch from the addition law: k+j up to the midpoint, n-(k+j)
on the opposite branch after it. `nodeComponentLabelEquivOfOne` reduces
exact order n and lifting all labels to constructing one actual point of
label one. This is an explicit hypothesis, not yet discharged by completeness.

The next open item is C1.5b's lifted generator over the complete DVR, followed
by nonsplit descent and the additive component bounds. These results do not
remove `Mazur_statement` from the global FLT theorem. All eighteen modules
below contain at most 106 lines (cap 240). The W14 proof commits add only
these modules and sorted FLT.lean imports.

| Item | Module under FLT/Mazur | Lines/cap | Commit |
| --- | --- | ---: | --- |
| cleared product identity | EllipticNodeAdditionProduct.lean | 70/240 | e561b076 |
| primitive difference factors | EllipticNodeDifferenceFactors.lean | 84/240 | e561b076 |
| actual addition witnesses | EllipticNodeAdditionCoordinates.lean | 58/240 | e561b076 |
| exact difference coordinates | EllipticNodeDifferenceCoordinates.lean | 82/240 | e561b076 |
| difference label law | EllipticNodeDifferenceLabels.lean | 68/240 | 1751ebb7 |
| all opposite/midpoint sums | EllipticNodeMixedLabels.lean | 98/240 | 1751ebb7 |
| line coefficient identities | EllipticNodeLineProducts.lean | 50/240 | d71f2ebf |
| exact triple depth | EllipticNodeTripleDepth.lean | 106/240 | d71f2ebf |
| ordered first-branch slope | EllipticNodeFirstBranchSlope.lean | 90/240 | d71f2ebf |
| actual third intersection | EllipticNodeThirdIntersection.lean | 67/240 | d71f2ebf |
| wraparound depth sum | EllipticNodeFirstTriple.lean | 80/240 | d71f2ebf |
| first-branch label law | EllipticNodeSameBranchLabels.lean | 97/240 | d71f2ebf |
| full label additivity | EllipticNodeLabelAdditivity.lean | 84/240 | d71f2ebf |
| additive maps and kernel | EllipticNodeLabelHom.lean | 82/240 | 5f15f50d |
| cyclicity/order divisibility | EllipticNodeComponentCyclic.lean | 50/240 | 5f15f50d |
| label decoding | EllipticNodeLabelDecode.lean | 54/240 | 5f15f50d |
| exact same-branch sum depths | EllipticNodeSumDepth.lean | 60/240 | 5f15f50d |
| lifted-generator criterion | EllipticNodeComponentGenerator.lean | 60/240 | 5f15f50d |

### Checked validation (2026-10-05 04:50 UTC)

- All eighteen foreground `LEAN_NUM_THREADS=2 lake build MODULE` runs and
  individual `lake exe runLinter MODULE` runs passed without warnings.
  Evidence: `Scratch/MazurDW14/MODULE-build.log` and `MODULE-lint.log`.
  No whole-library lint was run.
- All 44 theorems and three new map/equivalence definitions depend only on
  propext, Classical.choice and Quot.sound. The audit was rerun after the
  merge: `LEAN_NUM_THREADS=2 lake env lean Scratch/MazurDW14/Axioms.lean`;
  evidence: `Scratch/MazurDW14/axioms.log` (47 declarations).
- `python3 Scratch/MazurDW14/check.py` passes: module caps (50–106 lines),
  no admitted declarations, build/lint evidence, standard-only axiom sets,
  sorted unique imports, `git diff --check`, and merged origin/main ancestry.
- Fetched origin/main `6cac0cea` and merged as `561f6a2b`. The only conflict
  was FLT.lean imports; both sets were retained in sorted unique order.
  Required foreground `LEAN_NUM_THREADS=2 lake build FLT` passed all 12,986
  jobs, including FLT and FermatsLastTheorem, with no declaration clashes.
  Evidence: `Scratch/MazurDW14/root-build.log`.
- The global theorem still uses Mazur_statement and sorryAx alongside the
  standard three. Re-run `LEAN_NUM_THREADS=2 lake env lean
  Scratch/MazurDW14/GlobalAxioms.lean`; evidence: `global-axioms.log`.
- Inspected the live G1 wt-r5a and G2 wt-r1e briefs. No scope overlap,
  peer restart, fleet request, harness change, push, or whole-library lint.
  Handoff at the requested context boundary; no missing-foundation blocker.
