# FC0: source contracts for the curve foundations

Scope: G1-A1–A6 and G2-D1–D4 of [MAZUR_CONTRACTS.md](MAZUR_CONTRACTS.md).
Baseline: FLT `47069a2512946e49a1039596d2182d58a3cee831`, Mathlib
`c32e1ec0d1eb5237ba344eee50162f45d5b0fc76`. Source and API review: 2026-09-28.
The deliverable is a source ledger and typed propositions, not proofs of those propositions.

**Initial dispatch at the baseline above: FC01–FC03.** Finite-flat degree is substantially present in Mathlib.
Cartier divisors can use its existing ideal-sheaf/subscheme implementation.
Genus, cohomological base change and line-bundle ampleness still have representation gates.
The smooth-dimension and smooth-section contracts are now proved; see the implementation
notes below. The dispatch table records the original subdivision, not current completion.
The complete F-Curve family is not yet an implementation queue.

## FC13–FC14 proofs

[ClosedSubsets.lean](../FLT/Mazur/ClosedSubsets.lean) proves
`properClosedSubsetFinite`, including the empty subset.
[CurveFinite.lean](../FLT/Mazur/CurveFinite.lean) proves
`nonconstantProperCurveFinite` for arbitrary separated targets over a field.
The argument handles nonclosed target points as well as closed fibers.
Both exact contracts are audited in
[MazurCurveFinite.lean](../FLTTest/MazurCurveFinite.lean).

These results consume the stated dimension bound. The smooth-dimension bridge
FC12 and rational-section bridge FC15 are proved in the modules described below;
this does not supply modular curves or Mazur's arithmetic input.

## Generic-point consumer wiring (FC16)

[GenericFibers.lean](../FLT/Mazur/GenericFibers.lean) identifies the original
`Points X generic` with rational sections of the canonical scheme pullback.
The comparison is natural in the projection. It proves geometric nonconstancy
from `G2Cusps`, then `G2Fibers` using FC14 and FC15, and `G2CurveFinite`
from those fibers and `G2Finite`.

The final consumer accepts the documented `G1Geometry`, `G2Cusps` and
`G2Finite` inputs and separatedness of the quotient. The dimension bound
`topologicalKrullDim D.genericFiber.left ≤ 1` is now proved from smoothness,
rather than supplied as an extra premise. The proof combines
[EtaleCoordinate.lean](../FLT/Mazur/EtaleCoordinate.lean) (FC12a),
[EtaleDimLe.lean](../FLT/Mazur/EtaleDimLe.lean) (FC12b), and the affine-chart
and open-cover lemmas in [SmoothDimension.lean](../FLT/Mazur/SmoothDimension.lean),
with their composition in [SmoothDimensionBound.lean](../FLT/Mazur/SmoothDimensionBound.lean).
The full equality `SmoothCurveDimension` is also proved by
[SmoothCurveDimension.lean](../FLT/Mazur/SmoothCurveDimension.lean), using the lower
bound in [EtaleDimGe.lean](../FLT/Mazur/EtaleDimGe.lean) (FC12c).
That equality is not required for this finiteness consumer.
None of the modular-curve, quotient, cusp-separation or quotient-point-finiteness
inputs is constructed by these modules. The independent axiom checks are in
[MazurGenericFibers.lean](../FLTTest/MazurGenericFibers.lean).

## Smooth sections and their ambient divisors (FC05)

[SmoothSectionCartier.lean](../FLT/Mazur/SmoothSectionCartier.lean) proves
`SmoothSectionCartier` for the actual ideal sheaf of a section. It combines
compatible affine charts, the localized augmentation kernel, and flatness of
the section image over the base.
[SmoothOpenSectionCartier.lean](../FLT/Mazur/SmoothOpenSectionCartier.lean) proves
`SmoothOpenSectionCartier`: the ambient family need only be separated, and
smoothness of relative dimension one is required only on the open containing
the section. Pulling back the actual section ideal identifies it with the
smooth-open section ideal; its Cartier charts then give ambient charts.
No global smoothness or reducedness assumption is added.
[MazurSmoothGeometry.lean](../FLTTest/MazurSmoothGeometry.lean) audits these
two section theorems and the exact smooth dimension theorem.

## Relative sums and smooth-open sections (FC06)

[RelativeSums.lean](../FLT/Mazur/RelativeSums.lean) proves `RelativeCartierSum`.
Locally, the quotient by a product of regular equations is an extension of the
two flat quotients, hence flat over the base. The local proof gives sums of
relative effective Cartier divisors on arbitrary ambient families.

Finite sums include the empty sum and repeated sections with multiplicity.
Sections may land in a smooth open of a separated family; the ambient family
need not be smooth. Their ideal products remain relative Cartier after arbitrary
base change. The module also identifies the pulled-back ideals with the ideals
of the actual base-changed sections, via `section_prod_comap_eq`.
[MazurRelativeSums.lean](../FLTTest/MazurRelativeSums.lean) audits the sum and
base-change endpoints and checks a doubled section and the empty family.

[SectionSumFinite.lean](../FLT/Mazur/SectionSumFinite.lean) further proves that
these section sums are finite over the base when the ambient family is proper.
The proof first shows that each fiber is supported on finitely many section
values, then applies proper plus quasi-finite implies finite. This uses neither
distinctness of the sections nor a noetherian base. For sections in the smooth
open, it combines with FC06 to give an actual finite flat morphism.
[MazurSectionSumFinite.lean](../FLTTest/MazurSectionSumFinite.lean) audits those endpoints.
No degree formula is claimed: the number of support points alone does not
determine rank when sections occur with multiplicity.

This proves the split section-sum construction. Descent of cyclic subgroups
(G1-A5), the degree/ample subgroup criterion, and construction of the modular
curve remain separate obligations.

## Integrated sheaf and cohomology foundations

The following modules construct divisor sheaves and tensors, and provide
intermediate results toward the genus package:

- [CurveGenus.lean](../FLT/Mazur/CurveGenus.lean) compares the canonical constants
  map with actual degree-zero cohomology and proves dimension one under
  `HasConstantGlobalSections`. That condition remains an input; finiteness
  of degree-one cohomology and the genus construction are not supplied.
- [DivisorRestrictCoherence.lean](../FLT/Mazur/DivisorRestrictCoherence.lean)
  proves identity/composition for chart dual restriction, compatibility with
  chart tensor comparisons, and transport along open immersions.
- [DivisorInvertibleSheaf.lean](../FLT/Mazur/DivisorInvertibleSheaf.lean)
  proves that the actual Cartier ideal module sheaf is locally free of rank one.
  This is the ideal (negative divisor).
- [DivisorLineBundleSheaf.lean](../FLT/Mazur/DivisorLineBundleSheaf.lean) defines
  `divisorLineBundle I hI` as the intrinsic dual of that ideal sheaf. Evaluation
  identifies its sections on Cartier charts with the dual ideal modules and
  intertwines sheaf restriction with `CartierChart.dualRestrict`. Dualized chart
  trivializations prove local rank one; the unit ideal gives the structure module.
- [DivisorLineBundleRestrict.lean](../FLT/Mazur/DivisorLineBundleRestrict.lean)
  constructs `divisorLineBundleRestrictIso` from the actual ideal-module comparison.
  Its affine evaluation agrees with `divisorChartTransport`. The comparisons on
  nested opens satisfy identity and composition using `restrictFunctorId` and
  `restrictFunctorComp` (FC10f), with no additional hypotheses.
- [DivisorLineBundleSum.lean](../FLT/Mazur/DivisorLineBundleSum.lean) constructs
  `divisorLineBundleSumIso`: the actual sheaf tensor O(D) ⊗ O(E) is O(D+E).
  On common Cartier charts it is `CartierChart.sumEquiv`; the product-evaluation
  formula and restriction between chart sections are proved. Extending the
  additive map from this basis and checking scalar linearity gives the global map.
  **FC10 remains incomplete:** coherence with FC10f's open-subscheme comparison
  still needs proof. Empty-divisor coherence is now proved on both sides in
  `DivisorLineBundleSumUnit.lean`.
- [ModuleSheafTensor.lean](../FLT/Mazur/ModuleSheafTensor.lean) constructs the
  sheaf tensor by sheafification and proves its bilinear universal property.
  [ModuleSheafTensorRestrict.lean](../FLT/Mazur/ModuleSheafTensorRestrict.lean)
  proves restriction compatibility and comparisons on trivializing charts.
  The general affine comparison must not assume all affine line bundles are free.
- [CartierTensorRank.lean](../FLT/Mazur/CartierTensorRank.lean) identifies the
  local rank-one predicates in these two developments and proves that the
  actual sheaf tensor of Cartier ideal modules is locally free of rank one.
  It does not identify this tensor with the product ideal.

[MazurSheafIntegration.lean](../FLTTest/MazurSheafIntegration.lean) audits the
restriction, tensor, rank-one and conditional degree-zero endpoints against
the three standard Lean axioms.

## Dual presheaf and basic-open tensor localization

[ModuleSheafDual.lean](../FLT/Mazur/ModuleSheafDual.lean) constructs the actual
module-valued dual presheaf: sections on U are morphisms of module sheaves
from the restricted module to the structure module. Restriction has proved
identity, composition, scalar compatibility and evaluation equations.
[ModuleSheafDualSheaf.lean](../FLT/Mazur/ModuleSheafDualSheaf.lean) proves
the sheaf condition by gluing local linear morphisms, constructs the actual
dual sheaf, and proves contravariance and compatibility with open restriction
(FC10d3). The Cartier comparison in `DivisorLineBundleSheaf.lean` completes FC10d;
the global tensor/product comparison is in `DivisorLineBundleSum.lean`. Its
open-restriction coherence and general pullback comparisons
remain separate obligations.

FC10d checked 2026-09-28 18:29 UTC: `lake build FLT.Mazur.DivisorLineBundleSheaf`,
`lake build FLT` and `lake lint -- --no-build FLT` passed without warnings.

FC10f checked 2026-09-28 19:12 UTC: `lake build FLT.Mazur.DivisorLineBundleRestrict`,
`lake build FLT` and `lake lint -- --no-build FLT` passed without warnings.

FC10g global-sum leaf checked 2026-09-28 19:32 UTC:
`lake build FLT.Mazur.DivisorLineBundleSum`, `lake build FLT`, and
`lake lint -- --no-build FLT` passed without warnings. The new file has 254 lines,
all at most 100 columns; all 1,036 `FLT.lean` imports match the source files in
C sort order. This validates the global sum construction; the two coherence
obligations above remain open.

[ModuleSheafTensorAffine.lean](../FLT/Mazur/ModuleSheafTensorAffine.lean) proves
localization comparisons on basic opens of Spec R for actual quasi-coherent
module sheaves, without requiring free section modules. The basic-open
tensor is linearly equivalent to sections of the tilde of the global tensor.
The canonical map from that tilde to the existing sheaf tensor agrees with
the sheafification unit and pure tensors.
[ModuleSheafTensorTilde.lean](../FLT/Mazur/ModuleSheafTensorTilde.lean) proves
that map invertible using the basic-open basis and sheafification.
[ModuleSheafTensorAffineOpen.lean](../FLT/Mazur/ModuleSheafTensorAffineOpen.lean)
then transports the comparison to every affine open: sections of the tensor
are canonically the tensor of sections for quasi-coherent inputs, including
locally free sheaves of any rank. Both pure-tensor equations are proved;
no global freeness of the section modules is assumed (FC10e).

[MazurDualLocalization.lean](../FLTTest/MazurDualLocalization.lean) audits the
presheaf, restriction coherence, localization and canonical comparison endpoints.
[MazurDualTensorSheaf.lean](../FLTTest/MazurDualTensorSheaf.lean) additionally
checks that the actual dual sheaf, its restriction isomorphism, and the affine
tensor equivalences depend only on the three standard Lean axioms.
These results do not prove divisor-sum/tensor compatibility or ampleness.

## Cohomology with module coefficients (FC08-A1)

[ModuleCohomology.lean](../FLT/Mazur/ModuleCohomology.lean) constructs
Ext-based cohomology for an actual module sheaf, with its global-section action
and scalar action through the specified morphism to Spec k. Coefficient maps
induce k-linear cohomology maps, with identity and composition proved.
The unit coefficient recovers `ScalarH` by a linear equivalence.

In degree zero the comparison is with actual global sections, and
`moduleScalarH0Equiv_naturality` proves compatibility with coefficient maps.
[MazurModuleCohomology.lean](../FLTTest/MazurModuleCohomology.lean) audits
functoriality, unit specialization and the natural degree-zero comparison.
[ModuleCohomologyExact.lean](../FLT/Mazur/ModuleCohomologyExact.lean) proves
linearity of the connecting maps, exactness of the six-term segments, and
injectivity at degree zero. Its hypothesis is short exactness of the underlying
complex of abelian sheaves. Finiteness propagates through each adjacent
degree pattern; this does not establish the initial geometric finiteness inputs.

[LocalizationCech.lean](../FLT/Mazur/LocalizationCech.lean) constructs the actual
principal-open Cech complex and augmentation using
[TildePrincipalOpen.lean](../FLT/Mazur/TildePrincipalOpen.lean). It proves
injectivity of the augmentation for a spanning family and that exactness of
a complex can be checked after principal localization. Exactness of this Cech
complex in all degrees is now proved for finite spanning principal families
in the exactness module described below.
Finite-dimensionality of positive-degree cohomology and genus remain open.

## Positive divisor sheaves and restriction (FC10d/f)

[DivisorLineBundleSheaf.lean](../FLT/Mazur/DivisorLineBundleSheaf.lean) constructs
O(D) as the actual dual of the Cartier ideal sheaf, proves it locally free of
rank one, and identifies O(0) with the structure module.
[DivisorLineBundleRestrict.lean](../FLT/Mazur/DivisorLineBundleRestrict.lean)
identifies restriction of the ideal module with the pulled-back ideal module.
It then constructs restriction of O(D), matches the affine dual-ideal transport,
and proves identity and composition compatibility on nested opens.
The global sum/tensor isomorphism is proved in the module described below;
its open-restriction coherence and ampleness remain separate obligations.

[MazurCohomologyDivisor.lean](../FLTTest/MazurCohomologyDivisor.lean) audits
these cohomology, initial Cech and divisor-restriction endpoints against the
three standard Lean axioms. The final FLT arithmetic inputs are unchanged.

## Affine finiteness, split Cech covers and the global divisor sum

[AffineCoherent.lean](../FLT/Mazur/AffineCoherent.lean) proves that a locally
finitely presented module sheaf on an affine scheme has finite global sections.
Over a Noetherian ring, such sheaves are exactly the tildes of finite modules,
using Mathlib's actual local finite presentation predicate and canonical counit.
This is not yet a finiteness theorem for positive-degree cohomology.

[LocalizationCechCompare.lean](../FLT/Mazur/LocalizationCechCompare.lean)
identifies localization of finite Cech terms with sections on intersections
inside a principal open. The comparisons commute with coefficient maps,
differentials and augmentation.
[LocalizationCechSplit.lean](../FLT/Mazur/LocalizationCechSplit.lean) constructs
a contraction when one defining function is a unit, proving exactness of the
augmented complex, vanishing of positive homology and the degree-zero comparison
in that case. [LocalizationCechExact.lean](../FLT/Mazur/LocalizationCechExact.lean) proves
exactness of the augmented section complex in every degree for finite spanning
principal families, positive homology vanishing and the canonical H0 comparison
via augmentation. This completes the principal-cover exactness step (FC08-A5).

[CechSheafH.lean](../FLT/Mazur/CechSheafH.lean) identifies Ext-based degree-zero
cohomology with compatible section families for an open cover. The equivalence
is natural in the coefficient sheaf and respects coefficient multiplication.
[CechSheafHZero.lean](../FLT/Mazur/CechSheafHZero.lean) now supplies the
categorical adapter, including the differential sign and tuple coordinates.
Its `sheafHZeroEquiv` composes the two comparisons to identify Ext-based H0
with categorical Cech homology, naturally in the coefficient sheaf.
Comparison in higher degrees remains open.

[DivisorLineBundleSum.lean](../FLT/Mazur/DivisorLineBundleSum.lean) glues the
Cartier-chart sum comparisons to the actual sheaf isomorphism
O(D) tensor O(E) ≅ O(D+E), with the product-evaluation formula.
[DivisorLineBundleSumUnit.lean](../FLT/Mazur/DivisorLineBundleSumUnit.lean)
proves compatibility with the empty divisor on both sides, using the prescribed
trivialization of O(0) and the tensor unit map.
Compatibility with open-subscheme restriction comparisons remains separate;
this does not discharge all of FC10.

[MazurAffineCechSum.lean](../FLTTest/MazurAffineCechSum.lean) audits these endpoints
against the three standard Lean axioms. No arithmetic FLT input is removed.

## Free-sheaf Cech construction and evaluation

[CechFreeOpen.lean](../FLT/Mazur/CechFreeOpen.lean) constructs the free abelian
sheaf on an open and identifies maps from it with sections, naturally in both
the open and the coefficient sheaf. It also compares open-wise Ext H0 with sections.
[CechFreeResolution.lean](../FLT/Mazur/CechFreeResolution.lean) constructs the
augmented free-sheaf chain complex, its constant-integer term, coproduct terms,
and signed differential and augmentation formulas.
[CechFreeStalkInsertion.lean](../FLT/Mazur/CechFreeStalkInsertion.lean)
constructs an extra degeneracy by choosing a cover member containing the point.
[CechFreeStalkExactAll.lean](../FLT/Mazur/CechFreeStalkExactAll.lean) proves
exactness on every stalk in every degree, including the augmented integer term.
[CechFreeExact.lean](../FLT/Mazur/CechFreeExact.lean) then proves exactness of the
actual free-sheaf complex for any open cover.

[CechInjectiveAcyclic.lean](../FLT/Mazur/CechInjectiveAcyclic.lean) identifies
Hom from free terms with Cech cochains, including the alternating differentials.
It proves that injective coefficient sheaves have zero positive Cech homology.
[CechAcyclicCokernel.lean](../FLT/Mazur/CechAcyclicCokernel.lean) proves that
cover acyclicity persists under cokernels of embeddings into injectives.
Vanishing of H1 on intersections implies surjectivity on sections, yielding
degreewise short exact Cech complexes under the explicit acyclicity hypothesis.
`CechConnecting.lean` now constructs the connecting maps of the actual Cech
complexes, proves exactness on both sides, and proves naturality for morphisms
of short exact coefficient sequences. Cover acyclicity of the first term remains
an explicit hypothesis.
`CechDimensionShift.lean` now identifies the positive-degree connecting maps
with additive equivalences, for both Cech and Ext-based sheaf cohomology, and
proves naturality in short exact coefficient sequences. In degree one the
identification is with the quotient by the preceding degree-zero map, not with
H0 itself. The middle coefficient is required to be injective; the Cech results
also require an open cover and cover acyclicity of the first coefficient.
The higher-degree comparison is now proved in `CechAcyclicComparison.lean`,
with naturality and independence of the chosen injective embedding proved in
`CechAcyclicNaturality.lean`. `ModuleCechScalar.lean` makes it linear over global
sections and over the specified base scalars. Positive quasi-coherent cohomology
on arbitrary affine schemes vanishes by `AffineCohomologyVanishingAffine.lean`.
`AffineCoverCohomology.lean` consequently computes actual module cohomology from
any affine open cover of a separated scheme, naturally in the coefficient module.

`FiniteAffineCoverDimension.lean` proves vanishing in degrees at least the number
of affine charts, including degree zero for an empty cover. The separate
`FiniteAffineCoverFiniteness.lean` and `CoherentAffineCoverSections.lean` results
are conditional finiteness reductions: finite intersection sections over the
specified base ring suffice. Coherence gives finiteness over each intersection's
own ring, which is not enough to conclude finiteness over the base ring.
`ProjectiveGeneration.lean` extends finite families of chart sections in a
common natural twist and proves the resulting global evaluation map is an
epimorphism, using the derived finite local generators. It constructs a finite
free epimorphism onto a twist of any locally finitely presented module sheaf on
finite-coordinate polynomial projective space, without a Noetherian hypothesis.
`ProjectiveGenerationEventually.lean` strengthens this to every sufficiently
large natural twist, with a fixed finite generator index. No epimorphism or
extension witness is supplied by the caller. `FLTTest/MazurProjectiveGeneration.lean`
audits the five extension and generation endpoints.
General projective/proper coherent cohomology finiteness remains open: finite
free generation alone does not provide the remaining kernel/resolution argument.

`ClosedPushforwardCohomology.lean` identifies coherent closed-direct-image
cohomology with that on the closed subscheme, linearly over the specified base. The comparison is natural in coefficient
morphisms, including restriction to an arbitrary base ring and the existing
field-valued scalar cohomology maps.
`ClosedSubschemeCohomology.lean` transfers the ambient finite-cover vanishing
bound and proves equivalence of base-ring finiteness on both sides. This does
not supply the still-missing projective coherent finiteness input.
`FLTTest/MazurAffineCohomology.lean` audits nineteen comparison, naturality, vanishing and
conditional-finiteness endpoints against the three standard logical axioms.

`CoherentDevissage.lean` defines support using actual additive stalks and proves
support containment for subsheaves, Noetherian induction on closed subsets, and
reduction of that induction to irreducible closed subsets. Its two-out-of-three
lemmas transfer properties along explicitly coherent short exact sequences and
finite filtrations. This is only the induction and extension core: closedness of
coherent support, coherent subquotients, and generic-point extension arguments
are still needed for the full geometric devissage criterion.
`FLTTest/MazurCechConnecting.lean` audits eleven connecting-map and induction
endpoints; each uses only the three standard logical axioms.

[MazurCechAcyclic.lean](../FLTTest/MazurCechAcyclic.lean) audits the contraction,
stalkwise and sheaf exactness, injective vanishing and acyclic-cokernel endpoints.
No new arithmetic assumption is introduced or existing FLT arithmetic input removed.

[MazurCechResolution.lean](../FLTTest/MazurCechResolution.lean) audits the
principal-cover exactness, natural categorical H0 comparison, free-sheaf
construction and divisor-unit equations against the standard Lean axioms.

## Stalk coordinates and the projective-line building block

[CechFreeOpenStalk.lean](../FLT/Mazur/CechFreeOpenStalk.lean) computes the
stalk of the free sheaf on an open as the free abelian group on membership.
The comparison is natural in inclusions, agrees with local generators, and
gives the stalks and differential formulas of the free Cech terms.
In particular, `freeOpenStalk_isZero_of_notMem` proves vanishing outside the open.
The contraction and exactness of the free-sheaf complex are now proved by
the modules described above.

[ProjectiveLineCharts.lean](../FLT/Mazur/ProjectiveLineCharts.lean) constructs
the scheme by gluing two affine lines along the Laurent spectrum with inverse
coordinates, proves the charts cover, and supplies the structure morphism.
[ProjectiveLineEndpoints.lean](../FLT/Mazur/ProjectiveLineEndpoints.lean) constructs
the zero and infinity sections and proves their underlying points, morphisms
and sections distinct. This is a building block for cyclic pinching, not yet
a construction of Neron polygons or a proof of their geometric properties.

[MazurStalkFibers.lean](../FLTTest/MazurStalkFibers.lean) audits the stalk
comparisons, completed-local-ring node presentation, base change of the
partial nodal fiber conditions, and projective-line endpoints against the
three standard Lean axioms. The final FLT arithmetic inputs are unchanged.

`DRFiberClassification.lean` strengthens the nodal fiber and proper-flat family
records with the explicit condition that each geometric fiber is smooth or
satisfies the cyclic pinching predicate `IsNeronPolygon`. It proves stability
under arbitrary base change by composing geometric pullback squares, retaining
all earlier nodal conditions. It neither constructs pinching pushouts nor proves
classification for a concrete family. Arithmetic genus one and the group/action
data of generalized elliptic curves remain separate obligations.

`FLTTest/MazurShiftFibers.lean` audits twelve dimension-shift and classified-fiber
endpoints against the three standard logical axioms.

## Sources and the two different kinds of curve

[M] B. Mazur, *Modular curves and the Eisenstein ideal*, IHÉS 47 (1977), 33–186,
[Numdam PDF](https://www.numdam.org/item/PMIHES_1977__47__33_0.pdf).
Printed II §1, pp. 62–64 and III (4.1), pp. 151–152 were reread for this task.
In the Numdam file these are PDF pages 31–33 and 120–121; the cover is not printed page 33.

[DR] P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*,
LNM 349 (1973), 143–316, Chapter II. This is Mazur's reference [9].
The [DR source ledger](DR_SOURCE_LEDGER.md) independently verifies the Bonn primary scan
(checked 2026-09-28): I.1.0–1.2, the node models in I, Proposition/Theorem 5.3, and
II.1.1–1.6, 1.12, with French quotations and printed/PDF pages. The definitions and
these supporting statements are recovered; their Lean realizations and the C1/C2/C3
comparison proofs are not. In particular, II.1.4 requires smooth connected genus-one
or Néron-polygon geometric fibers. C1's nodal genus-one conditions alone are insufficient:
the II.1.3 characterization also requires trivial dualizing sheaf. Leaf 24 must use the
classification or prove the strengthened characterization. G1-A1/A3/A5/A6 remain gated
as complete generalized-elliptic-curve constructions, including their group/action data.

[S] Stacks Project. The tags below were checked against the project's `tags/tags` index and
chapter TeX sources (`curves`, `divisors`, `morphisms`, `coherent`, `varieties`) on 2026-09-28.
Each linked tag identifies a statement, not just a chapter. EGA IV §21.15 is background for
relative divisors, as discussed at [062T](https://stacks.math.columbia.edu/tag/062T).
Hartshorne III §9 is background for flat base change; the checked Stacks statements control
hypotheses here. Neither background citation substitutes for an unchecked proof lemma.

Keep these objects distinct:

- G1-A defines a **generalized elliptic curve** E/S. Its geometric fibers can be reducible
  nodal polygons. It has arithmetic genus one, not necessarily a smooth or integral fiber.
- G2-D uses the **coarse modular curve** X over Q. It is smooth, proper and geometrically
  integral, and generally has genus greater than one. Do not impose genus one on X.
- The subgroup H lies in the smooth locus of E. The divisor associated with H is on E;
  the proper-curve finite-map argument concerns X, not E or its polygons.

Mazur II §1 supplies the application context: generalized elliptic curves with level structure,
proper moduli stacks, smooth coarse models away from p, and the disjoint cusp sections.
It does not prove the eight generic foundation families listed in the planning document.
III (4.1) uses a nontrivial quotient generated by the curve image, then finiteness of the
map to that image. The present consumer can instead use the two distinct cusp images and
[S, 0CCL] directly; no general construction of a one-dimensional scheme-theoretic image is
needed to obtain G2Fibers. This trims that foundation without changing the arithmetic route.

## Exact consumer statements

Throughout, schemes and morphisms retain their specified base maps. A field-valued point is
an over-morphism from Spec k, not an unstructured topological point. The contracts live in
[`FLT/Mazur/FCurveContracts.lean`](../FLT/Mazur/FCurveContracts.lean), namespace
`FLT.Mazur.FCurve`. A named `def ... : Prop` is a target to prove, never an installed instance.

### C1. Proper relative curves: G1-A1/A2/A3 and G2-D2

For f : E → S use proper, flat and locally finitely presented. Require every geometric fiber
to be nonempty, geometrically connected, reduced, pure of dimension one and of arithmetic
genus one, with at worst nodes; the smooth-locus group/action conditions belong to G1-A.
The latter requirements must come from the actual DR definition, not an opaque predicate.
`ProperFlatFamily` deliberately specifies only the three morphism properties;
`GeometricFiberDimensionOne` specifies dimension one of each algebraically closed field fiber.
Global dimension one alone does not assert purity, connectedness, reducedness or nodality.

FC08-C23 (`CurveNode.lean`) pins nodes by the maximal-ideal adic completion of the actual
scheme stalk, with its scalar action induced by the structure morphism: the completion is
k-algebra isomorphic to `MvPowerSeries (Fin 2) k` modulo `(X₀ X₁)`. It proves equivalence
with a surjective power-series presentation having exactly that kernel. `AtWorstNodes`
requires each closed point to lie in the actual smooth locus or satisfy this node criterion;
it does not require a smooth fiber. Over an algebraically closed field this is the ledger's
ordinary double point model. Étale normal forms, smooth/node disjointness and field-extension
stability are not proved here; C24's fiber conditions and C2's genus obligations remain open.

The needed stability statement is: after **any** S' → S, the three morphism properties persist,
and the geometric fibers of E ×S S' identify with field extensions of fibers of E.
[S, 01W4](https://stacks.math.columbia.edu/tag/01W4),
[01U9](https://stacks.math.columbia.edu/tag/01U9),
[01TS](https://stacks.math.columbia.edu/tag/01TS), and
[02FY](https://stacks.math.columbia.edu/tag/02FY) give properness, flatness,
finite presentation and preservation of fiber dimension respectively.
The first part is `ProperFlatBaseChange`; genus stability is C2/C3, not a consequence of it.

G1-A2 only needs transport of this data under an isomorphism over S, and G1-A3 needs the
identity/composite pullback isomorphisms with their structure-map equations. These are
category/scheme adapters. They do not construct the smooth-locus group or action.

### C2. Relative genus/cohomology: G1-A1

For a proper curve E/k with H⁰(E,O_E) = k, define
`g(E/k) = dim_k H¹(E,O_E)`; require g = 1 for generalized elliptic fibers.
[S, 0BY7](https://stacks.math.columbia.edu/tag/0BY7) is precisely this definition.
Finiteness of these vector spaces is the i = 0,1, F = O_E case of
[S, 02O6](https://stacks.math.columbia.edu/tag/02O6): proper over an affine Noetherian
base and coherent coefficients implies finite cohomology modules.
[S, 0BUG](https://stacks.math.columbia.edu/tag/0BUG), parts (2)–(3), implies H⁰ = k
for a nonempty proper connected reduced curve over an algebraically closed field; part (7)
gives the geometrically connected/reduced version over any field. Port this proof if H⁰ = k
is derived rather than included in the fiber contract.
Do not define genus by `finrank` without proving finite dimensionality first.

Only fiberwise genus is required here. A locally free sheaf R¹f_*O_E and arbitrary-base
cohomology-and-base-change are stronger targets and are not prerequisites merely for defining
G1-A1 or its pullback. No Riemann–Roch, duality, Jacobian or genus formula for X₀(p) is requested.

**Gated:** attach the scalar action and H⁰/H¹ to the actual structure sheaf, prove the
finite-dimensionality comparison, and verify the precise DR fiber hypotheses. The current
Lean file intentionally has no `genus : Scheme → Nat` parameter or arbitrary supplied H¹.
Such parameters would typecheck while failing to pin this missing construction.

### C3. Genus under base change: G1-A3

For k ⊆ K and E/k as in C2, the **canonical** comparison is
`K ⊗_k H^i(E,O_E) ≅ H^i(E_K,O_EK)` for i = 0,1, as K-vector spaces.
[S, 02KH](https://stacks.math.columbia.edu/tag/02KH) proves flat base change for
quasi-coherent coefficients on a quasi-compact quasi-separated morphism. Field extensions
are flat; proper E/k supplies the compactness/separatedness conditions.
[S, 0BY9](https://stacks.math.columbia.edu/tag/0BY9) then gives dimension one,
H⁰ = K and equality of genus after a field extension.

For an arbitrary S' → S and a geometric point of S', identify its fiber with E_s extended
from κ(s). Apply this field-extension result, including its H⁰ assertion. No flatness of
S' → S is required, and no arbitrary-base R¹f_* base-change theorem is being claimed.

**Gated with C2:** scalar cohomology and the canonical comparison map have not been represented
and checked in Lean. Numerical equality of two unspecified natural numbers is not a substitute.

### C4. Effective Cartier divisors: G1-A5

An effective Cartier divisor D ⊂ E is a closed subscheme whose quasi-coherent ideal is locally
generated by a nonzerodivisor. Equivalently its ideal is invertible:
[S, 01WR](https://stacks.math.columbia.edu/tag/01WR) and
[01WS](https://stacks.math.columbia.edu/tag/01WS).
`EffectiveCartier I` uses the latter affine-local definition on actual `IdealSheafData`.
An invertible ideal need not be principal on every affine open; the existential neighborhood
in the Lean definition is essential. The empty divisor is allowed (local equation 1).

A section s of a separated smooth relative curve is a closed immersion and its image is a
relative effective Cartier divisor (`SmoothSectionCartier`).
[S, 067R](https://stacks.math.columbia.edu/tag/067R) says a section of a smooth morphism
is a regular immersion. In relative dimension one its regular ideal has one generator;
separatedness makes the immersion closed. This last codimension-one specialization still
requires a local smooth-algebra proof; it is not present merely because 067R is cited.
The image is isomorphic to S, so it is flat over S.
For a singular generalized curve use `SmoothOpenSectionCartier`: j : U → E is an open
immersion, U/S is smooth of relative dimension one, E/S is separated, and s is a section
landing in U. The divisor is the image of s followed by j on **E**. Requiring E/S itself
to be smooth would exclude polygon fibers.

Sums of effective divisors multiply their ideal sheaves:
[S, 01WU](https://stacks.math.columbia.edu/tag/01WU).
For relative effective divisors the sum is again relative:
[S, 0B8U](https://stacks.math.columbia.edu/tag/0B8U), encoded as `RelativeCartierSum`.
This supplies the divisor Σ_{i∈Z/p} [iP] for a section of the smooth-locus group.
Coincident sections count with multiplicities. A union of point sets is incorrect.
The cyclic-level condition is an equality of this divisor with the subgroup divisor after
an appropriate local choice of generator; effective Cartier theory alone does not define
or prove cyclicity over arbitrary rings. Its exact DR/descent interface remains gated.

### C5. Divisor pullback: G1-A3/A5

A relative effective Cartier divisor means D is Cartier on E and D → S is flat
([S, 062T](https://stacks.math.columbia.edu/tag/062T)).
For any S' → S the inverse image of D is effective Cartier on E ×S S'
([S, 056Q](https://stacks.math.columbia.edu/tag/056Q)), and remains flat over S'.
This is `RelativeCartierBaseChange`, using the existing ideal-sheaf `comap`.

The exact local input to 056Q is: for A → B, h ∈ B regular and B/(h) flat over A,
multiplication by 1 ⊗ h on A' ⊗A B is injective for every A-algebra A'.
Tensor the sequence `0 → B → B → B/(h) → 0`; flatness of the **quotient** preserves
injectivity. Flatness of B alone does not justify this assertion.
[S, 01WW](https://stacks.math.columbia.edu/tag/01WW) gives pullback of sums whenever
both divisor pullbacks exist. Also retain identity/composite pullback compatibilities.
Pullback along an arbitrary map of ambient schemes is not always Cartier: pulling V(t)
on A¹ back to t = 0 is the elementary counterexample.

### C6. Finite-flat degree: G1-A4/A5

Use finite, flat, **locally finitely presented** H → S and constant rank p.
[S, 02KA](https://stacks.math.columbia.edu/tag/02KA) defines finite locally free and degree;
[02KB](https://stacks.math.columbia.edu/tag/02KB) equates it with those three properties;
[02KD](https://stacks.math.columbia.edu/tag/02KD) gives arbitrary base change.
The degree at s is dim_{κ(s)} Γ(H_s,O_Hs), not the number of geometric points.
`FiniteLocallyFreeDegree` and `DegreeBaseChange` use Mathlib's actual `Hom.finrank`.
Constant rank is a pointwise condition and works on disconnected bases.

For this application all test schemes lie over T = Spec Z[1/(2p)], so p is invertible.
An alternative cyclic-level interface via étale-local generators is possible after proving
that the order-p subgroup is étale and verifying the DR comparison. Noninvertible-p level
theory is not an additional requirement of these consumers.

Finite + flat is enough over a locally Noetherian base, but G1-A3 quantifies over arbitrary
schemes, so do not delete finite presentation. A finite flat rank-p subgroup is not
necessarily étale at p and may have fewer than p geometric points. The group law, subgroup
closed immersion, and local generator/descent data belong to G1-A4/A5, not this rank adapter.
For a divisor made of n sections, rank n still requires the sum/flatness and length argument.

### C7. Ampleness: G1-A6

For a proper curve C/k and invertible L, [S, 0B5Y](https://stacks.math.columbia.edu/tag/0B5Y)
says L is ample iff its degree on every one-dimensional irreducible component is positive.
Its integral-curve input is [0B5X](https://stacks.math.columbia.edu/tag/0B5X).
For a reduced nodal polygon and an effective Cartier divisor D supported in the smooth
locus, this becomes: O(D) is ample iff D meets every irreducible component. The restriction
of D to a component has positive degree exactly when that intersection is nonempty.
`MeetsEveryComponent` records the support side only; it is not a definition of ampleness.
On a smooth connected fiber any nonempty such divisor meets the unique component. On a
split n-gon a subgroup meeting only the identity component fails the criterion when n > 1.
The p-gon test itself waits for G1-B, as stipulated in the original plan.

**Gated:** O(D), invertible-sheaf degree, ampleness and the comparison with this support
condition have no ready scheme-level API. The usual relative upgrade needs separate care:
[S, 0D2N](https://stacks.math.columbia.edu/tag/0D2N) proves that a line bundle ample on a
fiber is relatively ample nearby for a proper morphism with **Noetherian base**.
This is not an arbitrary-base theorem. Pin the general limit/descent theorem, or prove that
the required DR ample-level definition can be checked on geometric fibers, before releasing
G1-A6 for arbitrary test schemes. No blanket EGA citation closes that gate.

### C8. Dimension-one maps and rational fibers: G2-D1/D2/D3/D4

The required finite-map statement is the integral-source specialization of
[S, 0CCL](https://stacks.math.columbia.edu/tag/0CCL): if X is proper over k of dimension
at most one, Y is separated over k, and each dimension-one component of X has image
containing at least two points, then f : X → Y over k is finite.
For integral X, one pair a,b with f(a) ≠ f(b) suffices. This is
`NonconstantProperCurveFinite`. Y need not be a curve, smooth, proper or integral.

There are four genuine intermediate obligations:

1. `DistinctSectionImages`: two distinct k-valued images give distinct underlying image
   points. These are k-**sections** of the structure map. The over-base condition makes
   the residue map at a k-rational point unique. It is false for arbitrary Spec K maps
   without their fixed base equation. Apply this to G2Cusps; then use that f is over k.
2. `SmoothCurveDimension`: a nonempty smooth relative-dimension-one k-scheme has
   topological dimension one. Nonemptiness excludes the empty smooth scheme. Mathlib's
   standard-smooth definition is not already this topological assertion. The source is
   [S, 02G1](https://stacks.math.columbia.edu/tag/02G1) (differential rank equals local
   fiber dimension) and [02G2](https://stacks.math.columbia.edu/tag/02G2) (constant relative
   dimension). The proof of 02G1 reduces to standard-smooth affine algebras; this is the
   local bridge FC12 must split, not a new genus theorem.
3. `ProperClosedSubsetFinite`: a proper closed subset of an irreducible Noetherian T0
   space of dimension at most one is finite. Use it on closed fibers; to handle all
   fibers use the proper finite-neighborhood argument in 0CCL, rather than asserting
   every point of Y is closed. Mathlib already has the latter neighborhood theorem.
4. `FiniteRationalFibers`: a finite k-morphism has finite fibers on k-sections. Base change
   along a target section gives a finite k-scheme. Its rational points inject into its
   finite underlying space, using the fixed residue maps as in step 1. An alternative is
   injection into algebraic-closure points followed by `pointEquivClosedPoint`; that
   route additionally requires faithful base-change injectivity of hom sets.

Finite maps are locally quasi-finite and have finite scheme fibers. This alone is not a
proof about rational morphism sets until step 4 is supplied. G2-D4 is then a finite-union
argument using G2Finite. This family supplies **nothing** for G2-D5 torsion specialization,
D6 arithmetic specialization, or D7 the cusp contradiction; those gates remain unchanged.
No general image-dimension theorem or group-generation theorem is needed by this version.

## Pinned Mathlib survey

All paths below are under `.lake/packages/mathlib/Mathlib/`. “Missing” means the precise
consumer theorem/API was not found in this pinned tree; nearby infrastructure is listed.
The survey used `rg` over AlgebraicGeometry, sheaf cohomology, flat modules and dimension files.

| Item | Status and checked declarations |
| --- | --- |
| C1 proper/flat/fp | **Exists**: `IsProper`, `Flat`, `LocallyOfFinitePresentation`. |
| C1 base change | **Exists**: `IsProper.isStableUnderBaseChange`, |
| | `Flat.isStableUnderBaseChange`; pullback instances in the morphism files. |
| C1 smooth dimension | **Partial**: `SmoothOfRelativeDimension`, |
| | `smoothOfRelativeDimension_isStableUnderBaseChange`; topological bridge missing. |
| C2 genus | **Missing**: no relative/arithmetic scheme-genus definition was found. |
| C2 cohomology | **Partial**: `CategoryTheory.Sheaf.H`, `Sheaf.H.map`, |
| | `Scheme.Modules`, `Scheme.Modules.pullback`, `Scheme.Modules.pushforward`. |
| C2 scalar Ext | **Partial**: `CategoryTheory.Abelian.Ext` and its module instance in |
| | `Algebra/Homology/DerivedCategory/Ext/Linear.lean`; no ready O_E genus package. |
| C3 genus base change | **Missing**: scalar structure-sheaf comparison and finiteness. |
| | `Module.finrank_baseChange` exists for vector spaces; it is not cohomology base change. |
| C4 Cartier | **Partial**: `Scheme.IdealSheafData`, `.ideal`, `.subscheme`, `.subschemeι`, |
| | `.equivOfIsAffine`; no effective-Cartier predicate or smooth-section theorem found. |
| C4 sums | **Partial**: ideal-sheaf multiplication, `isRegular_mul_iff`; relative sum missing. |
| C5 pullback | **Partial**: `Scheme.IdealSheafData.comap`, `.comapIso`, `.comap_id`, |
| | `.comap_comp`, `.support_comap`; preservation of Cartier regularity missing. |
| C5 flat algebra | **Partial**: `Module.Flat.lTensor_exact`, `.rTensor_exact`, |
| | `.isSMulRegular_of_isRegular`; 056Q needs quotient-flatness, not just a flat ambient map. |
| C6 rank | **Exists**: `Scheme.Hom.finrank`, `.finrank_SpecMap_algebraMap`, |
| | `.finrank_pullback_snd`, `.finrank_of_isPullback`, `.isLocallyConstant_finrank`, |
| | `.one_le_finrank_iff_surjective`, `.isIso_iff_finrank_eq`. |
| C7 ample divisor | **Missing**: scheme Cartier-associated line bundle, degree, ampleness. |
| | `SheafOfModules.IsLocallyFree` is infrastructure, not this criterion. |
| C8 dimension | **Partial**: `topologicalKrullDim`, `topologicalKrullDim_subspace_le`, |
| | `IsHomeomorph.topologicalKrullDim_eq`; no proper-integral-curve finite-map theorem found. |
| C8 properness | **Exists**: `IsProper.of_comp` for a separated target structure map. |
| C8 finite neighborhoods | **Exists**: |
| | `exists_isFinite_morphismRestrict_of_finite_preimage_singleton` in |
| | `AlgebraicGeometry/ZariskisMainTheorem.lean` (Stacks 02UP). |
| C8 finite fibers | **Exists**: `IsFinite.of_isProper_of_locallyQuasiFinite`, |
| | `Scheme.Hom.finite_preimage_singleton`, `Scheme.Hom.finite_preimage`. |
| C8 rational points | **Partial**: `Scheme.SpecToEquivOfField`, |
| | `pointEquivClosedPoint`, `ext_of_apply_closedPoint_eq`; the latter two require |
| | an algebraically closed field. The over-Q finite-fiber adapter remains missing. |

Principal files: `Morphisms/{Proper,Flat,FinitePresentation,Smooth,FlatRank,QuasiFinite}.lean`,
`IdealSheaf/{Basic,Subscheme,Functorial}.lean`, `ZariskisMainTheorem.lean`,
`AlgClosed/Basic.lean`, `ResidueField.lean`, `Modules/Sheaf.lean`,
`CategoryTheory/Sites/SheafCohomology/Basic.lean`,
`Algebra/Category/ModuleCat/Sheaf/LocallyFree.lean`, `Topology/KrullDimension.lean`,
`RingTheory/Flat/{Basic,TorsionFree}.lean`, `LinearAlgebra/Dimension/Constructions.lean`.

The existing `FLT/GroupScheme/FiniteFlat.lean` is a separate affine finite-flat group-scheme
bridge; reuse it when producing the group/subgroup data. It does not supply a divisor or
ample-level theorem. Elliptic-curve `Jacobian` files are coordinates, not relative Jacobians.

## Leaf contracts and dispatch

Sizes are **200–500 new Lean lines per leaf**, including supporting lemmas; they are estimates,
not quotas. Do not pad an adapter. Hours are worker-hours, not calendar promises.
A gated row is a reserved slot, not a claim that an unported existence theorem fits 500 lines.
If its source proof expands beyond that bound, subdivide and review before dispatch.
All acceptance statements mean proved theorems, not merely inhabitants accepted as inputs.

| Leaf | Dependencies | Lines / hours | Acceptance and release state |
| --- | --- | --- | --- |
| FC01 family transport | L01–L02, current Mathlib | 200–300 / 8–16 | **Ready**: C1 core |
| | | | pullback, iso transport and identity/composite comparison equations. |
| FC02 constant degree | FC01 conventions | 200–300 / 8–16 | **Ready**: C6 degree |
| | | | pullback/iso transport, rank-one and positive-rank corollaries. |
| FC03 Cartier charts | current Mathlib | 250–400 / 15–30 | **Ready**: C4 local |
| | | | predicate, affine criterion, restriction, empty divisor and absolute sums. |
| FC04 relative pullback | FC03 | 300–500 / 25–45 | C5 quotient-flat tensor lemma |
| | | | and `RelativeCartierBaseChange`, with identity/composition equations. |
| FC05 section divisors | FC03 | 300–500 / 30–60 | **Gated**: pin codimension-one |
| | | | smooth local proof; prove `SmoothSectionCartier`, not regularity as an input. |
| FC06 relative sums | FC04–FC05 | 250–450 / 20–40 | C4 relative sum and finite |
| | | | sums of sections commute with pullback. Cyclic descent remains G1-A5. |
| FC07 scalar cohomology | actual O_E module/sheaf bridge | 300–500 / 30–60 | **Gated**: |
| | | | canonical H⁰/H¹ with k-action, H⁰/global-sections comparison. |
| FC08 genus definition | FC07, finite-cohomology port | 200–400 / 20–40 | **Gated**: |
| | | | C2 with proven finiteness; DR connected/reduced/node hypotheses pinned. |
| FC09 genus pullback | FC07–FC08, 02KH port | 300–500 / 30–60 | **Gated**: canonical |
| | | | field-extension comparison, then geometric-fiber genus preservation C3. |
| FC10 divisor line bundle | FC03, invertible-module tensor API | 300–500 / 25–50 | Sum proved; |
| | | | **Gated**: coherence with open restriction; empty-divisor coherence proved. |
| FC11 ample criterion | FC06/FC10, degree/ampleness ports | 300–500 / 30–60 | **Gated**: |
| | | | C7 component criterion; resolve arbitrary-base gate before relative use. |
| FC12 smooth dimension | smooth algebra dimension lemmas | 300–500 / 25–50 | |
| | | | `SmoothCurveDimension`; pin local proof subdivision before release. |
| FC13 closed subsets | topology dimension/noetherian API | 200–350 / 15–30 | C8 |
| | | | `ProperClosedSubsetFinite`, including the empty subset. |
| FC14 finite curve maps | FC12–FC13, existing finite neighborhoods | 250–450 / 20–40 | |
| | | | `NonconstantProperCurveFinite` for separated targets, not only curves. |
| FC15 rational fibers | L01, residue-field point API | 250–450 / 20–40 | C8 |
| | | | `DistinctSectionImages` and `FiniteRationalFibers` over any field. |
| FC16 consumer wiring | FC14–FC15, supplied G1Geometry/G2Cusps | 200–350 / 10–25 | |
| | | | G2Fibers; with G2Finite derive G2CurveFinite. No arithmetic assumptions hidden. |

First dispatch order: **FC01, FC02, FC03**. FC02 consumes FC01's family/over-base conventions;
FC03 is independent and can follow either. Their instructions are concrete:

1. FC01: prove `ProperFlatBaseChange`, transport the three properties along over-isomorphisms,
   and expose pullback identity/composite equations usable by a later generalized-curve record.
   Acceptance excludes genus and geometric-fiber dimension claims; test arbitrary bases.
2. FC02: prove `DegreeBaseChange` from the existing rank theorem, preserve degree under
   over-isomorphisms, and derive surjectivity for positive degree and isomorphism at degree one.
   Check the affine ring-rank comparison. Never count geometric points to define degree.
3. FC03: implement the Cartier predicate using the actual `IdealSheafData`, prove its
   affine-local characterization and invariance on restrictions, then empty divisor and sum.
   Verify the ideal/subscheme identification; do not require globally principal ideals.

FC04/FC06/FC13–FC16 have source-level statements but still require a proof-size review after
the first adapters. FC12 needs a local smooth-algebra lemma list, not a task called “dimension
theory”. The cohomology/degree/ampleness ports named in dependencies are **unbudgeted external
foundations** until separately split. This document does not justify the previous 8–16-leaf
allowance as a complete cost bound. The sixteen rows above are a scheduling envelope only.

## Typed coverage, gates and validation

The committed Lean file checks the C1 core/dimension predicates, C4/C5 divisor predicates and
proof targets, C6 degree contracts, C7 support predicate, and all four C8 proof targets.
It adds no proof of a missing theorem. C2/C3 scalar cohomology and C7 actual line-bundle
ampleness have **no Lean statement yet**: their required data types/constructions are the
explicit gates above. Treating a user-supplied genus or ample predicate as those constructions
would conceal the missing work. G1-A1–A6 therefore remain incomplete despite the ready leaves.

Reproduce source/API evidence with the pinned tree and the linked Stacks tags. For local checks:

```sh
lake build FLT.Mazur.FCurveContracts
lake build FLT
lake lint -- --no-build FLT.Mazur.FCurveContracts
git diff --check
```

The repository checks also compare the sorted import list in `FLT.lean` with every `.lean`
path under `FLT/`, check equality and count, scan the new Lean for prohibited proof shortcuts,
and enforce 100-character lines on both new files. Builds are run sequentially under the
10 GiB memory limit. The final checked-at timestamp and local commit are recorded in `LAST.txt`.

Checked at 2026-09-28 13:12 UTC: both builds exited 0 without warnings; the configured Batteries
linter passed. All 993 imports match all 993 source modules in byte order. The new Lean
contains none of the prohibited proof shortcuts; 100-column and whitespace checks passed.
