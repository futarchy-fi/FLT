# G1 after G5: polygon action, genus and the remaining Mazur gates

P4 (`PolygonNodeEqualizer`) and P5 (`PolygonIncidence`) supply local ring
exactness and cyclic linear exactness. They do not construct a polygon or
identify that linear complex with sheaf cohomology. This split develops the
relative group candidate and isolates its comparison with the smooth locus.
The historical G1–G4 contracts below retain their original caps.
The W20 validated outcome below supersedes the W19 and historical status tables.
New leaves are at most 240 lines. Unimplemented signatures remain contracts.

Checked 2026-09-30 19:16 UTC by the following read-only API searches (paths
below are relative to `.lake/packages/mathlib/Mathlib`, unless prefixed FLT):

```
rg -n 'isLocalization|eval₂|induction_on' .lake/packages/mathlib/Mathlib/Algebra/Polynomial/Laurent.lean
rg -n 'instHopfAlgebra|antipode_T' .lake/packages/mathlib/Mathlib/RingTheory/HopfAlgebra/MonoidAlgebra.lean
rg -n 'comul_T|counit_T' .lake/packages/mathlib/Mathlib/RingTheory/Bialgebra/MonoidAlgebra.lean
rg -n 'instCommGrpObjSpecAsOverSpec|mul_spec_asOver_spec_left|Spec.mapMulEquiv' .lake/packages/mathlib/Mathlib/AlgebraicGeometry/Group/Affine.lean
rg -n 'of_isLocalization_Away|theorem comp' .lake/packages/mathlib/Mathlib/RingTheory/Smooth/Basic.lean
rg -n 'FinitaryExtensive|isVanKampen_finiteCoproducts' .lake/packages/mathlib/Mathlib/{AlgebraicGeometry/Limits,CategoryTheory/Extensive}.lean
rg -n 'smoothLocus|preimage_smoothLocus_eq' .lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean
rg -n 'coordinateUnit|affine|toLaurent_affine' FLT/Mazur/PolygonChartScaling.lean
```

Sources: [DR II.1.1, II.1.12(a–c)][dr], printed pp. 173, 178 / PDF pp. 31,
36, and [Conrad, Definition 2.1.4][conrad], pp. 5–6; see
[DR_SOURCE_LEDGER](DR_SOURCE_LEDGER.md) for the checked transcriptions.
The coordinate calculations below derive from multiplication on the punctured
projective line. They are not additional numbered assertions in DR.

## G1 — Laurent points are units, cap 250, implemented

New `FLT/Mazur/LaurentUnitPoints.lean`, namespace `FLT.Mazur.LaurentUnitPoints`.
For commutative rings `R,A` and `[Algebra R A]`, put `L := R[T;T⁻¹]`:

```lean
def evalUnit (a : Aˣ) : L →ₐ[R] A
def pointsEquiv : (L →ₐ[R] A) ≃ Aˣ
theorem pointsEquiv_symm_apply (a : Aˣ) : pointsEquiv.symm a = evalUnit a
theorem evalUnit_T (a : Aˣ) (m : ℤ) :
    evalUnit a (LaurentPolynomial.T m) = (a ^ m : Aˣ).val
theorem evalUnit_natural {B : Type*} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (a : Aˣ) :
    f.comp (evalUnit a) = evalUnit (Units.map f.toMonoidHom a)
```

Use `eval₂ (algebraMap R A) a`; commutation with constants makes it an
algebra map. Recover a unit from the images of `T 1` and `T (-1)`; prove
both inverse laws by `LaurentPolynomial.induction_on`. Include constants,
not just the two generators. Source: the functor of points of G_m underlying
DR II.1.12(a). Anchors: Laurent.lean:232,531,551,559. No geometry prerequisite.
Unblocks identification of the multiplication constructed in G2 with units.

## G2 — the smooth multiplicative group over a ring, cap 350, implemented

New `FLT/Mazur/MultiplicativeGroupScheme.lean`, namespace
`FLT.Mazur.MultiplicativeGroupScheme`; any commutative ring `R`:

```lean
abbrev gm : Over (Spec (CommRingCat.of R)) :=
  (Spec (CommRingCat.of R[T;T⁻¹])).asOver (Spec (CommRingCat.of R))
instance : CommGrpObj (gm R)
instance : Smooth (gm R).hom
theorem comul_coordinate :
    Coalgebra.comul (R := R) (LaurentPolynomial.T 1 : R[T;T⁻¹]) =
      LaurentPolynomial.T 1 ⊗ₜ[R] LaurentPolynomial.T 1
theorem counit_coordinate :
    Coalgebra.counit (R := R) (LaurentPolynomial.T 1 : R[T;T⁻¹]) = 1
```

Reuse the existing Laurent Hopf algebra and cocommutativity instances;
do not reconstruct the group axioms. Expose the inverse `T ↦ T⁻¹` and the
scheme multiplication via `mul_spec_asOver_spec_left`. Smoothness follows
from polynomial smoothness and localization away from `X`, over arbitrary R.
Sources: G_m in DR II.1.1/1.12(a); localization gives its explicit smooth chart.
Anchors: HopfAlgebra/MonoidAlgebra.lean:67–80, Bialgebra/MonoidAlgebra.lean:442–445,
Coalgebra/MonoidAlgebra.lean:71, Group/Affine.lean:229,260;
Laurent.lean:489; Smooth/Basic.lean:559,568. G1 is needed only for the later
points comparison, not for this construction. Unblocks G4.

## G3 — scaling with a variable unit parameter, cap 300, implemented

New `FLT/Mazur/PolygonUniversalScaling.lean`, namespace
`FLT.Mazur.PolygonUniversalScaling`; commutative `R`, `L := R[T;T⁻¹]`.
Define `u : Lˣ := PolygonChartScaling.coordinateUnit (1 : Rˣ)` and:

```lean
def scaleLeft : R[X] →+* L[X] :=
  (PolygonChartScaling.affine u).comp (Polynomial.mapRingHom LaurentPolynomial.C)
def scaleRight : R[X] →+* L[X] :=
  (PolygonChartScaling.affine u⁻¹).comp (Polynomial.mapRingHom LaurentPolynomial.C)
def specialize (a : Rˣ) : L[X] →+* R[X] :=
  Polynomial.mapRingHom (LaurentPolynomial.eval₂ (RingHom.id R) a)
theorem specialize_left (a : Rˣ) :
    (specialize a).comp scaleLeft = PolygonChartScaling.affine a
theorem specialize_right (a : Rˣ) :
    (specialize a).comp scaleRight = PolygonChartScaling.affine a⁻¹
def overlapScale : L →+* L[T;T⁻¹]
theorem overlap_left : Polynomial.toLaurent.comp scaleLeft =
    overlapScale.comp Polynomial.toLaurent
theorem overlap_right : LaurentPolynomial.invert.toRingHom.comp
    (Polynomial.toLaurent.comp scaleRight) = overlapScale.comp
      (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)
```

Here `overlapScale` sends coefficients through the two constant inclusions
and `T` to `C u * T`. The final inversion acts on the inner coordinate only;
it must not invert the parameter. Check both endpoint evaluations as well.
Source: multiplication in DR II.1.12(b), on the normalization charts.
Anchors: P1 `coordinateUnit`, `affine`, `toLaurent_affine`,
`invert_toLaurent_affine`; Laurent `eval₂`, `eval₂_C`, `eval₂_T`.
Dependencies: P1, polynomial coefficient maps. These are relative coordinate
maps, not yet a descended polygon action. Unblocks that later action split.

## G4 — the split group with n components, cap 400, implemented

New `FLT/Mazur/PolygonSplitGroup.lean`, namespace `FLT.Mazur.PolygonSplitGroup`.
For commutative `R`, `n : ℕ`, `[NeZero n]`, write `G := gm R`:

```lean
abbrev model : Over (Spec (CommRingCat.of R)) := ∐ fun _ : ZMod n ↦ G
instance : CommGrpObj (model R n)
instance : Smooth (model R n).hom
theorem component_mul (i j : ZMod n) :
    Limits.prod.map (Sigma.ι (fun _ : ZMod n ↦ G) i)
        (Sigma.ι (fun _ : ZMod n ↦ G) j) ≫ μ[model R n] =
      μ[G] ≫ Sigma.ι (fun _ : ZMod n ↦ G) (i + j)
```

Construct multiplication by distributing the finite coproducts over products,
then `Sigma.desc`; identity uses component 0 and inversion sends i to -i.
Prove the group laws on each product of component charts. Source: the smooth
part of the standard polygon in DR II.1.1 and its group law in II.1.12(a).
Anchors: Scheme's `FinitaryExtensive` instance (Limits.lean:443),
`FinitaryExtensive.isVanKampen_finiteCoproducts` (CategoryTheory/Extensive.lean),
`Sigma.desc`, `Sigma.hom_ext`, `Limits.prod.map`; smoothness is local on the
source. Product/coproduct comparison maps count toward this cap; if they
exceed it, split that comparison off before attempting the group laws.
This produces the candidate group over R, including n=1, without assuming
that any given polygon's smooth locus has already been identified with it.

## G5 — identify the polygon smooth locus, implemented

Checked 2026-10-03 against W14 base `8425864c`. The historical G5 blocker is
closed by E1–E5 in [MAZUR_G5_GEOMETRY_SPLIT](MAZUR_G5_GEOMETRY_SPLIT.md):

| Geometry | Modules under `FLT/Mazur/` |
| --- | --- |
| E1–E2 node localization and opens | `PolygonNodeLocalization`, `PolygonNodeBranches` |
| E3 exact smooth locus and finite presentation | `PolygonNodePresentation`, `NodeSmoothLocus` |
| E4 cyclic and one-gon atlases, pinching | `PolygonCyclicAtlas`, `PolygonCyclicCocone`, `OneGonNormalization`, `PolygonCyclicPushout`, `OneGonGlobalPushout`, `PolygonAtlas` |
| E5a comparison with the supplied cocone | `PolygonCoconeComparison` |
| E5b exact atlas smooth locus | `PolygonAtlasSmoothLocus` |
| E5c specified isomorphism and group | `PolygonSmoothLocus` |

The detailed E3/E4 auxiliary-module list and historical validation are in the G5
split. `polygon_lfp`, `smoothIso`, `component_smoothIso_inv`, `smoothGrpObj`, and
`smoothCommGrpObj` are implemented. The component label is `ZMod.finEquiv n i`,
not its inverse. This works for n=1 and n=2, in every characteristic.
The smooth group is not yet an action on the entire polygon.

## W14 re-audit and dispatch rules

Checked at 2026-10-03 using the local source at `8425864c`, not a claim about
GitHub main. Reproduce the inventory with:

```sh
rg -n 'polygon_lfp|smoothIso|smoothGrpObj|component_smoothIso_inv' FLT/Mazur/Polygon*.lean
rg -n 'normalization|IsProper|topologicalKrullDim|H1' FLT/Mazur/Polygon*.lean
rg -n 'quotKerEquivOfSurjective' .lake/packages/mathlib/Mathlib/LinearAlgebra/Isomorphisms.lean
rg -n '^axiom Mazur_statement' FLT/Assumptions/Mazur.lean
rg -n 'mazurTorsionExclusion|pow_add_pow_ne_pow' FLT/Assembly/ExistingInputs.lean FermatsLastTheorem.lean
```

Earlier G1–G4 caps are historical. **Every new leaf below has a hard cap of 240
lines, including imports, comments, helper declarations and proofs.** Sketches
with future names are design contracts, not compiled Lean. A blocked row cannot
be implemented by taking its conclusion as a hypothesis or record field.
Ready means its mathematical proof and required APIs are identified; it does
not mean a proof has compiled. The completed W14 dispatch order was U1, U2, H1, at most three
implementation leaves this wave. Commit this phase artifact before proofs.

### U1 — coefficient naturality of chart scaling, cap 160, implemented

New `PolygonScalingNaturality`; commutative rings R,S, `f : R →+* S`, `a : Rˣ`:

```lean
theorem affine_natural :
    (Polynomial.mapRingHom f).comp (PolygonChartScaling.affine a) =
      (PolygonChartScaling.affine (Units.map f a)).comp (Polynomial.mapRingHom f)
theorem laurent_one : PolygonChartScaling.laurent (1 : Rˣ) = RingHom.id _
theorem laurent_mul (a b : Rˣ) :
    PolygonChartScaling.laurent (a * b) =
      (PolygonChartScaling.laurent a).comp (PolygonChartScaling.laurent b)
```

Also construct Laurent coefficient mapping and prove its analogous naturality.
Use polynomial extensionality and Laurent `C`, `T 1`, `T (-1)` extensionality;
no division, field hypothesis, or assertion about geometric base change.
Dependencies: `PolygonChartScaling`, Laurent polynomial API. This is the
coefficient compatibility needed to use G3 over parameter rings. Source:
DR II.1.12(b)'s multiplication, written in the two normalization coordinates.

### U2 — reciprocal scaling of node functions, cap 240, implemented

New `PolygonNodeScaling`; `A := PolygonNodeEqualizer.A`. Construct:

```lean
def scaling (a : Rˣ) : A (R := R) →+* A (R := R)
def map (f : R →+* S) : A (R := R) →+* A (R := S)
theorem scaling_one : scaling (1 : Rˣ) = RingHom.id _
theorem scaling_mul (a b : Rˣ) : scaling (a * b) = (scaling a).comp (scaling b)
theorem map_scaling (f : R →+* S) (a : Rˣ) :
    (map f).comp (scaling a) = (scaling (Units.map f a)).comp (map f)
```

First branch scales by a, second by a inverse. Prove both restriction formulas,
origin preservation and Laurent-localization compatibility. Specializing a to
G3's universal unit gives the actual node ring map `A R →+* A R[T;T⁻¹]`.
This is not the unproved isomorphism `A R[T;T⁻¹] ≅ R[T;T⁻¹] ⊗[R] A R`.
Dependencies: U1, `PolygonNodeEqualizer`, `PolygonNodeLocalization`; membership
is equality of evaluations at zero. Source: DR II.1.1/1.12(b), local coordinate
calculation. No assertion that the one-gon's irreducible affine chart is a node
ring; it is not, and variable scaling need not preserve that chosen open.

### Whole-polygon action after U1/U2: blocked leaves

Each row proposes one new module, cap 240. Dependencies are mandatory; none is
ready for dispatch merely because G5 is done. The missing base-change proof
must work over parameter schemes, not just over extension fields.
`BC g` below means `Over.pullback g`; `P` is the specified polygon and `G` its
G4 split group. Tensor notation denotes products in the over-category.

| Leaf/module | Lean statement sketch | Dependencies and unresolved proof |
| --- | --- | --- |
| U3 `PolygonNodeScalarExtension` | `def nodeTensorIso : S ⊗[R] A R ≃ₐ[S] A S` | Identify the actual base-changed node; use the split exact sequence, not arbitrary preservation of ring pullbacks. Pin tensor conventions first. |
| U4 `ProjectiveLineProductCharts` | `def chartProductIso : Gm ×ₛ chart K ≅ Spec (.of K[T;T⁻¹][X])` | Polynomial/tensor comparison; prove both projection formulas and pulled-back open cover. |
| U5 `ProjectiveLineUniversalAction` | `def act : Gm ⊗ Over.mk (ProjectiveLine.toBase K) ⟶ Over.mk (ProjectiveLine.toBase K)` | U4 and G3; glue chart maps, with both endpoint formulas. |
| U6 `PolygonPinchingFlatBaseChange` | `theorem pinching_pullback : IsPushout (BC g |>.map toComponents) (BC g |>.map toNodes) (BC g |>.map p) (BC g |>.map q)` | Flat g, U3 and saturated-open descent; must prove locality for the one-gon too. Existing IsPushout alone does not imply this. |
| U7 `PolygonUniversalAction` | `def act : G ⊗ P ⟶ P` | U5/U6, G4 product/coproduct comparison, rotations; specify normalization and node formulas. |
| U8 `PolygonActionUnit` | `theorem unit_act : (η[G] ▷ P) ≫ act = (λ_ P).hom` | U7 and U6 for product descent; normalization/node restrictions jointly detect equality. |
| U9 `PolygonActionAssociativity` | `theorem mul_act : (μ[G] ▷ P) ≫ act = (α_ G G P).hom ≫ (G ◁ act) ≫ act` | U7/U6 with two parameter factors, U1/U2 multiplication, rotation commutation. |
| U10 `PolygonActionSmoothRestriction` | `theorem smooth_act : (e.hom ⊗ₘ ι) ≫ act = μ[Psm] ≫ ι` | Here e : Psm ≅ G is G5 smoothIso; compare on every pair of torus components. |
| U11 `PolygonActionBaseChange` | `theorem baseChange_action_laws : ActionLaws (baseChangedAct g)` | U8/U9 and actual pullback product comparisons; arbitrary scheme g after action exists. Define ActionLaws with the two equations, then prove it. |
| U12 `PolygonActionGraph` | `theorem component_act : component i ≫ translation a j = scaling a ≫ component (i+j)` | U7 and smooth restriction over extension fields; identify DR graph rotations, including n=1. |

U3–U6 caps are dispatch limits, not evidence that all helpers fit. Before each
is released, freeze its typed maps and source-local proof; if a generic descent
lemma needs more than 240 lines, split that proof first. U6 in particular remains
a source-design gate, not a ready theorem inferred from G5.

### H1 — incidence kernel and cokernel, cap 160, implemented

New `PolygonIncidenceQuotient`; field K, n>0:

```lean
def kernelEquiv : LinearMap.ker (PolygonIncidence.difference K hn) ≃ₗ[K] K
def cokernelEquiv :
    ((Fin n → K) ⧸ LinearMap.range (PolygonIncidence.difference K hn)) ≃ₗ[K] K
theorem cokernelEquiv_mk (v : Fin n → K) :
    cokernelEquiv K hn (Submodule.Quotient.mk v) = PolygonIncidence.total K n v
```

Also prove both finranks are one. Dependencies: P5's `ker_difference`,
`eq_initial_of_difference_eq_zero`, `range_difference`, `total_surjective`, and
`LinearMap.quotKerEquivOfSurjective`. This is linear algebra of the dual cycle
(DR II.1.1); it does not identify either space with sheaf cohomology. Include
n=1 and characteristic dividing n; never use averaging by n.

### Normalization, cohomology and genus: blocked leaves

Each proposed module has cap 240. Use actual structure-sheaf module objects,
not a definition of H¹ as the incidence cokernel. `ν` denotes the existing
normalization map; `i` the node map. Functor names in these sketches are
schematic until the typed sheaf pushforwards are fixed.

| Leaf/module | Lean statement sketch | Dependencies and unresolved proof |
| --- | --- | --- |
| H2 `PolygonNormalizationFinite` | `theorem normalization_finite : IsFinite ν` | Explicit node and one-gon coordinate maps; affine-local finite-module proofs. Surjectivity also required. |
| H3 `PolygonStructureInclusion` | `def inclusion : O_P ⟶ pushforward ν O_components` | H2, actual module sheaf pushforward/scalars and local normalization maps. |
| H4 `PolygonBranchDifferenceSheaf` | `def difference : pushforward ν O_components ⟶ pushforward i O_nodes` | H3, endpoint evaluations, fix orientation to match P5. |
| H5 `PolygonNormalizationExact` | `theorem exact : (ShortComplex.mk inclusion difference zero).ShortExact` | H3/H4, node equalizer and one-gon localizations, stalkwise exactness. Local ring exactness alone is insufficient. |
| H6 `ProjectiveLineStandardComparison` | `def standardIso : ProjectiveLine.scheme K ≅ ProjectiveSpace K (Fin 2)` | Compare the existing glued P¹ to the projective model; preserve charts and constants. |
| H7 `ProjectiveLineStructureCohomology` | `def h0Equiv : H0 toBase ≃ₗ[K] K; theorem h1_zero : Subsingleton (H1 toBase)` | H6; reuse projective twist degree-zero/cohomology or affine Čech comparison, and scalar compatibility. |
| H8 `PolygonNormalizationCohomology` | `def h0Normalization : H0 (ν_* O_components) ≃ₗ[K] (Fin n → K)` | H2/H7, finite coproducts and affine direct-image comparison; also prove H¹ vanishes. |
| H9 `PolygonNodeCohomology` | `def h0Nodes : H0 (i_* O_nodes) ≃ₗ[K] (Fin n → K)` | Finite closed nodes and affine vanishing; prove evaluation identifications. |
| H10 `PolygonCohomologyIncidence` | `def h1Incidence : H1 P.hom ≃ₗ[K] ((Fin n → K) ⧸ LinearMap.range (difference K hn))` | H5/H8/H9 and long exact sequence; identify its H⁰ map with P5, not merely an abstract dimension count. |
| H11 `PolygonConstantSections` | `theorem constants : HasConstantGlobalSections P.hom` | H5/H8/H9, H1 kernel equivalence and scalar-map compatibility. |
| H12 `PolygonProper` | `theorem proper : IsProper P.hom` | H2 finite surjective normalization, H6 proper P¹; prove finite type/separatedness and proper descent hypotheses. |
| H13 `PolygonDimension` | `theorem dimension : topologicalKrullDim P.left = 1` | Node/one-gon charts, nonempty torus, dimension bounds; G5 lfp is insufficient. |
| H14 `PolygonGenusOne` | `theorem genus_one : curveGenus P.hom dimension constants = 1` | H10/H11/H12/H13 and H1. Transport to specified cocones via polygonIso. |
| H15 `PolygonGeometricGenus` | `theorem geometric_genus : NodalGenusOneGeometricFibers P.hom` | H14, geometric base-change identification of the polygon; do not assume scalar H¹ base change. |

Existing `ModuleCohomologyExact`, `AffinePushforwardCohomology`,
`CechAcyclicComparison`, `ProjectiveTwistCohomology`, `ProperCurveGenus` and
`ScalarCohomology` provide foundations, not these comparison maps. H2–H9 each
need a typed API/source check before release. They may require further ≤240-line
helpers; neither this table nor G5 certifies a bounded complete genus proof.

## Beyond polygon G1: gates to the actual FLT consumer

Even U1–U12 and H1–H15 do not construct an algebraic modular curve. The selected
route and source references remain [MAZUR_CONTRACTS](MAZUR_CONTRACTS.md) and
[MAZUR_PLAN](MAZUR_PLAN.md): DR II.1.4/1.12, IV, VI §5, VII §2; Mazur II §1,
II §§6–10, II (14.1), III §§3–5 and I (2.9). No new source theorem is claimed
verified beyond those ledgers. Remaining packages are **not dispatchable leaves**:

1. Generalized elliptic families (proper, flat, finitely presented; smooth or
   polygon fibers; group/action/graph conditions), level divisors and ampleness.
2. Moduli atlas/groupoid, degeneration and contraction, coarse quotient and
   geometric-point property, proper smooth prime-level curve away from p,
   disjoint cusp sections and their Néron-model specialization orientation.
3. Picard/Jacobian representability, Hecke correspondences, Eisenstein quotient,
   integral abelian model, finite rational quotient and nonzero cuspidal image.
4. A1 local semistability and components; A2 odd torsion specialization and the
   global bad-prime argument; A3 cyclotomic extension/unramifiedness; A4 the
   Herbrand weight-two input; A5 isogeny iteration with finite rational-generator
   fibers and no backtracking. None follows just from polygon geometry.

The older contracts have 250–500-line applications and large foundation
families. They are not silently relabeled ≤240 here. Before dispatch, subdivide
one source proof at a time into ≤240-line modules with typed statements; without
that subdivision these packages remain source-design blockers. Claiming a
complete finite list of ready ≤240-line leaves for all of Mazur would be false.
The independent scalar-cohomology extension comparison is also still a separate
foundation gate, not supplied by the existing geometric-fiber predicate.

After these gates, the final small leaves are:

| Leaf | Sketch | Cap / dependencies |
| --- | --- | --- |
| T1 `PrimeTorsionConclusion` | `theorem noLargePrimeTorsion : NoLargePrimeTorsion` | 150; actual G1/G2/A1–A5 proofs, currently blocked |
| T2 assembly rewire | `mazurTorsionExclusion_of_noLargePrimeTorsion noLargePrimeTorsion` | 80; T1, later permission to edit existing Lean modules |
| T3 final audit | `#print axioms PNat.pow_add_pow_ne_pow` | 80-line audit; rebuilt final consumer after T2 |

T2 must replace the `ExistingInputs` use of `mazur_W`; proving a disconnected
replacement theorem does not change the final declaration's dependencies.
W14's new-module-only rule prohibits that edit in this wave. It is unnecessary
to prove the full cardinal-bound axiom if the sufficient prime-torsion input is
proved and the consumer rewired. Other `sorryAx` inputs have independent queues.

## W14 implementation evidence

Checked 2026-10-03 01:40 UTC. The phase split was committed as `dc83a262`
before implementation. No further implementation leaf is released by this wave;
U3/U4/H2/H6 require the typed API checks recorded above.

| Leaf | Module | Lines/cap | Commit | Audited declarations |
| --- | --- | --- | --- | --- |
| U1 | `PolygonScalingNaturality` | 105/160 | `3b763ba8` | 13 |
| U2 | `PolygonNodeScaling` | 139/240 | `005eeca7` | 33 |
| H1 | `PolygonIncidenceQuotient` | 75/160 | `d8a4622f` | 18 |

All three passed their foreground build and individual lint commands below.
The combined `collectAxioms` audit checked 64 declarations, including generated
helpers: only `propext`, `Classical.choice`, `Quot.sound`. The incidence theorem
is not a polygon genus theorem. `universal` targets the node over the Laurent
ring, without asserting the still-missing tensor/base-change comparison.

Reproduce the axiom check by saving this block outside the library and running
`LEAN_NUM_THREADS=2 lake env lean PATH` (after the three module builds):

```lean
import FLT.Mazur.PolygonNodeScaling
import FLT.Mazur.PolygonIncidenceQuotient
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`FLT.Mazur.PolygonScalingNaturality,
    `FLT.Mazur.PolygonNodeScaling, `FLT.Mazur.PolygonIncidenceQuotient]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for mod in modules do
    let some idx := env.getModuleIdx? mod | throwError "Missing module {mod}"
    let mut count := 0
    for (name, _) in env.constants.toList do
      if env.getModuleIdxFor? name == some idx then
        let axioms ← collectAxioms name
        unless axioms.all allowed.contains do
          throwError "Disallowed axioms for {name}: {axioms}"
        count := count + 1
    if count == 0 then throwError "No declarations checked for {mod}"
    logInfo m!"CHECKED {mod}: {count} declarations"
```

## Validation for implementation leaves

Foreground `LEAN_NUM_THREADS=2 lake build MODULE`, then
`LEAN_NUM_THREADS=2 lake exe runLinter MODULE`, one module at a time. Audit every
new declaration using `collectAxioms`: only propext, Classical.choice, Quot.sound.
No sorry, new axiom, native_decide, or conclusion-assuming record. Only new Lean
modules and sorted FLT.lean imports; docs may change. Commit locally, never push.

[dr]: https://www.math.uni-bonn.de/people/rapoport/myalggeom/preprints/Lesschemas.pdf
[conrad]: https://math.stanford.edu/~conrad/papers/kmpaper.pdf

## W15 typed-contract check and dispatch

Checked 2026-10-03 on W15 base `31114b5c`. The untracked
`W15_CONTRACT.lean` compiles with `LEAN_NUM_THREADS=2 lake env lean`.
For arbitrary commutative rings R,S and `[Algebra R S]`, coefficient mapping
is an R-algebra homomorphism `A R →ₐ[R] A S`, using the existing scalar tower
on the subalgebra. `AlgHom.liftEquiv R S _ _` gives the comparison
`S ⊗[R] A R →ₐ[S] A S` with pure-tensor formula `s ⊗ p ↦ s • map p`.
Thus the proposed U3 isomorphism has a checked source, target and scalar
convention; no flatness assumption is needed.

U3 is released with cap 240. Its inverse is the linear reconstruction
`p ↦ aeval (1 ⊗ x) p.first + aeval (1 ⊗ y) p.second - C (p.first.eval 0)`.
The equality of endpoint values proves reconstruction on A(S); tensor
induction and coefficient naturality prove the other composite is identity.
This is an explicit split-module argument, not an assertion that tensoring
preserves arbitrary ring pullbacks. Both branch restriction formulas are
required as part of the delivered comparison.

For U4 the identified APIs are `polyEquivTensor'` in
`Mathlib/RingTheory/PolynomialAlgebra.lean` and `pullbackSpecIso` with its
projection lemmas in `Mathlib/AlgebraicGeometry/Pullbacks.lean`. The geometric
product charts and their pulled-back cover still require typechecking.
H2/H6 and U5/U6 remain subject to the source/API gates above; if their helper
proofs do not fit 240 lines, record the split before implementing the helpers.

U4's complete typed prototype now checks (`W15_PRODUCT_PROOF.lean`). Its
`chartProductIso K S` identifies the pullback of `Spec S → Spec K` and the
affine-line chart with `Spec S[X]`, for arbitrary commutative K-algebras S.
Both inverse/projection formulas are the spectra of the constant inclusion
and polynomial coefficient map. The Bool-indexed cover is the actual
`Scheme.Pullback.openCoverOfRight`, transported through these isomorphisms.
Taking S = K[T;T⁻¹] gives the required multiplicative-group product chart.
The final module remains capped at 240.

H2 is split before implementation, since local finite-module calculations
alone do not identify the inverse images in the constructed global polygon:

| Leaf | New module / typed contract | Cap | Proof obligation |
| --- | --- | --- | --- |
| H2a | `PolygonNormalizationAlgebra`: `Module.Finite (A R) (R[X] × R[X])`, `Module.Finite (B R) R[X]` | 180 | Generate the first module by 1 and (1,0); generate the second algebra by integral X, satisfying X²-X-u. Prove both spectrum maps surjective. |
| H2b | `PolygonCyclicNormalizationPullback` | 240 | Identify inverse images of every node chart with the disjoint union of its two affine branches, including n=2's two overlaps. |
| H2c | `OneGonNormalizationPullback` | 240 | Prove the square formed by `OneGonAffineNormalization.alpha`, the affine normalization map and `OneGonGluing.node` is cartesian; also the torus square. |
| H2d | `PolygonNormalizationFinite` | 160 | Apply target-local finiteness to H2b/H2c and H2a; prove global surjectivity and transport to the specified cocone. |

H6's target in the earlier sketch is schematic: the actual type is
`ProjectiveSpace.space K (Fin 2)`, not a declaration named `ProjectiveSpace`.
Its proof must compare the two explicit open immersions and their Laurent
transition; no standard-model isomorphism is supplied by the current files.
The available chart APIs are `chartPolynomialEquiv`, `affineChartAt`,
`reindexChartRingMap_coordinate` and `overlap_isLocalization`. Separate the
polynomial-chart/transition comparison (H6a, cap 240) from the open-cover
pushout isomorphism and scalar compatibility (H6b, cap 180) before dispatch.
The cartesian transition comparison remains a proof obligation, not a field
in a new chart record.

H2a is implemented in 108 lines. H2c's complete prototype also typechecks:
`IsPullback (oneBranch K) (alpha K) (OneGonGluing.node K) (normalization K)`
and `IsPullback (𝟙 _) (overlapLeft K ≫ left K) (OneGonGluing.torus K)
(normalization K)`. The proof computes both inverse-image opens using the
existing gluing intersection and the conductor; it includes coordinate one
in the torus chart. Split H2d into H2d1 `OneGonNormalizationFinite` (cap 120,
now released from H2a/H2c) and H2d2 `PolygonNormalizationFinite` (cap 160,
still dependent on the cyclic inverse-image comparison H2b).

H6a is further split before library implementation: H6a1
`ProjectiveLineStandardCharts` (cap 200) constructs the two polynomial chart
isomorphisms in `ProjectiveSpace.space K (Fin 2)`, their scalar maps and cover.
H6a2 `ProjectiveLineStandardOverlap` (cap 240) identifies their intersection
with the existing Laurent chart and proves the reciprocal-coordinate
transition. H6b `ProjectiveLineStandardComparison` (cap 180) compares the
resulting open-cover pushout with `ProjectiveLine.scheme K`, preserving both
charts and the base map. The chart maps use `chartRing_hom_ext`, the checked
`chartPolynomialEquiv`, and explicit swapping of the two homogeneous indices.

For H2b, split the cyclic proof further: H2b1
`PolygonCyclicNormalizationRanges` (cap 200) proves that a point of component
`i` mapping into node chart `j` lies either in its left chart with `i=j`, or
in its right chart with `i=finRotate n j`. The proof uses `charts_eq_iff` and
rules out a full branch meeting the opposite punctured branch; it does not
discard the second edge when n=2. H2b2 `PolygonCyclicNormalizationPullback`
(cap 240) packages these ranges as the open immersion of the two affine
branches into the normalization coproduct and proves the cartesian square.
H2d2 then descends their finite maps on the target chart cover and transports
through `sigmaComparison (Over.forget _)` to the specified normalization.

H2d2 is split before coding: `PolygonCyclicNormalizationFinite` (cap 160)
proves finite surjective normalization on the plain scheme coproduct, then
transports it to the existing over-category normalization through the
canonical coproduct comparison. `PolygonNormalizationFinite` (cap 160)
combines that result with the one-gon result (including its one-component
coproduct comparison), then transports finite surjectivity to any supplied
pinching cocone using the existing `polygonIso`. Neither transport introduces
an assumed finiteness field.

U5 is split before library implementation. U5a `ProjectiveLineProductOverlap`
(cap 220) identifies `Spec S[T;T⁻¹]` as the cartesian intersection of U4's
polynomial product charts, for arbitrary commutative K-algebras S. The proof
uses the basic open of X and the original gluing intersection, then applies
`BinaryOpenDescent.isPushout`. U5b `ProjectiveLineUniversalAction` (cap 240)
glues G3's two ring maps on that pushout for S=K[T;T⁻¹], proves the base-map
identity and both endpoint formulas, and packages the result in `Over (Spec K)`.
U6 remains a separate source-design gate: an open-cover pushout argument does
not establish base-change preservation of the closed pinching diagram.

## W15 implementation evidence and remaining descent gap

Checked 2026-10-03 02:58 UTC at implementation head `07a99bd9`, relative to
base `31114b5c`. These results supersede U3/U4/U5/H2/H6's earlier blocked status.
All module names below have prefix `FLT.Mazur.`.

| Leaf | Module | Lines/cap | Commit | Audited declarations |
| --- | --- | --- | --- | --- |
| U3 | `PolygonNodeScalarExtension` | 141/240 | `7b3c5137` | 29 |
| U4 | `ProjectiveLineProductCharts` | 135/240 | `8c393cef` | 33 |
| H2a | `PolygonNormalizationAlgebra` | 108/180 | `199a6694` | 11 |
| H2c | `OneGonNormalizationPullback` | 99/240 | `5c3a05e3` | 6 |
| H2d1 | `OneGonNormalizationFinite` | 60/120 | `eaf57a64` | 4 |
| H6a1 | `ProjectiveLineStandardCharts` | 165/200 | `41040c8e` | 39 |
| H6a2 | `ProjectiveLineStandardOverlap` | 141/240 | `8bb365f7` | 19 |
| H6b | `ProjectiveLineStandardComparison` | 64/180 | `097ab2ac` | 15 |
| H2b1 | `PolygonCyclicNormalizationRanges` | 96/200 | `6e6d025e` | 7 |
| H2b2 | `PolygonCyclicNormalizationPullback` | 139/240 | `a9413d27` | 25 |
| H2d2a | `PolygonCyclicNormalizationFinite` | 104/160 | `412da268` | 14 |
| H2d2b | `PolygonNormalizationFinite` | 89/160 | `27a7f6f8` | 8 |
| U5a | `ProjectiveLineProductOverlap` | 143/220 | `0e06745c` | 19 |
| U5b | `ProjectiveLineUniversalAction` | 161/240 | `07a99bd9` | 32 |

Each module passed `LEAN_NUM_THREADS=2 lake build MODULE` and
`LEAN_NUM_THREADS=2 lake exe runLinter MODULE` sequentially in the foreground.
The combined audit imports these 14 modules and uses the origin-module loop
shown in W14's recipe, with these 14 names in `modules`. All 261 declarations,
including generated helpers, use only `propext`, `Classical.choice`, `Quot.sound`.
Local evidence: `GOAL_MAZUR_W15_AXIOM_AUDIT.lean` and
`GOAL_MAZUR_W15_ALL_AXIOMS.txt` (untracked, outside the library).

Read-only checks: `git diff --check 31114b5c..HEAD` passed; the new-module line
counts meet every declared cap; source scans found no `sorry`, `admit`, `axiom`
or `native_decide`. `FLT.lean` imports are sorted and match all library paths.
The diff contains new Lean modules, imports and authorized docs only. No
whole-library build or lint ran, and nothing was pushed.

H2 proves finite surjective normalization for every positive polygon, including
the one-gon, and for any supplied cocone with the specified pinching pushout.
H6 identifies the glued line with `ProjectiveSpace.space K (Fin 2)`, preserving
charts, endpoints and the base map. U5 constructs
`MultiplicativeGroupScheme.gm K ⊗ Over.mk (ProjectiveLine.toBase K) ⟶
Over.mk (ProjectiveLine.toBase K)` with both affine formulas and fixed endpoint
sections. U5 does not yet descend this morphism to the polygon.

### U6: checked statement, unproved base-change descent

`W15_U6_CONTRACT.lean` checks the target below for `g : S ⟶ Spec (.of K)`,
`[Flat g]`, positive n, and a supplied cocone p,q. It checks a proposition's
type; it contains no proof of that proposition.

```lean
IsPushout
  ((Over.pullback g).map (PolygonPinching.toComponents K n hn))
  ((Over.pullback g).map (PolygonPinching.toNodes K n))
  ((Over.pullback g).map p) ((Over.pullback g).map q)
```

The missing implication is from the original pinching pushout to this one.
The current arbitrary-target proofs in `NodePinchingDescent` and
`OneGonPinchingDescent` require `[Field K]`. Their neighborhood construction
in `PinchingNeighborhoods.normalizedAt_eval` divides by a nonzero endpoint
value. Over K[T;T⁻¹], a nonzero value such as T−1 need not be invertible.
Replacing K by the parameter ring therefore does not instantiate those proofs.
The type checks and API evidence are in `GOAL_MAZUR_W15_U6_CONTRACT.txt`.

U3 supplies the node scalar-extension isomorphism. The one-gon equalizer
`B R = {p : R[X] | p.eval 0 = p.eval 1}` still needs its own scalar-extension
comparison. After that, arbitrary-target descent must be proved locally over
the parameter base, then transported through the global pinching atlas.
The one-gon's chosen affine open need not be preserved by universal scaling;
its node chart cannot be treated as the split node algebra A.

A further source/API check found only flat-surjective descent in mathlib's
`AlgebraicGeometry/EffectiveEpi.lean`; it requires flatness of the descending
morphism. H2's finite normalization does not supply that hypothesis. The
open-cover pushout in U5 is a different diagram and does not prove U6.

The next proof split is proposed, not released as completed or bounded code:

| Proposed leaf | Required result | Initial cap |
| --- | --- | --- |
| U6a | One-gon `S ⊗[R] B R ≃ₐ[S] B S`, with normalization and endpoint formulas | 220 |
| U6b | Saturated principal neighborhoods after localizing the parameter base, for both pinching charts | 240 |
| U6c1 / U6c2 | Arbitrary-target affine pinching descent over parameter rings, separately for the node and one-gon | 240 each |
| U6d | Identify pulled-back atlas diagrams and glue the global pinching pushout, including n=1 | 240 |

Each requires a checked proof design and further splitting if its helpers
exceed the cap. U7–U12 remain dependent on U6; no polygon action or action-law
theorem is delivered in W15. H3–H5 and H7–H15, full G1 moduli, G2 arithmetic
and A1–A5 remain unproved as described above.

The final dependency is unchanged: read-only `rg -n '^axiom Mazur_statement'
FLT/Assumptions/Mazur.lean` returns line 103; `ExistingInputs.lean:28` uses
`mazur_W`, and `FermatsLastTheorem.lean:24` uses `mazurTorsionExclusion`.
This is source evidence, not a new axiom audit of the final FLT theorem.

## W16 checked scalar-extension design

Checked 2026-10-03 with `LEAN_NUM_THREADS=2 lake env lean
W16_ONEGON_PROOF.lean` (exit 0). U6a is released with cap 220:
`OneGonScalarExtension` constructs the coefficient comparison and proves it
bijective using the linear retraction
`p ↦ p - C (p.eval 1 - p.eval 0) * X` onto B. This retraction commutes with
coefficient extension. Tensoring it splits the normalization inclusion;
`polyEquivTensor` supplies the polynomial comparison. Tensor induction proves
the two compatibility squares, giving injectivity and surjectivity without
flatness. The normalization square and endpoint formulas are part of the leaf.
The checked prototype contains the proofs, not just theorem statements.

U6b will use neighborhoods at arbitrary primes of the parameter ring.
For branch polynomials p,q, multiply by the opposite endpoint value instead
of dividing: the two node branches then have common value p(0)q(0).
For the one-gon use `(1-X) C(q(1)) p + X C(p(0)) q`, whose endpoint values
are p(0)q(1). These common values avoid the chosen base prime, but need not
be units. Localized equalizers must consequently evaluate into the base
localized at that common value. This is a proof design awaiting compilation;
no size or completion claim for U6b–U12 is made here.

U6b is split before library implementation. Two complete prototypes passed
`lake env lean`: `W16_NEIGHBORHOODS_PROOF.lean` and
`W16_EQUALIZER_PROOF.lean`. Release U6b1 `RelativePinchingNeighborhoods`
(cap 120) for the arbitrary-prime neighborhoods above. Release U6b2
`RingEqualizerLocalization` (cap 150) for any two ring maps f,g and an element
s of their equalizer: the equalizer of the localized maps to D[1/f(s)] is
C[1/s]'s subring canonically isomorphic to (eqLocus f g)[1/s]. Equality of
localized endpoint values only implies equality after multiplication by
f(s)^k; the proof multiplies the numerator by s^k and increases its denominator
exponent. It handles zero divisors and arbitrary commutative rings.
Specializing to the node and one-gon, and constructing/gluing scheme morphisms,
remain separate leaves. These two results alone do not establish U6c or U6d.

U6c is split further before implementation. The complete
`W16_LOCAL_DESCENT_PROOF.lean` prototype compiles. Release U6c0
`RingEqualizerLocalDescent` (cap 180): the localized equalizer spectrum has
unique descent to an affine target; for arbitrary targets it descends on any
saturated principal neighborhood mapping into an affine target open. Both
endpoint/base-localization formulas and the cartesian normalization square
are proved. U6c1/U6c2 must still construct covering families of these local
descents and prove their compatibility and global uniqueness.

`W16_RELATIVE_LOCAL_PROOF.lean` now compiles in full. Release U6c3
`RelativePinchingLocalDescent` (cap 140), specializing U6c0 to B and to the
product normalization of A. At every base prime it constructs an actual
morphism on a saturated open containing that node. The node proof uses the
prime-spectrum decomposition of a product to put both normalization branches
inside the chosen target affine open. All coefficient rings are commutative
rings, with no field or nonzero-is-unit assumption. This is local existence,
not global arbitrary-target descent or preservation of the pinching pushout.

Three further helper proofs are checked before release. U6c4
`SurjectiveDominantEpi` (cap 100) proves that a quasi-compact, surjective,
scheme-theoretically dominant morphism is an epimorphism, by injectivity on
sections; it also derives schematic dominance of Spec of an injective ring
map. Prototypes `W16_EPI_PROOF.lean` and `W16_SCHEMATIC_PROOF.lean` compile.
U6c5 `RingEqualizerAwayEndpoint` (cap 70) proves the localized normalization
is an isomorphism if the common endpoint value is zero: the localized endpoint
ring is the zero ring, so the localized equalizer is the entire normalization.
`W16_AWAY_ENDPOINT_PROOF.lean` compiles. This provides local descent away from
the endpoint image without invoking a field-only smooth-locus calculation.
Global gluing and the pulled-back polygon atlas remain separate obligations.

U6c6 `SchematicDescentGluing` is released with cap 90 after the complete
`W16_GLUE_PROOF.lean` compiled. Local descents on a supplied open cover glue
uniquely for a quasi-compact surjective schematically dominant normalization:
overlap projections are epimorphisms by U6c4, since open immersions are flat
and schematic dominance is stable under flat base change. This uses flatness
of the open immersion, not the false assertion that normalization is flat.

U6c7 `RingEqualizerDescent` is released with cap 110 after the complete
`W16_DESCENT_PROOF.lean` compiles. For a finite normalization of a ring equalizer
whose common endpoint map is surjective, local descents at all base primes
extend uniquely to the entire equalizer spectrum. A prime containing the
endpoint kernel lies in the endpoint image; every other prime avoids a kernel
element, so U6c5 applies. The proof constructs the full open cover and uses
U6c6; it does not assume a global descent in a record or hypothesis. The
pinching-chart specializations still need their own checked proof.

U6c1/U6c2 are now released together as `RelativePinchingDescent` (cap 160).
The complete `W16_GLOBAL_PINCHING_PROOF.lean` compiles: `oneGon_desc` and
`node_desc` prove existence and uniqueness for arbitrary target schemes over
any commutative coefficient ring. The intermediate `node_product_desc` works
on Spec of the normalization product, and the two-branch statement follows
via `coprodSpec`. The finite normalization instances and surjective endpoint
maps are proved for the actual A and B, not supplied as new structure fields.

U6d must be split before constructing the global base-changed pushout.
The complete `W16_CHART_BASECHANGE_PROOF.lean` compiles. Release U6d1
`PinchingChartBaseChange` (cap 130): identify the actual scheme pullbacks of
Spec A(R) and Spec B(R) along Spec S → Spec R with Spec A(S) and Spec B(S),
with both projection formulas. This works without flatness. Transporting the
global normalization squares, node sections and whole pinching span through
these comparisons remains required; a chart isomorphism alone is not U6.

U6d2 `PolygonProductAtlas` is released with cap 200 after the full
`W16_PRODUCT_ATLAS_PROOF.lean` compiles. It constructs actual open covers of
the affine-parameter pullbacks, for every positive n. For n ≥ 2 the charts
are Spec A(S); for n=1 they are Spec B(S) and Spec (S ⊗[K] K[T;T⁻¹]). Both
projections are computed. The one-gon torus is deliberately retained in its
canonical tensor coordinates. `pullbackCover` also gives the actual pulled-back
cover for arbitrary scheme bases. These are covers of the specified polygon,
not a replacement polygon defined by assuming its pinching property.
The normalization comparison and endpoint compatibility on these covers are
still needed to apply `RelativePinchingDescent` to the global cocone.

## W16 implementation evidence and remaining global comparison

Checked 2026-10-03 03:54 UTC, implementation head `93c1fbf9`, base `0b2d8d7b`.

| Item | Module under `FLT/Mazur/` | Lines/cap | Commit |
| --- | --- | --- | --- |
| U6a | `OneGonScalarExtension` | 129/220 | `e87e6616` |
| U6b1 | `RelativePinchingNeighborhoods` | 74/120 | `10712d7a` |
| U6b2 | `RingEqualizerLocalization` | 85/150 | `27b657dc` |
| U6c0 | `RingEqualizerLocalDescent` | 134/180 | `152da214` |
| U6c3 | `RelativePinchingLocalDescent` | 93/140 | `646eeb2a` |
| U6c4 | `SurjectiveDominantEpi` | 54/100 | `fe05e3cf` |
| U6c5 | `RingEqualizerAwayEndpoint` | 41/70 | `fe05e3cf` |
| U6c6 | `SchematicDescentGluing` | 49/90 | `30fcabbb` |
| U6c7 | `RingEqualizerDescent` | 74/110 | `b723c15c` |
| U6c1/U6c2 | `RelativePinchingDescent` | 90/160 | `626a135f` |
| U6d1 | `PinchingChartBaseChange` | 92/130 | `6790bcc0` |
| U6d2 | `PolygonProductAtlas` | 181/200 | `93c1fbf9` |

All 12 modules passed their individual foreground commands:

```
LEAN_NUM_THREADS=2 lake build FLT.Mazur.MODULE
LEAN_NUM_THREADS=2 lake exe runLinter FLT.Mazur.MODULE
```

`LEAN_NUM_THREADS=2 lake env lean GOAL_MAZUR_W16_AXIOM_AUDIT.lean`
checked all 191 declarations originating in these modules, including generated
helpers. `GOAL_MAZUR_W16_ALL_AXIOMS.txt` records only `propext`,
`Classical.choice`, `Quot.sound`. No whole-library build or lint was run.
All final module builds are warning-free. No proof placeholders, new axioms,
or native_decide occur in the new code; comments are excluded from that scan.
`GOAL_MAZUR_W16_VALIDATION.txt` records the caps, audit counts and complete
sorted import inventory. `git diff --check 0b2d8d7b..HEAD` passes.
Only new Lean modules, sorted `FLT.lean` imports and the authorized split doc
are changed. All commits use krandder's requested name/email, with no AI credit.
Nothing was pushed. Scratch proofs, audit logs and handoffs remain outside
`FLT/` and `docs/`, untracked or ignored.

The remaining U6 gap is the **global pinching pushout after base change**.
The field-only affine-descent obstruction is closed; it is not the remaining
blocker. The new covers alone do not prove preservation of the closed pinching
pushout. This is unfinished mathematical formalization, not an approval or
infrastructure blocker.

`W16_U6_REMAINING_CONTRACT.lean` compiles without placeholders. Its output
`GOAL_MAZUR_W16_U6_CONTRACT.txt` records a precise next one-gon comparison:

```lean
IsPullback
  (Spec.map (CommRingCat.ofHom (PolygonNodePresentation.B (R := S)).val.toRingHom))
  (affineNormalizationLift K S)
  (PolygonProductAtlas.oneGonChartMap K S false)
  (normalizationProduct K S)
```

The scratch definitions are actual pullback maps; `alpha_toBase` is proved and
axiom-audited. The displayed IsPullback is only a checked proposition, not a
proved theorem. The final arbitrary-scheme `Over.pullback g` IsPushout contract
from W15 is also checked, not proved.

Next proof obligations, to split and typecheck before assigning caps:

1. Prove that cartesian one-gon normalization square in the new coordinates,
   and the analogous cyclic two-branch square. Transport the H2 normalization
   squares through U6d1's ring isomorphisms and the actual coproduct comparisons.
2. Transport the global input cocone's endpoint relation to the relative
   affine normalization charts. In particular, identify the one-gon alpha
   chart's zero/one sections with the pulled-back zero/infinity sections;
   do not treat this chart as invariant under universal scaling.
3. Apply `RelativePinchingDescent` chartwise, glue with the actual product cover,
   and prove the base-morphism identity plus both pinching cocone factorization
   equations and uniqueness. Descend locally on a general base scheme and
   transport from the specified polygon to an arbitrary supplied cocone.
4. Only then construct U7's whole-polygon action and prove U8–U12: unit,
   associativity, smooth restriction, base change and graph rotation.

U6's pushout, U7–U12, H3–H5/H7–H15, full G1 moduli, G2 arithmetic and A1–A5
remain unproved. No whole-polygon action, genus theorem or Mazur removal is
claimed. Source checks still return `axiom Mazur_statement` at
`FLT/Assumptions/Mazur.lean:103`, `mazur_W` at
`FLT/Assembly/ExistingInputs.lean:28`, and `mazurTorsionExclusion` at
`FermatsLastTheorem.lean:24`. This is source evidence, not a new compiled audit
of `PNat.pow_add_pow_ne_pow`. The final existing-consumer rewire is also outside
this wave's new-module-only authorization.

## W17 checked normalization comparison

The full `W17_ONEGON_PROOF.lean` prototype passed foreground `lake env lean`
on 2026-10-03 before release. U6d3 `OneGonProductNormalization` has cap 160:
use the polynomial and equalizer base-change isomorphisms to prove the coefficient
normalization square cartesian by pullback cancellation, paste the original
one-gon normalization square, then cancel the global normalization base-change
square. Both projections and the cocone equation are proved. This establishes
the precise W16 remaining normalization contract over arbitrary parameter rings.
Endpoint compatibility, the cyclic analogue and global pushout remain separate.

`W17_ENDPOINTS_PROOF.lean` also compiles in full before release. U6d4
`OneGonProductEndpoints` has cap 130: compute both pullback projections of
zero/one in the affine normalization, identify the actual constant endpoint
sections, prove their normalization images equal the node section, and apply
`RelativePinchingDescent.oneGon_desc`. This proves local descent from a global
normalization map satisfying the endpoint relation, not the global pushout.

`W17_NODE_COORDINATES_PROOF.lean` compiles before release. U6d5
`NodeNormalizationBaseChange` has cap 140: tensoring the product of polynomial
rings gives the product over the new base; both scheme pullback projections
are computed. Pullback cancellation against the node chart base-change square
proves the coefficient normalization square cartesian. The global cyclic
normalization comparison will be a separate leaf.

The full `W17_CYCLIC_PROOF.lean` prototype compiles. U6d6
`CyclicProductNormalization` has cap 180: transport the existing normalization
square through `coprodSpec`, then paste U6d5's coefficient square and cancel the
normalization base-change square. This proves the actual cartesian comparison
for each cyclic node chart, with both projections and the normalization equation.
Endpoint transport and global descent remain separate obligations.

`W17_CYCLIC_ENDPOINTS_PROOF.lean` compiles before release. U6d7
`CyclicProductEndpoints` has cap 150: the origins of the product-polynomial
branches are the pulled-back zero and adjacent infinity sections, checked by
both projections and `coprodSpec`. The input endpoint equality supplies the
hypothesis of `RelativePinchingDescent.node_product_desc`. Global gluing and
transport from the specified pinching cocone are still required.

`W17_DOMINANCE_PROOF.lean` compiles before release. U6d8
`PolygonNormalizationDominant` has cap 130: prove the original polygons reduced
from their actual chart covers, derive schematic dominance of the finite
surjective normalization, and transport it through the flat base-change squares.
The resulting normalization products are finite, surjective and epimorphisms.
The coefficient algebra may be nonreduced; reducedness is used only over K.

`W17_CYCLIC_DESCENT_PROOF.lean` compiles before release. U6d9
`CyclicProductDescent` has cap 90: obtain node descents from U6d7, transport their
factorizations through U6d6's actual cartesian squares, and apply schematic
descent gluing over the product atlas using U6d8. Uniqueness and preservation
of the parameter base map follow from the normalization epimorphism. This is
global affine-parameter descent for n >= 2, still to be matched to the specified
over-category cocone and extended to general base schemes.

`W17_TORUS_PROOF.lean` compiles before release. U6d10 `OneGonProductTorus`
has cap 100: the full tensor-Laurent chart has identity normalization, proved
by pasting the original torus square and canceling the base-change square.
Both projections and the normalization equation are proved; no invariant
alpha-chart assumption or noncanonical coordinate replacement is used.

`W17_ONEGON_DESCENT_PROOF.lean` compiles before release. U6d11
`OneGonProductDescent` has cap 100: apply schematic descent gluing to the actual
node/torus product cover, using U6d4 for the node and U6d10 for the torus.
The result is global unique arbitrary-target descent for n=1, with the base
map and node-section factorization. The specified over-category span and
general scheme base still require comparison and locality arguments.

## W17 validation and remaining exact-span descent

Checked at 2026-10-03 04:30 UTC; base 38f8782e; implementation head 1f740224.
Read-only checks: `GOAL_MAZUR_W17_VALIDATION.txt` and the axiom audit below.

| Item | Module under `FLT/Mazur/` | Lines/cap | Commit |
| --- | --- | --- | --- |
| U6d3 | `OneGonProductNormalization` | 136/160 | `c68a7cfe` |
| U6d4 | `OneGonProductEndpoints` | 101/130 | `c68a7cfe` |
| U6d5 | `NodeNormalizationBaseChange` | 111/140 | `c68a7cfe` |
| U6d6 | `CyclicProductNormalization` | 139/180 | `c68a7cfe` |
| U6d7 | `CyclicProductEndpoints` | 110/150 | `c68a7cfe` |
| U6d8 | `PolygonNormalizationDominant` | 96/130 | `1f740224` |
| U6d9 | `CyclicProductDescent` | 47/90 | `1f740224` |
| U6d10 | `OneGonProductTorus` | 73/100 | `1f740224` |
| U6d11 | `OneGonProductDescent` | 59/100 | `1f740224` |

The exact W16 one-gon normalization pullback contract is now proved by
`OneGonProductNormalization.node_isPullback`, with zero/one endpoint transport.
The cyclic node analogue is `CyclicProductNormalization.node_isPullback`, with
origins mapped to zero and adjacent infinity on the normalization coproduct.
Both actual affine-parameter polygons now have unique arbitrary-target global
descent (`OneGonProductDescent.exists_desc`, `CyclicProductDescent.exists_desc`).
The base-morphism equations are proved, as is the one-gon node factorization.
These statements allow arbitrary commutative coefficient algebras, including
nonreduced ones. The one-gon torus keeps its canonical tensor coordinates.

## Validation

Every module passed its foreground `LEAN_NUM_THREADS=2 lake build FLT.Mazur.MODULE`
and its separate `LEAN_NUM_THREADS=2 lake exe runLinter FLT.Mazur.MODULE`.
The final builds are warning-free; no whole-library build or lint was run.
`LEAN_NUM_THREADS=2 lake env lean GOAL_MAZUR_W17_AXIOM_AUDIT.lean` checked all
162 originating declarations, including generated helpers, with only
`propext`, `Classical.choice`, `Quot.sound` (`GOAL_MAZUR_W17_ALL_AXIOMS.txt`).
No placeholders, new axioms or native_decide occur in the nine modules.
All leaves fit their caps, assigned after compiling the full proof prototypes.
`git diff --check 38f8782e` passes; imports are sorted and complete.
All commits use krandder / 5401138+krandder@users.noreply.github.com, without AI credit.

## Exact remaining gap

**U6 remains unproved:** the global descent results have not yet been transported
to the exact `Over.pullback g` pinching span, or extended by locality to an
arbitrary scheme base. This is unfinished proof work, not an approval or
infrastructure blocker. The new global descent theorems do not assert
preservation of a closed pinching pushout.

`W17_U6_REMAINING_CONTRACT.lean` compiles without placeholders; its output is
`GOAL_MAZUR_W17_U6_CONTRACT.txt`. It checks both the affine-parameter specified
`IsPushout` and final arbitrary-base, arbitrary-cocone target. These two targets
are checked propositions, not proved theorems. Two useful helper proofs there
are checked and axiom-audited: `componentsIso` identifies the original scheme
normalization coproduct with the specified over-category coproduct;
`nodeRetraction_toNodes` proves the node leg split epic.

Next obligations, without assigning unchecked caps:

1. Transport `componentsIso` through base change and pullback symmetry;
   `Over.pullback` uses `(original, parameter)` order, while the proved descent
   modules use `(parameter, original)`. For n=1 use `coproductUniqueIso`.
2. Pull the input cocone relation back to the actual endpoint sections in U6d4
   and U6d7. Apply the global descent results and `desc_toBase` to obtain the
   descended over-morphism and its normalization factorization. The split-epic
   node leg lets its node factorization follow from the cocone equation.
3. Establish locality in the parameter scheme via its affine open cover,
   including the scalar algebra induced by an affine chart's map to `Spec K`.
   Glue the actual over-morphisms and both factorizations; use normalization
   epimorphisms for overlap equality and uniqueness.
4. Transport the specified polygon result to an arbitrary supplied pushout
   cocone using `PolygonPinching.polygonIso`. Only then close U6.
5. Construct U7 and prove U8–U12; these have not been implemented in W17.

No action or Mazur removal is claimed. Checked source evidence still shows
`axiom Mazur_statement` in `FLT/Assumptions/Mazur.lean:103`, `mazur_W` in
`FLT/Assembly/ExistingInputs.lean:28`, and `mazurTorsionExclusion` in
`FermatsLastTheorem.lean:24`. This is source evidence, not a fresh compiled
axiom audit of `PNat.pow_add_pow_ne_pow`. Full G1 moduli, G2 arithmetic and the
remaining assembly work are also unproved; existing-consumer edits remain
outside the new-module-only authorization.


## W18 checked transport design

`W18_TRANSPORT_PROOF.lean` and `W18_PUSHOUT_PROOF.lean` compile in full
before release (2026-10-03). U6e1 `PinchingPullbackTransport` has cap 140:
compare parameter-first products with `Over.pullback` using pullback symmetry
and functorial isomorphisms; pull a cocone equation back to both branch sections;
prove the node leg split epic after any base change. A general categorical
criterion then reduces the pushout universal property to unique normalization
descent. No preservation of a pinching pushout is assumed.

`W18_CYCLIC_TRANSPORT_PROOF.lean` compiles in full before release.
U6e2 `CyclicPinchingProduct` has cap 160. The coproduct comparison and
pullback symmetry identify normalization and each endpoint. Apply W17 global
descent to the transported cocone, use `desc_toBase` for the over-morphism,
and invoke U6e1's split-leg criterion. The conclusion is the specified
`Over.pullback` pushout for every coefficient algebra and every n ≥ 2.

`W18_ONEGON_TRANSPORT_PROOF.lean` compiles in full before release.
U6e3 `OneGonPinchingProduct` has cap 150. The singleton coproduct comparison
identifies the normalization and its zero/infinity sections. W17 one-gon
descent supplies the over-morphism, and U6e1 supplies the node factorization.
This proves the specified affine-parameter pushout also for n = 1.

`W18_AFFINE_PROOF.lean` compiles in full before release. U6e4
`PolygonPinchingAffineBaseChange` has cap 130. Combine n = 1 and n ≥ 2 using
the atlas isomorphisms, then use `polygonIso` for an arbitrary supplied cocone.
For any map from `Spec S`, recover its algebra using `Spec.preimage`; for
an arbitrary affine scheme, reflect the pushout along pullback by `isoSpec.inv`,
an equivalence, and transport through `Over.pullbackComp`. This proves U6
for every affine scheme base, including nonreduced coefficient rings.

`W18_LOCALITY_PROOF.lean` compiles before release. U6e5
`OverPullbackLocalPushout` has cap 110. The underlying map of a pulled-back
over-morphism forms the expected cartesian square. Pull the base cover back
to the target, use local pushout descents and that square for factorization,
then invoke schematic descent gluing. Cancellation recovers the structure
map and proves uniqueness. This is a generic locality lemma with geometric
hypotheses, not an assumed preservation result for the pinching square.

`W18_FLAT_PROOF.lean` compiles in full before release. U6e6
`PolygonPinchingFlatBaseChange` has cap 120. The specified polygon is reduced;
its finite surjective normalization is schematically dominant. The cartesian
square from U6e5 preserves these properties under flat base change. On every
member of the parameter's affine cover, U6e4 and `Over.pullbackComp` give the
local pushout; U6e5 glues descent. U6e1 supplies the node factorization.
Finally `polygonIso` transports to any supplied pinching cocone. This closes
the exact U6 contract for arbitrary scheme bases with a flat structure map.

`W18_TENSOR_PROOF.lean` compiles before release. U7a
`PolygonPinchingTensor` has cap 80. Apply U6, postcompose the structure map
back to `Spec K` (a colimit-preserving functor), and transport through pullback
symmetry. The result is the exact pinching pushout after tensoring on the
left by any flat parameter object, including the split smooth group.

`W18_ENDPOINT_ACTION_PROOF.lean` compiles before release. U7b
`ProjectiveLineActionEndpoints` has cap 110. Precompose with the inverse
right unitor, identify the resulting product section by its two projections,
and apply U5's zero/infinity formulas. These are the endpoint equations on
the actual monoidal products needed to check U7's cocone.

`W18_ACTION_PROOF.lean` compiles in full before release. U7c
`PolygonUniversalAction` has cap 150. G4's product/coproduct colimit defines
the normalization and node inputs. U7b fixes the endpoints; `rotateIndex_next`
handles infinity on the successor component. U7a descends this cocone to
`G ⊗ C ⟶ C`, with proved normalization, node and individual-component formulas.
This closes U7's morphism construction, not its unit or associativity laws.

`W18_SPECIALIZE_PROOF.lean` compiles in full before release. U8a
`ProjectiveLineActionSpecialization` has cap 160. The product projections
identify constant-unit specialization on each polynomial chart; U1's
specialization identities give the existing projective-line scaling. Laurent
generators identify the Hopf counit with evaluation at one. Comparing the
monoidal product map with this specialization proves the projective-line
unit law. This also supplies constant-unit formulas needed by U12.

`W18_UNIT_PROOF.lean` compiles before release. U8b `PolygonActionUnit`
has cap 80. The split node leg makes normalization epic. Precompose with
the inverse left unitor and with normalization; on every component, U7's
formula and U8a's projective-line unit law give the identity. This closes U8.

### W18 validated outcome (2026-10-03 05:19 UTC)

U6–U8 are proved; U9–U12 remain unfinished. Implementation commits:
`5a495164` (U6) and `95ba78a7` (U7/U8).

| Item | Module under `FLT/Mazur/` | Lines/cap | Commit |
| --- | --- | --- | --- |
| U6e1 | `PinchingPullbackTransport` | 95/140 | `5a495164` |
| U6e2 | `CyclicPinchingProduct` | 125/160 | `5a495164` |
| U6e3 | `OneGonPinchingProduct` | 113/150 | `5a495164` |
| U6e4 | `PolygonPinchingAffineBaseChange` | 91/130 | `5a495164` |
| U6e5 | `OverPullbackLocalPushout` | 69/110 | `5a495164` |
| U6e6 | `PolygonPinchingFlatBaseChange` | 81/120 | `5a495164` |
| U7a | `PolygonPinchingTensor` | 45/80 | `95ba78a7` |
| U7b | `ProjectiveLineActionEndpoints` | 81/110 | `95ba78a7` |
| U7c | `PolygonUniversalAction` | 105/150 | `95ba78a7` |
| U8a | `ProjectiveLineActionSpecialization` | 130/160 | `95ba78a7` |
| U8b | `PolygonActionUnit` | 50/80 | `95ba78a7` |

Checks: foreground `LEAN_NUM_THREADS=2 lake build FLT.Mazur.MODULE` and
`LEAN_NUM_THREADS=2 lake exe runLinter FLT.Mazur.MODULE` for each module
separately; all final runs exit 0 without warnings.
`GOAL_MAZUR_W18_AXIOM_AUDIT.lean` checks all 137 originating declarations,
including generated helpers, using only the standard three axioms.
`W18_REMAINING_CONTRACT.lean` checks the proved U6/U7/U8 declarations and
the unproved universal projective-line associativity and torus equations.
The latter are propositions, not theorems.

The next proof gate is the two-parameter projective-line action law over the
actual group product, followed by its torus multiplication formula. These
are needed to descend polygon associativity and identify smooth restriction.
Constant-unit specialization and the unit law do not discharge that gate.
U11 base-change action laws and U12 translation/graph identification remain
separate obligations. No caps for these remaining proofs are released here.
The Mazur assumption and existing assembly consumers are unchanged.


## W19 checked affine-point design

`W19_POINTS_PROOF.lean` compiles in full (2026-10-03). U9a
`ProjectiveLineActionPoints`, cap 160, evaluates both polynomial charts over
any coefficient algebra. Pullback projections identify the evaluation map;
polynomial generators give scaling by the unit and its inverse. Tensor
projections and Laurent generators identify the actual Hopf multiplication
with multiplication of units. The parameters need not be field-valued.
This supplies chart computations, not yet universal associativity.

`W19_ASSOC_PROOF.lean` compiles in full before release. U9b
`ProjectiveLineActionAssociativity`, cap 180, compares both composites on
the two polynomial charts over `K[T;T⁻¹] ⊗[K] K[T;T⁻¹]`. The tensor spectrum
isomorphism and three projections identify the actual iterated product and
associator. U9a computes the two sides as `(a*b)*x` and `a*(b*x)` (with
inverse units on the second chart); cover extensionality proves `assoc_act`.

`W19_POLYGON_PROOF.lean` compiles before release. U9c
`PolygonActionAssociativity`, cap 100, tensors the pinching pushout and uses
the split node leg to cancel the normalization. The product/coproduct
comparison reduces the result to U9b and commuting cyclic rotations.
This proves the exact polygon `assoc_act` contract, including n=1.

`W19_TORUS_PROOF.lean` compiles before release. U10a
`ProjectiveLineActionTorus`, cap 100, identifies the torus inclusion with
the first affine-chart coordinate of a unit. U9a computes its image under
universal scaling. The actual tensor spectrum comparison and Hopf
multiplication prove `gm ◁ torusToComponent ≫ act = μ[gm] ≫ torusToComponent`.

`W19_SMOOTH_PROOF.lean` compiles before release. U10b
`PolygonActionSmooth`, cap 100, constructs the actual inclusion of the smooth
open. U10a and the split-group component multiplication identify restriction
of the polygon action. Transport through `smoothIso`, with `smoothGrpObj` and
`smoothCommGrpObj` installed explicitly, proves `smooth_restriction`.

`W19_BASECHANGE_PROOF.lean` compiles before release. U11
`PolygonActionBaseChange`, cap 120, defines the action using the tensorator
of the actual `Over.pullback g` functor. Generic lax-monoidal naturality and
coherence transport each proved law. `unit_act` and `assoc_act` hold for any
scheme morphism g, without a flatness assumption or pushout-preservation
hypothesis. These are equations for the pulled-back action and group.

`W19_TRANSLATION_PROOF.lean` compiles before release. U12a
`PolygonActionTranslation`, cap 120, specializes the actual universal action
at a unit and split component. U8a identifies projective-line specialization;
U7's component formula and epic normalization prove `translation_eq`: the
translation is exactly `polygonScaling ≫ polygonRotation`. Node and component
formulas follow for every field and positive n. This alone does not identify
the irreducible-component graph of a base-changed polygon.

`W19_H3_PROOF.lean` compiles before release. H3
`PolygonStructureInclusion`, cap 100, constructs the canonical morphism from
the polygon structure module to the actual normalization direct image. Its
map on each open is exactly `p.left.app`. Finite surjective normalization and
the reduced atlas, transported through `polygonIso`, give schematic dominance
and injectivity on every open; the sheaf morphism is monic. This does not yet
prove exactness at the normalization direct image.

`W19_H4_PROOF.lean` compiles before release. H4
`PolygonBranchDifferenceSheaf`, cap 120, selects the zero and adjacent infinity
branches over the actual node coproduct. The cocone equations put both maps
over the polygon; direct-image composition gives restriction morphisms of
module sheaves. Their difference is oriented zero minus adjacent infinity,
and `inclusion_difference` proves the composite with H3 vanishes.
No epimorphism, kernel equality, or H5 short exactness is assumed or claimed.

`W19_IMAGES_PROOF.lean` compiles before release. U12b
`PolygonTranslationImages`, cap 100, identifies specialization as an
automorphism and proves exact set-image equations for normalization components
and nodes, including an explicit one-component theorem. Surjectivity of the
projective scaling automorphism removes its parameter from the component
image. Identifying these images with geometric irreducible components after
base change remains a separate U12 obligation.

`W19_H7_PROOF.lean` compiles before release. Split H7 into vanishing and
constant sections before claiming its full conclusion. H7a
`ProjectiveLineCohomologyVanishing`, cap 140, lifts the two homogeneous indices
to the field universe by an explicit graded renaming isomorphism. The existing
zero-twist Čech calculation computes actual Ext cohomology; the zero-twist
structure-module isomorphism and `standardIso` transport vanishing to the
constructed line. `structure_positive` proves every positive degree vanishes;
`h1_zero` has the exact `H1 (ProjectiveLine.toBase K)` type. H7b, constant
sections and the base-linear H0 comparison, remains a separate obligation.

`W19_H0_PROOF.lean` compiles before release. H7b
`ProjectiveLineConstantSections`, cap 160, uses the actual polynomial
restrictions of a global section and their Laurent-overlap equality. Positive
coefficients vanish because inversion gives only nonpositive exponents; the
constant coefficients agree. Cover extensionality and the specified base map
prove `constant_sections`; `h0Equiv` identifies the actual H0 with K linearly,
and `h0Equiv_constants` checks the canonical constants. Together H7a/H7b close H7.


## W19 validated outcome (2026-10-03 06:20 UTC)

Checked local implementation head `1b348890`, relative to base `4b52a77e`.
Checks: `GOAL_MAZUR_W19_VALIDATION.txt`, `GOAL_MAZUR_W19_ALL_AXIOMS.txt`,
and the compiled `W19_REMAINING_CONTRACT.lean`.

**U9–U11, H3, H4 and H7 are proved. U12 is partial; H5 and the remaining
genus/moduli/arithmetic work are unfinished.** All commits are local.

| Item | Module under `FLT/Mazur/` | Lines/cap | Commit |
| --- | --- | --- | --- |
| U9a | `ProjectiveLineActionPoints` | 128/160 | `d8c0f475` |
| U9b | `ProjectiveLineActionAssociativity` | 142/180 | `a1c9d444` |
| U9c | `PolygonActionAssociativity` | 56/100 | `a1c9d444` |
| U10a | `ProjectiveLineActionTorus` | 70/100 | `83cfc548` |
| U10b | `PolygonActionSmooth` | 67/100 | `83cfc548` |
| U11 | `PolygonActionBaseChange` | 72/120 | `83cfc548` |
| U12a | `PolygonActionTranslation` | 82/120 | `5ae0d44a` |
| U12b | `PolygonTranslationImages` | 59/100 | `5ae0d44a` |
| H3 | `PolygonStructureInclusion` | 60/100 | `5ae0d44a` |
| H4 | `PolygonBranchDifferenceSheaf` | 81/120 | `5ae0d44a` |
| H7a | `ProjectiveLineCohomologyVanishing` | 102/140 | `1b348890` |
| H7b | `ProjectiveLineConstantSections` | 123/160 | `1b348890` |

U9 proves both exact universal associativity equations, comparing the two
projective charts over the tensor of independent Laurent parameters. U10
proves the torus multiplication formula and the restriction through the actual
smooth-locus isomorphism. U11 proves unit and associativity for the actual
pullback action along an arbitrary scheme morphism.

U12a/b identify specialization with uniform scaling followed by rotation and
prove its set-image formulas on normalization components and nodes, including
n=1. These do **not** identify the geometric irreducible-component graph after
field extension. H3/H4 construct the actual normalization and branch-difference
module-sheaf maps, prove monicity of the first and vanishing of their composite.
H7 computes actual H0 and H1 of the specified projective line, including the
canonical scalar comparison and vanishing in every positive degree.

Each module passed its foreground `LEAN_NUM_THREADS=2 lake build MODULE` and
separate `LEAN_NUM_THREADS=2 lake exe runLinter MODULE`. Final runs have no
warnings. The combined audit checks all 137 originating declarations, including
generated helpers, with only `propext`, `Classical.choice`, `Quot.sound`.
No whole-library build or lint was run. All caps are at most 240, each released
after its complete proof prototype compiled; imports and scope checks pass.

### Exact remaining proof gates

1. **U12:** identify normalization images with geometric irreducible components
   and nodes with graph edges; compare the pulled-back polygon/group coordinates
   and translations by arbitrary extension-field points. Theorems for every
   chosen base field do not alone prove this base-change identification.
2. **H5:** compare H3/H4 on the cyclic-node and one-gon charts with the proved
   normalization-ring equalizers and branch evaluations. Prove local
   surjectivity and kernel equality, then the actual sheaf short exact sequence.
   Monicity and a zero composite do not supply those claims.
3. **H8/H9:** identify actual scalar cohomology of the normalization/node direct
   images with `Fin n → K` in degree zero, with the specified restriction maps,
   and prove degree-one vanishing. The typed remaining contracts compile.
4. **H10–H15:** identify the long-exact-sequence map with cyclic incidence, then
   prove polygon constants, properness, dimension, genus and geometric-fiber
   comparison. H7 is projective-line cohomology, not polygon genus.

These remaining gates have no newly released caps. They are unfinished proof
work, not a permission or infrastructure blocker. Full G1 moduli, G2 arithmetic,
and final assembly remain unproved. A source check still finds
`axiom Mazur_statement` at `FLT/Assumptions/Mazur.lean:103`, `mazur_W` at
`FLT/Assembly/ExistingInputs.lean:28`, and the final consumer at
`FermatsLastTheorem.lean:24`. No fresh compiled consumer axiom audit or removal
of the Mazur dependency is claimed.


## W20 checked H5 auxiliary design

Checked 2026-10-03: `W20_AFFINE_EXACT_PROOF.lean` and
`W20_SPECTRUM_PROOF.lean` compile without placeholders. H5 is split before
implementation; these auxiliary leaves do not close the global polygon gate.

- H5a `AffineModuleExact`, cap 60: the natural tilde counit identifies a
  spectrum-module complex with the tilde of its global sections. Exactness of
  tilde transports section short exactness to the actual sheaves.
- H5b `StructureDirectImageSections`, cap 70: `ΓSpecIso` identifies global
  sections of the actual structure direct image with the source ring. Naturality
  computes both the canonical unit and branch restrictions.

The affine node and one-gon sequences, comparison with restrictions of the
polygon maps, and global short exactness remain separate obligations. No cap
for those unfinished proofs is released here.

`W20_SCHEME_BRANCH_PROOF.lean` compiles in full with 30,000 heartbeats per
command. H5c `AffineBranchSequence`, cap 140, uses the actual direct images on
spectra. Its section formulas identify the two branch maps; the ring kernel
condition and explicit surjectivity transfer through H5a. Scheme-map equations
are inputs to this generic construction, derived from ring-map equations in
its applications. Neither global polygon exactness nor its chart comparisons
are assumptions of this construction.

`W20_NODE_PROOF.lean` compiles in full. H5d `AffineNodeNormalizationExact`,
cap 120, applies H5c to the cyclic node ring and to the one-gon endpoint-equalizer
ring. Kernel lifts are the equalizer subtypes themselves. Surjectivity uses
`(C a, 0)` for the two-branch node and `C a * (1-X)` for the one-gon, with the
orientation zero minus adjacent infinity. These prove `ShortComplex.ShortExact`
for actual sheaves on the two affine spectra. Comparing these complexes with
restrictions of H3/H4 on the glued polygon remains open.

`W20_OPEN_IMAGE_PROOF.lean` compiles before release. H5e
`StructureImageOpenChart`, cap 140, identifies the actual structure direct
image on any cartesian open chart. Ring section isomorphisms prove module
linearity; naturality with the structure inclusion and with arbitrary compatible
branch restrictions is proved, not assumed.

`W20_OPEN_EXACT_PROOF.lean` compiles before release. H5f
`ModuleExactOpenCover`, cap 100, detects zero modules on covers, then detects
vanishing of the kernel, homology and cokernel. Its final theorem uses the
actual open-immersion maps of `Scheme.OpenCover`, via `isoOpensRange`.
It still needs proved local short exactness on those maps for the polygon.

`W20_POLYGON_COMPLEX_PROOF.lean` compiles in full. H5g
`PolygonNormalizationComplex`, cap 110, defines precisely H5's complex using
H3/H4. The cartesian squares for normalization and nodes, and the two endpoint
commutation equations, give an isomorphism with the actual affine complex.
`chart_shortExact` transfers the proved ring exactness through this isomorphism.
It does not posit an unproved sheaf-exactness field. The concrete atlas data must
still be supplied, including the one-gon's complementary torus chart.

`W20_CYCLIC_NODE_CHART_PROOF.lean` compiles before release. H5h
`CyclicNodeChart`, cap 140, proves that a node belongs only to its own cyclic
chart: different charts meet along punctured branches, which exclude the node.
This gives the node pullback square, transported through the canonical
coproduct comparison to the specified over-category nodes. It includes n=2.

`W20_CYCLIC_NORMALIZATION_CHART_PROOF.lean` compiles in full. H5i
`CyclicNormalizationExact`, cap 180, transports the normalization pullback via
`coprodSpec`, proves both endpoint equations against the specified branch
sections, and applies H5g/H5f. `CyclicNormalizationChart.shortExact` proves the
actual sheaf short exact sequence for every cyclic polygon n ≥ 2, including n=2.
The one-gon and transport to arbitrary supplied cocones are separate gates.

`W20_ONEGON_NODE_CHART_PROOF.lean` compiles in full. H5j
`OneGonNormalizationChart`, cap 130, uses the existing Möbius normalization
coordinate `alpha`. Its zero/one endpoints are the projective zero/infinity;
the one-component coproduct comparisons give the cartesian squares. The actual
one-gon normalization complex is short exact on its pinched affine chart.
The complementary torus chart is still required for global one-gon exactness.

`W20_ONEGON_TORUS_PROOF.lean` compiles in full before release. H5k
`OneGonNormalizationTorus`, cap 120, proves that the node preimage over the torus
is empty and that normalization there is the identity in cartesian coordinates.
The first map is an isomorphism and the third object vanishes; the two-chart
cover proves global one-gon short exactness.

`W20_TRANSPORT_PROOF.lean` compiles before release. H5l
`PolygonNormalizationTransport`, cap 100, compares actual complexes under a
cocone isomorphism by their cartesian squares. Restriction along the inverse
reflects exactness, transporting the atlas result to any supplied cocone.

`W20_H5_PROOF.lean` compiles in full. H5m `PolygonNormalizationExact`, cap 70,
assembles the one-gon and cyclic atlas results and transports them through
`polygonIso`. Its `shortExact` proves H5 for the exact H3/H4 maps and any
specified positive-size pinching cocone. `abelianSheaf_shortExact` supplies the
additive-sheaf sequence used by cohomology. H5 is now proved; H8/H9 and the
genus and geometric incidence bridges remain separate obligations.

`W20_COPRODUCT_SECTIONS_PROOF.lean` compiles before release. H8a/H9a
`SchemeCoproductSections`, cap 100, applies the Gamma-Spec adjunction to the
coproduct and proves each coordinate is the actual component restriction.
It includes the comparison for coproducts formed in schemes over a base.
The index and coefficient universes are independent, so `Fin n` needs no
coefficient-universe restriction.

`W20_H0_IMAGE_PROOF.lean` compiles before release. H8b/H9b
`StructureDirectImageHZero`, cap 60, identifies degree-zero direct-image
cohomology with source global sections. The scalar comparison uses the actual
composite structure morphism; no affine or separatedness assumption is needed.

`W20_COPRODUCT_CONSTANTS_PROOF.lean` compiles before release. H8c/H9c
`CoproductConstantSections`, cap 80, turns proved constant-section properties
on components into a ring and base-linear section equivalence. Its coordinate
lemma identifies values by actual component restriction.

`W20_COPRODUCT_IMAGE_H0_PROOF.lean` compiles in full. H8d/H9d
`PolygonNormalizationHZero`, cap 100, applies the section comparison to the
actual normalization and node module sheaves. H7 supplies constant sections
on each projective line; `ΓSpecIso` supplies them on each point. The resulting
`normalizationEquiv` and `nodeEquiv` are base-linear equivalences with `Fin n → K`,
with explicit coordinate restriction formulas. Degree-one vanishing remains open.

`W20_NODE_CLOSED_PROOF.lean` compiles before release. H9e
`PolygonNodesClosed`, cap 110, proves the actual node map is a closed immersion
for cyclic polygons, the one-gon and any specified pinching cocone. On each
node chart evaluation is a surjective ring map; over the complementary
one-gon torus the source is empty. Thus the node map is finite and affine.

## W20 validated outcome

Checked 2026-10-03 07:38 UTC. Foreground module builds and single-module lint passed
for all 18 new modules. The originating-declaration audit in
`GOAL_MAZUR_W20_AXIOM_AUDIT.lean` checked 207 declarations; every dependency
axiom is `propext`, `Classical.choice` or `Quot.sound`. The checked consumer
`W20_REMAINING_CONTRACT.lean` proves the exact original H5 target and both
H0 equivalence targets, and checks node finiteness. These root validation
artifacts stay untracked, outside the library and docs.

H5 is proved for every positive polygon size and every supplied pinching
cocone, using the actual H3 inclusion and H4 branch difference. The proof
includes n=1 and n=2, and gives additive-sheaf short exactness. H8/H9 now have
their H0 identifications with `Fin n → K`, with component and node restriction
formulas. The node map is a closed immersion, hence finite and affine.

H8/H9 degree-one vanishing is still unproved. The available
`affinePushforward_moduleH_subsingleton_iff` requires a separated target;
polygon separatedness has not yet been established in these modules. It also
needs cohomology of the normalization coproduct to be compared with the H7
projective-line calculation. Prove these prerequisites, or supply a direct
acyclic comparison that avoids separatedness, before marking H8/H9 complete.
No bounded proof cap is released for these unfinished obligations.

The cyclic incidence comparison, polygon constants, properness, dimension,
genus and geometric base change remain open. Geometric U12 still needs actual
irreducible components and node/edge incidence after field extension. The
moduli/arithmetic argument and final assembly also remain open: source check
`rg -n 'Mazur_statement|mazur_W' FLT/Assumptions/Mazur.lean
FLT/Assembly/ExistingInputs.lean` still finds the assumption and its use.
No compiled final-consumer axiom audit or Mazur removal is claimed.


## W21 separatedness prerequisite: checked split

`W21_COVER_PROOF.lean` compiles before release. S1 `SeparatedOpenCover`,
cap 80, tests the diagonal on the product cover. The standard cartesian
diagonal square identifies each restriction with the actual overlap map.
Since that map is an immersion, a closed image suffices. This is a general
criterion; it does not assume or yet prove polygon separatedness.

The concrete closed overlap graphs and their chart-pair assembly are separate
leaves. No cap is released for a leaf until its complete prototype compiles.

`W21_GRAPH_PROOF.lean` compiles in full. S2 `CyclicOverlapGraph`, cap 130,
proves surjectivity of the actual tensor ring map using T and T⁻¹. The tensor
spectrum comparison identifies its spectrum with the Laurent overlap graph
in the product of adjacent node charts. That graph is a closed immersion.
This proves each edge graph, including the two edges relevant to n=2; it does
not yet assemble chart-pair closedness or polygon separatedness.

`W21_CYCLIC_PROOF.lean` compiles in full. S3 `PolygonCyclicSeparated`, cap
160, identifies each distinct chart intersection image with the union of its
available forward and reverse edge graphs. Injectivity of the open pullback
projection turns the atlas point-equality theorem into this exact image
identity. Equal chart pairs use the affine diagonal; S1 assembles the cover.
Both edges remain in the n=2 case. The structure morphism and underlying
cyclic scheme are separated. The one-gon remains a separate leaf.

`W21_ONEGON_GRAPH_PROOF.lean` compiles in full. S4 `OneGonOverlapGraph`,
cap 150, proves that z + z⁻¹ - 2 inverts the conductor t(t-1) under the actual
Möbius transition. The existing conductor-localization theorem gives
surjectivity of the tensor ring map. The tensor spectrum comparison then
proves that the specified one-gon overlap graph is a closed immersion.
The binary-cover assembly remains a separate leaf.

`W21_ONEGON_SEPARATED_PROOF.lean` compiles in full. S5 `OneGonSeparated`,
cap 120, obtains the actual chart pullback from the gluing colimit's point
equality criterion. S4 supplies the mixed graph; exchange of factors handles
its reverse, and identical chart pairs use their affine diagonals. S1 proves
the one-gon structure morphism and underlying scheme separated.

`W21_POLYGON_SEPARATED_PROOF.lean` compiles in full. S6 `PolygonSeparated`,
cap 60, assembles S3/S5 for every positive size and transports separatedness
through the canonical cocone isomorphism. The exact missing W20 instance
`(PolygonAtlas.polygon K n).left.IsSeparated` is now supplied.

`W21_H1_PROOF.lean` compiles in full. H9f/H8e
`PolygonDirectImageCohomology`, cap 90, transports affineness from the finite
scheme coproduct of points. Affine cohomology vanishing and the proved
separatedness give H9 positive-degree vanishing for the actual node direct
image of any specified cocone. The same affine comparison reduces H8 to
positive-degree vanishing on the normalization coproduct; it does not assume
that remaining conclusion.

`W21_DISJOINT_COHOMOLOGY_PROOF.lean` compiles in full. H8f
`DisjointStructureCohomology`, cap 110, proves positive-degree structure
cohomology vanishing from a disjoint open cover and proved acyclicity on each
chart. A tuple intersection is one chart or empty; increasing tuples in
positive degree have empty intersection. The existing Čech homotopy and
acyclic-cover comparison finish the proof without assuming affine charts.

`W21_COPRODUCT_COHOMOLOGY_PROOF.lean` compiles in full. H8g
`SchemeCoproductCohomology`, cap 90, transports structure cohomology through
scheme isomorphisms and the component open-range isomorphisms. The actual
coproduct cover is disjoint and exhaustive. H8f and H7 give positive-degree
vanishing for the specified normalization coproduct, with the index universe
lifted explicitly. No restriction on the coefficient-field universe is used.

`W21_NORMALIZATION_H1_PROOF.lean` compiles in full. H8h/H9g
`PolygonNormalizationHOne`, cap 60, applies the affine comparison to the
proved source vanishing. It proves the exact scalar H1 targets for the
normalization and node module sheaves of every supplied pinching cocone,
and all positive degrees for normalization. Together with W20's H0
comparisons, this closes H8 and H9.

`W21_INCIDENCE_PROOF.lean` compiles in full. H10a `PolygonHZeroIncidence`,
cap 140, computes restriction on actual direct-image global sections. Each
branch reads the specified component constant. H0 naturality and subtraction
identify `moduleScalarHMap` of H4 with `PolygonIncidence.difference` under
W20's equivalences, including its orientation and the n=1 case.

`W21_H1_INCIDENCE_PROOF.lean` compiles in full. H10b
`PolygonCohomologyIncidence`, cap 110, uses the exact H5 connecting map. H8
makes it surjective; H10a and exactness identify its kernel with the range
of cyclic incidence. `h1Incidence` proves the original H10 linear-equivalence
target and `h1_finrank` computes actual H1 dimension one.

`W21_CONSTANTS_PROOF.lean` compiles in full. H11 `PolygonConstantSections`,
cap 120, embeds actual H0 in the component constants using H5. H10a places
its image in the incidence kernel. The specified base scalar map gives every
constant vector, so `constants` proves `HasConstantGlobalSections C.hom`.
Both conclusions apply to every supplied positive-size pinching cocone.

`W21_CLOSED_COVER_PROOF.lean` compiles in full. H12a
`UniversallyClosedFiniteCover`, cap 70, proves closedness by writing an image
as a finite union of closed chart images, then repeats this on each actual
base-changed cover. It supplies the universal-closedness step for the finite
coproduct of proper projective lines.

`W21_PROPER_PROOF.lean` compiles in full. H12b `PolygonProper`, cap 90,
transports properness to the actual projective line, applies H12a to the
finite normalization coproduct, and descends universal closedness through
the surjective normalization. Proved separatedness and local finite
presentation give `IsProper C.hom` for every supplied cocone.

`W21_INTEGRAL_DIMENSION_PROOF.lean` compiles in full. H13a
`IntegralDimension`, cap 60, lifts each finite chain of primes by going up
from a prime above its head. Surjective contraction therefore bounds the
base dimension by that of the extension.

`W21_OPEN_DIMENSION_PROOF.lean` compiles in full. H13b
`OpenCoverDimension`, cap 60, transports chart dimensions to their actual
open ranges and applies the sober-space local upper bound. Open embeddings
give the complementary lower bound.

`W21_NODE_DIMENSION_PROOF.lean` compiles in full. H13c
`PolygonNodeDimension`, cap 70, uses H13a and the finite normalization rings
to bound both actual node rings above by one. Quasi-finite incomparability
and the split normalization's polynomial quotient give the lower bounds.

`W21_POLYGON_DIMENSION_PROOF.lean` compiles in full. H13d
`PolygonDimension`, cap 100, applies the proved node-ring dimensions to
the actual cyclic and one-gon covers. The one-gon torus embeds in the
affine line. An open node chart supplies the lower bound in each case.
The cocone isomorphism transports dimension one to every supplied cocone.

`W21_GENUS_PROOF.lean` compiles in full. H14 `PolygonGenusOne`, cap 60,
combines actual H1 dimension one with H11/H12/H13. The theorem proves the
original curve-genus equality for every supplied cocone, in `Type` as
required by the existing proper-cohomology genus API. It does not assert
the additional nodal geometric-fiber conditions in H15.

### W21 remaining geometric proof gates

H15 remains unfinished. `NodalGenusOneGeometricFibers` quantifies over actual
pullback squares at every algebraically closed extension field and requires
`NodalGenusOneFiberCore`, which extends `NodalFiberCore`. H14 proves genus
with actual properness, constants and total dimension; it does not supply
connectedness, pure dimension of every irreducible component, or the
completed-stalk node criterion. `CurveNode.IsNode` asks for an algebra
isomorphism from the completion of the actual local ring to the split
power-series node model. A polynomial node equation does not fill this field.

The existing `PolygonPinchingAffineBaseChange.spec_pullback` preserves the
pinching pushout for every affine base map. To apply the new genus theorem
to that square, identify the base-changed projective-line components, node
coproducts and endpoint maps with the specified diagram over the extension
field, then transport the pushout. The new theorem's validity over every
field does not by itself provide these comparison maps.

Geometric U12 still needs the actual normalization component images to be
identified with irreducible components, with distinctness and node/edge
incidence after field extension. Existing translation image formulas remain
useful, including n=1, but do not establish this graph identification. A
bounded next leaf is the component-image classification over a field; it
also supports the missing pure-dimension proof. No cap is released before a
complete prototype for that leaf is checked.

These are unproved prerequisites, not mathematical obstructions and not a
request for user permission. The moduli/arithmetic and final assembly work
also remain. Read-only source checks on 2026-10-03 at 08:46 UTC still find
`Mazur_statement` in `FLT/Assumptions/Mazur.lean:103` and the `mazur_W`
consumer in `FLT/Assembly/ExistingInputs.lean:28`. Recheck with
`rg -n 'Mazur_statement|mazur_W' FLT/{Assumptions/Mazur,Assembly/ExistingInputs}.lean`. No final-consumer axiom audit or Mazur
removal is claimed here.

### W21 checked outcome

Checked at 2026-10-03 08:57 UTC. Separatedness and H8–H14 are proved; H15,
geometric U12 and Mazur removal remain unfinished. The 20 new modules total
1,407 lines. All caps were released only after complete root prototypes
compiled.

| Item | Module | Lines/cap |
| --- | --- | ---: |
| S1 | `SeparatedOpenCover` | 42/80 |
| S2 | `CyclicOverlapGraph` | 100/130 |
| S3 | `PolygonCyclicSeparated` | 138/160 |
| S4 | `OneGonOverlapGraph` | 115/150 |
| S5 | `OneGonSeparated` | 95/120 |
| S6 | `PolygonSeparated` | 43/60 |
| H8e/H9f | `PolygonDirectImageCohomology` | 61/90 |
| H8f | `DisjointStructureCohomology` | 86/110 |
| H8g | `SchemeCoproductCohomology` | 59/90 |
| H8h/H9g | `PolygonNormalizationHOne` | 40/60 |
| H10a | `PolygonHZeroIncidence` | 106/140 |
| H10b | `PolygonCohomologyIncidence` | 92/110 |
| H11 | `PolygonConstantSections` | 98/120 |
| H12a | `UniversallyClosedFiniteCover` | 46/70 |
| H12b | `PolygonProper` | 63/90 |
| H13a | `IntegralDimension` | 34/60 |
| H13b | `OpenCoverDimension` | 35/60 |
| H13c | `PolygonNodeDimension` | 45/70 |
| H13d | `PolygonDimension` | 73/100 |
| H14 | `PolygonGenusOne` | 36/60 |

Each module passed its foreground `LEAN_NUM_THREADS=2 lake build
FLT.Mazur.MODULE` and individual `lake exe runLinter FLT.Mazur.MODULE`,
without warnings. No whole-library build or lint was run.
`W21_CONSUMER_CONTRACT.lean` compiled the exact separatedness, H8/H9, H10,
constants, properness, dimension and genus conclusions.
`GOAL_MAZUR_W21_AXIOM_AUDIT.lean` checked all 158 originating declarations,
including generated helpers, and found only `propext`, `Classical.choice`
and `Quot.sound`. Both checks used `LEAN_NUM_THREADS=2 lake env lean FILE`.
The source guard found no `sorry`, `axiom` or `native_decide` in the new
modules; all caps and sorted unique imports passed. The audit, validation
logs and handoff remain untracked at the workspace root.

## W22: geometric-fiber prerequisites

The complete root prototypes `W22_PROJECTIVE_TOPOLOGY_PROOF.lean` and
`W22_OPEN_COMPONENT_PROOF.lean` compiled before these caps were released.

| Leaf | Module | Cap | Checked proof design |
| --- | --- | ---: | --- |
| H15a | `ProjectiveLineTopology` | 90 | The Laurent overlap is nonempty and open in each integral affine chart, hence dense; the two charts cover the glued line. Its dense irreducible image proves irreducibility. |
| H15b | `OpenIrreducibleComponent` | 50 | A larger irreducible set meeting an open subset lies in the closure of their intersection; this proves maximality of the open subset's closure. |

H15 as a whole remains unfinished: component classification, pure dimension,
connectedness, completed-stalk nodes, and the field-extension comparison are
separate proof obligations. No cap for those obligations is claimed yet.
