# G1 after G5: polygon action, genus and the remaining Mazur gates

P4 (`PolygonNodeEqualizer`) and P5 (`PolygonIncidence`) supply local ring
exactness and cyclic linear exactness. They do not construct a polygon or
identify that linear complex with sheaf cohomology. This split develops the
relative group candidate and isolates its comparison with the smooth locus.
The historical G1–G4 contracts below retain their original caps.
The W14 frontier after G5 uses new leaves of at most 240 lines.
The signatures are implementation contracts, not yet typechecked declarations.

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
