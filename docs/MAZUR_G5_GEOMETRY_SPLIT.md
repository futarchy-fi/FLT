# G5: geometry of the polygon smooth locus

Source: DR II.1.1 (printed 173 / PDF 31) and II.1.12(a) (178 / 36),
[Bonn scan](https://www.math.uni-bonn.de/people/rapoport/myalggeom/preprints/Lesschemas.pdf).
See DR_SOURCE_LEDGER.md for the transcriptions. The local calculations below
are prerequisites derived from the cyclic pinching description, not additional
numbered DR assertions. This split does not close Mazur_statement G1.

## Correction to the proposed atlas

An open atlas by copies of the two-branch affine node cannot cover the 1-gon:
the 1-gon is irreducible, whereas every neighborhood of the origin of
Spec K[x,y]/(xy) is reducible. Completed or étale local models do not give
such a Zariski open immersion. Do not silently assume n > 1 in G5.
For n ≥ 2 use the equalizer ring `A` already constructed in
PolygonNodeEqualizer. For n = 1 use
`B := {p : K[t] | p.eval 0 = p.eval 1}`: the two points of one affine line
are pinched. This chart comes from deleting the normalization point z=1,
with coordinate t=z/(z-1). Its puncture is D(t(t-1)); adjoining the full
Laurent chart recovers the missing smooth point. This works also in char 2.
For n=2 the two node charts overlap in TWO Laurent components.

All signatures below are contracts; only completed leaves are typechecked.
Caps count entire modules including helpers. No structure may take an atlas,
pushout property, finite presentation, or smooth-locus conclusion as a field.
`K` is a field; `R` is a commutative ring; `N := PolygonNodeEqualizer.A`.

## E1 — localize the two branches, cap 260, implemented

New `FLT/Mazur/PolygonNodeLocalization.lean`, namespace
`FLT.Mazur.PolygonNodeLocalization`. Define `x=(X,0)`, `y=(0,X)` in `N`,
and `leftMap/rightMap : N →+* R[T;T⁻¹]` by branch restriction then toLaurent.

```lean
def x : PolygonNodeEqualizer.A (R := R)
def y : PolygonNodeEqualizer.A (R := R)
theorem x_mul_y : x (R := R) * y = 0
theorem first_surjective : Function.Surjective (PolygonNodeEqualizer.first (R := R))
theorem second_surjective : Function.Surjective (PolygonNodeEqualizer.second (R := R))
-- Each theorem installs its specified map as the algebra structure.
theorem left_isLocalization :
    letI := (leftMap (R := R)).toAlgebra
    IsLocalization.Away (x (R := R)) R[T;T⁻¹]
theorem right_isLocalization :
    letI := (rightMap (R := R)).toAlgebra
    IsLocalization.Away (y (R := R)) R[T;T⁻¹]
```

Lift p to `(p,C(p(0)))`. Equality after the left map is killed by x;
use the symmetric calculation on the right. Source: the punctured branches
in DR II.1.1. Dependencies: P4 only. These are algebra localizations, not a
scheme pushout claim. Unblocks E2 and the n≥2 overlap maps in E4.

## E2 — two disjoint open Laurent branches, cap 260, implemented

New `FLT/Mazur/PolygonNodeBranches.lean`, namespace
`FLT.Mazur.PolygonNodeBranches`. Define `node := Spec (.of N)` and
`left/right := Spec.map (.ofHom leftMap/rightMap)`.

```lean
instance : IsOpenImmersion (left R)
instance : IsOpenImmersion (right R)
theorem range_left : Set.range (left R) = PrimeSpectrum.basicOpen (x (R := R))
theorem range_right : Set.range (right R) = PrimeSpectrum.basicOpen (y (R := R))
theorem disjoint_ranges : Disjoint (Set.range (left R)) (Set.range (right R))
theorem branches_cover_complement :
    Set.range (left R) ∪ Set.range (right R) =
      (PrimeSpectrum.zeroLocus {x (R := R), y (R := R)})ᶜ
```

Also prove both composites to Spec R equal the Laurent structure map.
This identifies the punctured charts with the already smooth G_m, without
claiming that the omitted closed subscheme is the entire nonsmooth locus.
Source: same branch calculation for DR II.1.1. Dependencies: E1 and G2.
Implemented after E1. No polygon existence or singularity assumption.

## E3a — chart algebra, cap 300, implemented; bridge completed in E3b–E3e

New `FLT/Mazur/PolygonNodePresentation.lean`, namespace
`FLT.Mazur.PolygonNodePresentation`. Use the actual equalizer A, not an
unrelated quotient. Define `B := AlgHom.equalizer (Polynomial.aeval 0)
(Polynomial.aeval 1) : Subalgebra K K[X]`, and evaluation maps
`aEval : A →ₐ[K] K`, `bEval : B →ₐ[K] K`. The exact algebra bridge is:

```lean
instance : Algebra.FinitePresentation K (PolygonNodeEqualizer.A (R := K))
instance : Algebra.FinitePresentation K (B (R := K))
theorem a_smoothLocus :
    Algebra.smoothLocus K (PolygonNodeEqualizer.A (R := K)) =
      (PrimeSpectrum.zeroLocus (RingHom.ker (aEval (R := K)).toRingHom))ᶜ
theorem b_smoothLocus :
    Algebra.smoothLocus K (B (R := K)) =
      (PrimeSpectrum.zeroLocus (RingHom.ker (bEval (R := K)).toRingHom))ᶜ
```

No smoothness hypothesis is allowed on either chart. For B the generators
are `u = X*(X-1)` and `v = X*u`, with relation `v²-u*v-u³=0`;
this relation works in characteristic two as well. Finite generation plus
`Algebra.FinitePresentation.of_finiteType` proves finite presentation over K.
The alternatives for singularity are the explicit infinitesimal lifting
obstruction (`FormallySmooth.iff_comp_surjective`) or a computed cotangent
presentation (`smoothLocus_eq_compl_support_inter`). Neither criterion alone
computes this example. Start with explicit generators, then assess the
remaining singularity/localization proof against the total cap; split rather
than replace nonsmoothness by a record field. E3 transports the proved algebra
statement to schemes through the spectrum stalk isomorphisms.

## E3 — singularity and finite presentation of the actual charts, implemented

`FLT/Mazur/NodeSmoothLocus.lean` completes the scheme and algebra smooth-locus
equalities. It reuses `B`, `aToBase`, `bToBase`, `aOrigin` and `bOrigin` from
PolygonNodePresentation, which already supplies both locally finite
presentation instances. The original 400-line proposal was split into the
four separately capped modules below.

```lean
instance : LocallyOfFinitePresentation (aToBase K)
instance : LocallyOfFinitePresentation (bToBase K)
theorem a_smooth_complement :
    ((aToBase K).smoothLocus : Set (Spec (.of N))) = (Set.range (aOrigin K))ᶜ
theorem b_smooth_complement :
    ((bToBase K).smoothLocus : Set (Spec (.of B))) = (Set.range (bOrigin K))ᶜ
```

Source: the ordinary double points of the standard polygon, DR II.1.1.
Dependencies: E2, explicit presentations of N and B, and a proved local
nonsmoothness criterion (e.g. cotangent dimension). None is an input field.
The four completed leaves, in namespace `FLT.Mazur.PolygonNodePresentation`:

- E3b `NodeQuotient` (121/200): surjective aPresent, kernel (xy), quotient equivalence.
- E3c `OneGonQuotient` (154/260): surjective bPresent, kernel (v²-uv-u³), quotient equivalence.
- E3d `NodeInfinitesimalObstruction` (250/250): both origin localizations are not formally smooth.
- E3e `NodeSmoothLocus` (183/220): coordinate zero loci equal origin images;
  both algebra and scheme smooth loci are exactly the origin complements.

All statements concern the actual chart rings, over every field including
characteristic two. The local obstruction extends a nonliftable tangent map
to each origin localization by proving that all denominators map to units.
The smooth-locus bridge uses spectrum stalk isomorphisms, with no assumed
geometric conclusions. Validation commands and evidence are recorded below.

## E4 — construct the polygon and prove the cocone: n=1 complete, general n open

New `FLT/Mazur/PolygonAtlas.lean`, namespace `FLT.Mazur.PolygonAtlas`.
For `n : ℕ`, `[NeZero n]`, `hn : 0 < n`, construct actual glue data using
E2's opens for n≥2 and the B/Laurent construction above for n=1.
Write `base := Spec (.of K)`, and `Achart/Bchart : Over base` for E3's charts.

```lean
def polygon (K : Type u) [Field K] (n : ℕ) [NeZero n] : Over (Spec (.of K))
def normalization : PolygonPinching.components K n ⟶ polygon K n
def nodes : PolygonPinching.nodes K n ⟶ polygon K n
def nodeChart (h : 2 ≤ n) (i : Fin n) : Achart K ⟶ polygon K n
instance (h : 2 ≤ n) (i : Fin n) : IsOpenImmersion (nodeChart K n h i).left
theorem nodeCharts_cover (h : 2 ≤ n) (z : (polygon K n).left) :
    ∃ i w, (nodeChart K n h i).left w = z
theorem isPushout : IsPushout (PolygonPinching.toComponents K n hn)
    (PolygonPinching.toNodes K n) (normalization K n) (nodes K n)
```

For n=1 additionally construct open maps from Bchart and G_m and prove joint
surjectivity. Prove the pushout for arbitrary target schemes by local descent;
Spec of the ring pullback only proves the affine-target case and is insufficient.
Source: cyclic pinching in DR II.1.1. Dependencies: E1–E3, B's puncture
localization, explicit two-component overlaps when n=2. The n=1 case is now
proved in OneGonMarkedPinching, including the exact marked cocone over K.
General n≥2 overlap cocycles and cyclic descent remain.
400 is a hard stop, not a claim that these missing foundations fit that cap.

## E5 — specified cocone comparison and G5, cap 400, blocked

New `FLT/Mazur/PolygonSmoothLocus.lean`, namespace `FLT.Mazur.PolygonPinching`.
For `C : Over (Spec (.of K))`, `p : components K n ⟶ C`, `q : nodes K n ⟶ C`,
and `h : IsPushout (toComponents K n hn) (toNodes K n) p q`:

```lean
def polygonIso : PolygonAtlas.polygon K n ≅ C
theorem polygon_lfp : LocallyOfFinitePresentation C.hom
-- Install polygon_lfp before forming smoothLocus.
def smoothIso :
    Over.mk (C.hom.smoothLocus.ι ≫ C.hom) ≅ PolygonSplitGroup.model K n
```

Require the component formula, with `torusToComponent` induced by
`ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K` and its map over K:
`(Sigma.ι _ ((ZMod.finEquiv n).symm i) ≫ smoothIso.inv).left ≫
 C.hom.smoothLocus.ι = (torusToComponent K ≫ componentι K n i ≫ p).left`.
Then transport the commutative group through this specified iso.
Source: DR II.1.1 and II.1.12(a). Dependencies: E3/E4 and G4.
`IsPushout.isoIsPushout` compares the actual cocones; smooth-locus naturality
transports E3 along the proved open atlas. Not ready before E4’s gluing and cocone proofs.

## API evidence and execution

Checked 2026-09-30 by these read-only searches (M = `.lake/packages/mathlib/Mathlib`):

```
rg -n 'def (A|first|second|lift)|mem_A' FLT/Mazur/PolygonNodeEqualizer.lean
rg -n 'lemma mk|lemma surj' $M/RingTheory/Localization/Away/Basic.lean
rg -n 'instance isLocalization|algebraMap_eq_toLaurent' $M/Algebra/Polynomial/Laurent.lean
rg -n 'of_isLocalization|isoOfRangeEq' $M/AlgebraicGeometry/OpenImmersion.lean
rg -n 'basicOpen_mul|basicOpen_zero|mem_basicOpen' $M/RingTheory/Spectrum/Prime/Topology.lean
rg -n 'structure GlueData|ι_jointly_surjective' $M/AlgebraicGeometry/Gluing.lean
rg -n 'isoIsPushout' $M/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Defs.lean
rg -n 'mem_smoothLocus|preimage_smoothLocus_eq' $M/AlgebraicGeometry/Morphisms/Smooth.lean
rg -n 'does not|not proved|smooth/node' FLT/Mazur/CurveNode.lean
```

E1–E3 and the n=1 case of E4 are implemented. General n≥2 gluing and E5 remain open. Build in the foreground with LEAN_NUM_THREADS=2;
run `lake exe runLinter FLT.Mazur.MODULE` separately for each module. Audit all
new declarations with collectAxioms; allow only propext/Classical.choice/Quot.sound.
C-sort FLT.lean public imports; commit each leaf locally; never push. If any
cap fails, commit proved material and record exact remainder and smaller caps
in untracked BLOCKED.md outside FLT/. Only this split document is committed prose.

E1 checked 2026-09-30 20:12 UTC: 136/260 lines; foreground module build,
individual runLinter, and collectAxioms on all 21 module declarations passed.
Audit output: untracked GOAL_MAZUR_W6_E1_AXIOMS.txt; only the three allowed axioms.

E2 checked 2026-09-30 20:16 UTC: 123/260 lines; foreground module build,
individual runLinter, and collectAxioms on all 24 module declarations passed.
Audit output: untracked GOAL_MAZUR_W6_E2_AXIOMS.txt; only the three allowed axioms.
Both imports are C-sorted in FLT.lean; git diff --check passed. G5 remains open.

Historical E3a W7 checkpoint (superseded by E3b–E3e):
PolygonNodePresentation proves the two finite-generation
calculations, B's relation and conductor divisibility, both finite-presentation
instances and their scheme analogues, B's puncture localization/open immersion,
smoothness of both A branches and B's puncture, and both origin-image formulas.
It does not prove that the displayed equations generate the presentation
kernels, nor nonsmoothness at the origins, nor either exact smooth-locus equality.
The W7 proof inventory occupied 275/300 lines. Its remaining local singularity
calculation was split into the four W8 leaves now completed above.

E3a checked 2026-09-30 20:31 UTC: `LEAN_NUM_THREADS=2 lake build
FLT.Mazur.PolygonNodePresentation` and the individual `lake exe runLinter
FLT.Mazur.PolygonNodePresentation` both passed. The collectAxioms audit
(`/tmp/mazur-w7-e3a-axioms.lean`) checked all 39 module declarations; only
propext, Classical.choice and Quot.sound occur. Output is untracked
GOAL_MAZUR_W7_E3A_AXIOMS.txt. `wc -l` reports 275; C-sorted FLT.lean imports
and `git diff --check` passed. No whole-library build or lint was run.

E3b W8 NodeQuotient checked 2026-09-30 20:41 UTC: `lake build
FLT.Mazur.NodeQuotient`, its individual `runLinter`, and collectAxioms passed
(see untracked GOAL_MAZUR_W8_NODE_AXIOMS.txt). The module is 121/200 lines;
it proves aPresent surjective, its kernel exactly (xy), and the quotient
algebra equivalence to the actual equalizer, over any commutative ring.
The one-gon kernel and origin obstructions remain open at this checkpoint.

E3c W8 OneGonQuotient checked 2026-09-30 20:46 UTC: foreground module
build, individual runLinter and collectAxioms passed (untracked
GOAL_MAZUR_W8_ONEGON_AXIOMS.txt). It proves bPresent surjective over every
commutative ring; over every field, including characteristic two, the kernel
is exactly (v²-uv-u³), with an algebra equivalence to the actual B.
Both presentation kernels are now proved; the origin obstructions remain open.

E3d W8 NodeInfinitesimalObstruction checked 2026-09-30 20:57 UTC:
foreground module build, individual runLinter and all 51 collectAxioms checks
passed (untracked GOAL_MAZUR_W8_OBSTRUCTION_AXIOMS.txt). At 250/250 lines,
it proves both origin local rings non-formally-smooth using the square-zero
map K[e]/(e³) → K[e]/(e²), with explicit nonliftable tangent vectors and
invertibility of every origin-localization denominator. No characteristic
restriction is used. E3 now needs only the smooth-locus identification.


E3e W8 NodeSmoothLocus checked 2026-09-30 21:03 UTC: `LEAN_NUM_THREADS=2
lake build FLT.Mazur.NodeSmoothLocus` and the individual `lake exe runLinter
FLT.Mazur.NodeSmoothLocus` passed, at 183/220 lines. It proves a_zeroLocus_origin,
b_zeroLocus_origin, a_smoothLocus, b_smoothLocus, a_smooth_complement and
b_smooth_complement. E3 is complete; E4 was not started.

The final `lake env lean /tmp/mazur-w8-all-axioms.lean` audit rechecked every
new declaration in all four W8 modules: 17 + 23 + 51 + 15 = 106 declarations,
with only propext, Classical.choice and Quot.sound. Output is untracked
GOAL_MAZUR_W8_ALL_AXIOMS.txt. All four foreground module builds and individual
module lints passed; all line caps, C-sorted FLT.lean imports, and
`git diff --check` passed. No whole-library build or lint was run.

## E4 one-component overlap and chart gluing

`OneGonTransition` constructs the involution t ↦ t/(t-1) on the actual
ring R[t, 1/(t(t-1))], over any commutative ring. `OneGonOverlap` proves
that the resulting map to the Laurent chart is an open immersion with image
D(z-1). `OneGonGluing` glues this map to the existing B-chart puncture,
constructs both open chart inclusions, proves their joint coverage, and
constructs the structure morphism over the coefficient field.

`FLTTest/MazurOneGon` checks the transitive axioms of all declarations in
both new namespaces, and instantiates the involution over Z and ZMod 2.
The chart pushout is constructed; its identification with the specified
one-component cyclic pinching is now proved in OneGonMarkedPinching below.
This does not close E4 for arbitrary n, E5, the genus calculation, the
relative group action, or Mazur_statement.

## E4 affine pinching algebra

`OneGonPinchingAlgebra` proves that B is the categorical pullback of
R[t] → R × R (evaluation at 0 and 1) and R → R × R (the diagonal),
for every commutative ring R. Its lift accepts arbitrary commutative
source rings. Evaluation is surjective by linear interpolation and its
kernel is exactly (t(t-1)). `FLTTest/MazurOneGonPinching` audits all new
declarations and checks instantiation over Z and ZMod 2.

This ring result alone only supplies affine-target descent. Over fields,
OneGonRefinedDescent now proves arbitrary-target descent, and
OneGonNormalization identifies the glued normalization with P¹ in the
t-coordinate and proves its pinching universal property for t=0 and t=1.
No rational torsion exclusion is proved here; NoLargePrimeTorsion remains
the arithmetic target.

The affine-line map to the pinched chart is now proved finite and
surjective, hence closed and a topological quotient map. The finite-module
proof gives explicit generators 1 and t over B, using subtraction of the
difference of endpoint values times t. These results work over every
commutative coefficient ring. Over fields, arbitrary-target descent is now
supplied by OneGonRefinedDescent below. The P¹ identification in the t-coordinate is supplied below.

`OneGonAffineDescent` proves existence and uniqueness of descent for maps
from the affine normalization and pinched point to any affine scheme,
provided their restrictions to the two endpoints agree. The proof uses
the ring pullback and the full faithfulness of Spec, then transports
along the affine target's canonical isomorphism with its spectrum.
This affine result is now extended by the localization and gluing construction
below; it is not the global P¹ pinching or a rational torsion exclusion.

`OneGonDescentUniqueness` proves that over a field the affine normalization
map is an epimorphism in Scheme, using injective maps on global functions
and stalks and the already proved surjectivity. Its hom_ext theorem gives
uniqueness of descent for every target scheme, including nonaffine ones.
Existence for arbitrary targets is now proved in OneGonRefinedDescent.
The P¹ identification in the t-coordinate is supplied below; arithmetic torsion exclusion remains open.

`OneGonLocalizedPinching` identifies the image of B[1/s] in K[t,1/s]
with the equalizer of endpoint evaluations whenever the common value
of s at the node is nonzero. The restriction map is injective. The proof
clears a common denominator and descends its numerator using equality of
endpoint values. This supplies the local algebra used by OneGonRefinedDescent
on principal neighborhoods of the node. The P¹ identification in the t-coordinate is supplied below; rational torsion
exclusion remains open.

## Explicit local maps and two-chart gluing

`OneGonLocalMaps` constructs the descended ring homomorphism via the
localized restriction image, proves its normalization equation and
uniqueness, and takes Spec to obtain the actual local scheme map.
`OneGonMapGluing.nodeMap_on_principal` identifies these maps with the
restrictions of the descended node-chart morphism.

`OneGonMapGluing.gluedMap` glues the descended node morphism and a torus
morphism on the actual OneGonGluing.scheme. The overlap equation is proved
from compatibility on the normalization. Both chart equations, recovery
of the original normalization map, and uniqueness of the global map are
proved. The target scheme can be nonaffine.

Scope of this gluing theorem: the normalization-chart map is supplied
with an explicit affine factorization Spec(K[t]) → Spec(A) → X and equal
endpoint evaluations in Spec(A). The theorem still uses that hypothesis.

## Constructed affine factorizations for arbitrary targets

`OneGonNodeFiber` proves that the fiber of the node is exactly the two
endpoints. It also proves that any principal neighborhood D(s) containing
the node, together with the conductor puncture D(u), covers Spec(B).

`OneGonLocalFactorization.exists_compatible_node_factorization` constructs
a principal neighborhood and an affine target open for any morphism
Spec(K[t]) → X whose endpoint morphisms agree. Closedness of the finite
normalization removes the image of the complement of the target open;
the principal-open basis then supplies s with nonzero node value.
The resulting map Spec(K[t,1/s]) → U has the required composite with U → X.
Equality of the two localized endpoint morphisms is preserved by
cancellation of the open immersion. No affine factorization is assumed.

## Descent and gluing across the refined cover

`OneGonRefinedDescent.existsUnique_desc` proves unique descent of every
endpoint-compatible morphism Spec(K[t]) → X to Spec(B), for an arbitrary
target scheme X over the same universe and any coefficient field K.
It uses the constructed affine factorization, descends it on D(s), and
glues with the original map on the conductor puncture D(u).
The normalization square over D(s) is proved cartesian. Its lifting
property proves equality on the actual intersection; the two opens cover
both the pinched chart and its normalization. No local factorization or
overlap equality for the descended maps is assumed.

`desc` is the resulting morphism, with normalization recovery and
`principal_desc` recording recovery of each compatible local descent.
`gluedMap` then glues it with a compatible torus-chart map on the existing
OneGonGluing.scheme. Its node, torus, and normalization equations and
uniqueness are proved. This removes the supplied affine-factorization
hypothesis required by the earlier OneGonMapGluing API.

## Global normalization in projective coordinates

`OneGonNormalization.scheme` glues Spec(K[t]) and the existing torus chart
along the actual puncture. `projectiveIso` identifies this scheme with
the fixed `ProjectiveLine.scheme`, with both inverse identities proved.
On the affine chart the coordinate is t. On the inverse projective chart
w=1/t, the torus map is w=1-z⁻¹, where z=t/(t-1).
The images D(w) and D(1-w) cover that inverse chart; their intersection
is proved to be the original puncture via a cartesian square.

`projectiveToOneGon` is the resulting map from P¹ to the one-gon.
Its affine restriction is the actual pinching map, and its torus restriction
is the existing torus inclusion. The two identified sections in this
coordinate convention are t=0 and t=1.
`existsUnique_projective_desc` proves that every morphism from P¹ to an
arbitrary scheme identifying these sections factors uniquely through
`projectiveToOneGon`.

This identifies the glued source and proves the pinching universal property
in the (0,1) presentation. The following transport supplies the fixed
(0,∞) marked cocone.

## The specified marked one-component cyclic pinching

`ProjectiveLineMobius.iso` constructs the global automorphism t ↦ t/(t-1)
by gluing across the existing refined affine cover. It proves both inverse
identities, preservation of the structure morphism, fixation of zero, and
interchange of one and infinity. The construction works over every field,
including characteristic two.

`OneGonMarkedPinching.normalization` composes this automorphism with the
previous map to the one-gon. Its zero and infinity sections map to the same
node. Unique arbitrary-target descent is transported first in Scheme and
then in Over(Spec K); the descended morphism's compatibility with the base
is proved using uniqueness.

`componentsMap` and `nodesMap` give the actual two legs from the coproduct
objects in PolygonPinchingDiagram. `isPushout` proves that they realize
the exact span `toComponents K 1 hn`, `toNodes K 1`, without assuming a
pushout existence instance. Hence `isNeronOneGon` proves the project's
`IsNeronNGon (Over.mk (OneGonGluing.toBase K)) 1 hn` predicate, and
`isNeronPolygon` follows. This closes E4 for n=1.

Validation: FLTTest.MazurOneGonPinching audits every declaration in both new
namespaces and its transitive axioms, allowing only propext, Classical.choice,
and Quot.sound, and instantiates the marked one-gon in characteristic two.
The two module linters and mk_all import check are run individually.

General n≥2, the E5 smooth-locus comparison, genus, relative group action,
and the arithmetic rational torsion exclusion remain open. No separate
claim about the library's canonical-normalization interface is made here.
