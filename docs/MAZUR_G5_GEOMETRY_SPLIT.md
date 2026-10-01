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

## E4 — construct the polygon and prove the cocone, cap 400, blocked

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
localization, explicit two-component overlaps when n=2. Not ready: overlap
cocycles and arbitrary-target pinching descent remain.
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

E1–E3 are implemented; E4–E5 remain blocked by gluing and arbitrary-target
pinching descent. Build in the foreground with LEAN_NUM_THREADS=2;
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
