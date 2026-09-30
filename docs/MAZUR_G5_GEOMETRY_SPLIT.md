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

## E2 — two disjoint open Laurent branches, cap 260, ready after E1

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
Ready once E1 passes. No polygon existence or singularity assumption.

## E3 — singularity and finite presentation of the actual charts, cap 400, blocked

New `FLT/Mazur/PolygonNodeSmooth.lean`. Define `B : Subalgebra K K[X]`
as `AlgHom.equalizer (Polynomial.aeval 0) (Polynomial.aeval 1)`.
Write `aToBase`, `bToBase` for the induced Spec maps; define
`aOrigin : Spec K ⟶ Spec N`, `bOrigin : Spec K ⟶ Spec B` by evaluation.

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
Blocker: no checked presentation/singularity API bridge in this checkout;
CurveNode defines a completed-ring predicate but explicitly does not prove
smooth/node disjointness. The B localization and presentation must be proved
before this is ready; if the cap fails, split those algebra lemmas first.

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
cocycles, B's missing algebra, and arbitrary-target pinching descent remain.
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
transports E3 along the proved open atlas. Not ready before those proofs.

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

Execute E1 then E2 this wave; E3–E5 are explicitly blocked, not assumed ready
merely because E2 compiles. Build in the foreground with LEAN_NUM_THREADS=2;
run `lake exe runLinter FLT.Mazur.MODULE` separately for each module. Audit all
new declarations with collectAxioms; allow only propext/Classical.choice/Quot.sound.
C-sort FLT.lean public imports; commit each leaf locally; never push. If any
cap fails, commit proved material and record exact remainder and smaller caps
in untracked BLOCKED.md outside FLT/. Only this split document is committed prose.

E1 checked 2026-09-30 20:12 UTC: 136/260 lines; foreground module build,
individual runLinter, and collectAxioms on all 21 module declarations passed.
Audit output: untracked GOAL_MAZUR_W6_E1_AXIOMS.txt; only the three allowed axioms.
