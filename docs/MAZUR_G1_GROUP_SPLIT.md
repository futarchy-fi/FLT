# G1: the relative smooth group frontier

P4 (`PolygonNodeEqualizer`) and P5 (`PolygonIncidence`) supply local ring
exactness and cyclic linear exactness. They do not construct a polygon or
identify that linear complex with sheaf cohomology. This split develops the
relative group candidate and isolates its comparison with the smooth locus.
Caps include headers and helpers; all five proposed modules have cap ≤400.
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

## G1 — Laurent points are units, cap 250, ready

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

## G2 — the smooth multiplicative group over a ring, cap 350, ready

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

## G3 — scaling with a variable unit parameter, cap 300, ready

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

## G4 — the split group with n components, cap 400, after G2

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

## G5 — identify the polygon smooth locus, cap 400, blocked on geometry

New `FLT/Mazur/PolygonSmoothLocus.lean`, namespace `FLT.Mazur.PolygonPinching`.
Use field `K`, `n>0`, `[NeZero n]`, and the existing realized cocone
`p : components K n ⟶ C`, `q : nodes K n ⟶ C`,
`h : IsPushout (toComponents K n hn) (toNodes K n) p q`:

```lean
-- First prove local finite presentation from the node/open charts.
theorem polygon_lfp : LocallyOfFinitePresentation C.hom
-- Install polygon_lfp locally to form C.hom.smoothLocus.
def smoothIso :
    Over.mk (C.hom.smoothLocus.ι ≫ C.hom) ≅ PolygonSplitGroup.model K n
```

Acceptance also identifies each punctured normalization component with its
corresponding `ZMod n` component using `ZMod.finEquiv n`. Transport G4's group
structure through this specified iso. Source: DR II.1.1/1.12(a).
Anchors: `smoothLocus`, `mem_smoothLocus`, `preimage_smoothLocus_eq`
(Morphisms/Smooth.lean:290,294,324), `Scheme.Opens.ι` (Restrict.lean:52),
`ProjectiveLine.overlapLeft`, `IsPushout.hom_ext`, `ZMod.finEquiv`.
Dependencies: G4; a constructed polygon with an open node-chart atlas;
proof that node origins are precisely its nonsmooth points; comparison of
that construction with the specified cocone. None of these geometric
prerequisites follows just by taking Spec of P4's ring pullback. This leaf
is not ready and must not replace those prerequisites with record fields.

## Remaining gates and validation

Execute ready leaves in order, at most three per wave. Build in the foreground,
lint each new module separately, check every declaration's axioms, C-sort the
FLT.lean imports, and commit locally. Only propext, Classical.choice and
Quot.sound are allowed; no sorry or new axioms. If a cap fails, commit proved
lemmas and record the exact remainder plus smaller caps in untracked BLOCKED.md.

Polygon existence/genus has no unimplemented ready leaf in POLYGON_SPLIT after
P5: gluing node charts, the pinching universal property, the normalization
sheaf sequence, P¹ cohomology and its comparison with P5 still need a separate
source split. G5 depends on the geometric part, not on a genus assumption.
After G3/G5, a further bounded split must construct the action morphism on the
whole polygon and prove its laws after base change; P3's constant-unit action
alone cannot do this. Neither this document nor P4/P5 closes G1 or Mazur.

[dr]: https://www.math.uni-bonn.de/people/rapoport/myalggeom/preprints/Lesschemas.pdf
[conrad]: https://math.stanford.edu/~conrad/papers/kmpaper.pdf
