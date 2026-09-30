# G1 polygon construction: the next five source leaves

This is a bounded frontier of the next gate in MAZUR_G1G2_SPLIT, not a claim
that five small files suffice for all of G1. The first three leaves construct
the scalar part missing from R1–R3's cyclic action. The last two provide
local algebra for polygon existence and the genus computation. Geometric
realization and the identification of the relative smooth group remain open.
No arithmetic conclusion is an input field. Caps count the whole new module.

Checked 2026-09-30 against this checkout. Reproduce the API checks with:

```
rg -n 'eval₂|invert_T|invert_C|induction_on' .lake/packages/mathlib/Mathlib/Algebra/Polynomial/Laurent.lean
rg -n 'left_toBase|right_toBase|overlap_condition|chartToBase' FLT/Mazur/ProjectiveLineCharts.lean
rg -n 'zeroSection|infinitySection|chartZero' FLT/Mazur/ProjectiveLineEndpoints.lean
rg -n 'toComponents|branchι_toComponents|componentι' FLT/Mazur/PolygonPinchingDiagram.lean
rg -n 'polygonRotation|components_polygonRotation' FLT/Mazur/NeronPolygonRotation.lean
rg -n 'desc|hom_ext' .lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Defs.lean
```

Sources: [DR II.1.1, II.1.12](https://www.math.uni-bonn.de/people/rapoport/myalggeom/preprints/Lesschemas.pdf),
printed pp. 173 and 178 (PDF pp. 31 and 36); see DR_SOURCE_LEDGER.md.
The formulas below are explicit algebraic consequences of cyclic pinching
and the scalar action on the normalization, not quotations from DR.
For the genus strategy, use the normalization exact sequence: functions on
the branches must agree at each node. Do not identify its finite incidence
complex with scheme cohomology without proving the sheaf comparison.

## P1 — compatible scaling of affine charts, cap 300, ready now

New `FLT/Mazur/PolygonChartScaling.lean`, namespace
`FLT.Mazur.PolygonChartScaling`. Work over any commutative ring `R`.
For `a : Rˣ`, construct the following ring maps (notation `L = R[T;T⁻¹]`):

```lean
def affine (a : Rˣ) : R[X] →+* R[X] -- X ↦ C ↑a * X
 def laurent (a : Rˣ) : L →+* L -- T ↦ C ↑a * T
 theorem affine_one : affine (1 : Rˣ) = RingHom.id _
 theorem affine_mul (a b : Rˣ) :
     affine (a * b) = (affine a).comp (affine b)
 theorem affine_zero (a : Rˣ) :
     (Polynomial.evalRingHom 0).comp (affine a) = Polynomial.evalRingHom 0
 theorem toLaurent_affine (a : Rˣ) :
     Polynomial.toLaurent.comp (affine a) =
       (laurent a).comp Polynomial.toLaurent
 theorem invert_toLaurent_affine (a : Rˣ) :
     LaurentPolynomial.invert.toRingHom.comp
       (Polynomial.toLaurent.comp (affine a⁻¹)) =
     (laurent a).comp
       (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)
```

Also expose constants and both Laurent generators. Use `Polynomial.eval₂RingHom`
and `LaurentPolynomial.eval₂`; the latter takes an actual unit, constructed
with inverse `C ↑a⁻¹ * T (-1)`. The inverse scaling in the second chart is
essential. This is relative algebra over `R`, not yet a group scheme action.
Source: the usual multiplication action on the punctured projective line
in the standard polygon of DR II.1.1. Dependencies: Mathlib only. Unblocks P2.

## P2 — endpoint-preserving projective scaling, cap 300, after P1

New `FLT/Mazur/ProjectiveLineScaling.lean`; import P1 and
`ProjectiveLineEndpoints`. Namespace `FLT.Mazur.ProjectiveLine`, field `K`:

```lean
def scaling (a : Kˣ) : scheme K ⟶ scheme K
 theorem left_scaling (a : Kˣ) :
     left K ≫ scaling K a = Spec.map (CommRingCat.ofHom (PolygonChartScaling.affine a)) ≫ left K
 theorem right_scaling (a : Kˣ) :
     right K ≫ scaling K a = Spec.map (CommRingCat.ofHom (PolygonChartScaling.affine a⁻¹)) ≫ right K
 theorem scaling_toBase (a : Kˣ) : scaling K a ≫ toBase K = toBase K
 def scalingOver (a : Kˣ) : component K ⟶ component K
 theorem zeroSection_scalingOver (a : Kˣ) : zeroSection K ≫ scalingOver K a = zeroSection K
 theorem infinitySection_scalingOver (a : Kˣ) : infinitySection K ≫ scalingOver K a = infinitySection K
 theorem scalingOver_one : scalingOver K 1 = 𝟙 _
 theorem scalingOver_mul (a b : Kˣ) : scalingOver K (a*b) = scalingOver K a ≫ scalingOver K b
```

Here `component K` means `Over.mk (toBase K)`, as in PolygonPinching.
Construct by the existing open-immersion pushout and P1's two compatibility
equalities. Prove laws by `pushout.hom_ext`; expose inverse scaling as an iso.
Source: the two coordinate formulas for scalar multiplication on P¹.
No new pushout existence is required here: ProjectiveLineCharts already built it.
Unblocks P3. This is an action by constant units, not yet relative representability.

## P3 — scalar action on a realized polygon, cap 350, after P2

New `FLT/Mazur/NeronPolygonScaling.lean`; import P2 and `NeronPolygonRotation`.
Use the same `K,n,hn,C,p,q,h` context as R2; namespace `PolygonPinching`.

```lean
def componentsScaling (a : Kˣ) : components K n ⟶ components K n
 theorem componentι_scaling (a : Kˣ) (i : Fin n) :
     componentι K n i ≫ componentsScaling K a =
       ProjectiveLine.scalingOver K a ≫ componentι K n i
 theorem toComponents_scaling (a : Kˣ) :
     toComponents K n hn ≫ componentsScaling K a = toComponents K n hn
 def polygonScaling (a : Kˣ) : C ⟶ C
 theorem components_polygonScaling (a : Kˣ) :
     p ≫ polygonScaling K hn p q h a = componentsScaling K a ≫ p
 theorem nodes_polygonScaling (a : Kˣ) : q ≫ polygonScaling K hn p q h a = q
 theorem polygonScaling_one : polygonScaling K hn p q h 1 = 𝟙 C
 theorem polygonScaling_mul (a b : Kˣ) :
     polygonScaling K hn p q h (a*b) =
       polygonScaling K hn p q h a ≫ polygonScaling K hn p q h b
 theorem polygonScaling_rotation (a : Kˣ) (b : ZMod n) :
     polygonScaling K hn p q h a ≫ polygonRotation K hn p q h b =
       polygonRotation K hn p q h b ≫ polygonScaling K hn p q h a
```

Construct the component map with `Sigma.desc`, and descend it with identity on
nodes by `h.desc`. Include the inverse iso and `n=1` (no `1<n` hypothesis).
Source: multiplication and rotations on the standard polygon, DR II.1.1/1.12(c).
The result is the two commuting constant-parameter actions; claiming an action
of a relative smooth group scheme would be stronger and is not allowed here.

## P4 — affine node equalizer, cap 350, ready independently, next wave

New `FLT/Mazur/PolygonNodeEqualizer.lean`; namespace `PolygonNodeEqualizer`.
For a commutative ring `R`, construct `A` as the subalgebra of `R[X] × R[X]`
consisting of pairs `(f,g)` with `f.eval 0 = g.eval 0`.

```lean
def inclusion : A →ₐ[R] (R[X] × R[X])
 def difference : (R[X] × R[X]) →ₗ[R] R -- (f,g) ↦ f(0)-g(0)
 theorem inclusion_injective : Function.Injective (inclusion (R := R))
 theorem range_inclusion : LinearMap.range inclusion.toLinearMap = LinearMap.ker difference
 theorem difference_surjective : Function.Surjective (difference (R := R))
 def lift {B : Type*} [CommRing B] [Algebra R B]
     (f g : B →ₐ[R] R[X])
     (h : (Polynomial.aeval (0 : R)).comp f =
          (Polynomial.aeval (0 : R)).comp g) : B →ₐ[R] A
```

Acceptance includes uniqueness and the two projections of `lift`. This is the
ring pullback universal property, not the pushout property in all schemes.
Anchors: `Subalgebra`, `AlgHom.range`, `LinearMap.mem_range`, `LinearMap.mem_ker`
and `Polynomial.aeval`. `rg -n` finds `eval₂AlgHom` in
`Algebra/Polynomial/AlgebraMap.lean:159`, `AlgHom.range` in
`Algebra/Algebra/Subalgebra/Basic.lean:545`, and `mem_ker`/`mem_range` in
`Algebra/Module/Submodule/{Ker,Range}.lean:64/68`. Source: equality of the two values at a pinched node.
Unblocks affine node charts and the local normalization sequence.

## P5 — cyclic normalization incidence, cap 350, ready independently, next wave

New `FLT/Mazur/PolygonIncidence.lean`, field `K`, `n>0`.
Use `Fin n` and the existing `PolygonPinching.next hn` (or an explicitly proved
identification with addition by one in `ZMod n`). Define linear maps
`constant : K →ₗ[K] (Fin n → K)`, `difference : (Fin n → K) →ₗ[K] (Fin n → K)`
by `difference v i = v i - v (next hn i)`, and `total` by summation.

```lean
theorem ker_difference : LinearMap.ker (difference K hn) = LinearMap.range (constant K n)
 theorem range_difference : LinearMap.range (difference K hn) = LinearMap.ker (total K n)
 theorem total_surjective : Function.Surjective (total K n)
```

Prove the second equality by partial sums, never division by `n`: the theorem
must hold when the characteristic divides `n`, and for `n=1`. Anchors:
`Fin.sum_univ_eq_sum_range`, `Finset.sum_range_succ`, `LinearMap.range`,
`LinearMap.ker`. `rg -n` finds the multiplicative source declarations
`Fin.prod_univ_eq_prod_range` in `Data/Fintype/BigOperators.lean:227` and
`prod_range_succ` in `Algebra/BigOperators/Group/Finset/Basic.lean:536`;
`to_additive` generates the cited sum lemmas. Source: the cyclic difference map in the normalization sequence.
Unblocks the genus-one dimension calculation once the geometric comparison exists.

## Acceptance and remaining geometric gate

Implement P1, P2, P3 in order this wave (at most three leaves). Each gets a
foreground `LEAN_NUM_THREADS=2 lake build MODULE`, then its own
`LEAN_NUM_THREADS=2 lake exe runLinter MODULE`, then `#print axioms` for every
new declaration; only `propext`, `Classical.choice`, `Quot.sound` are permitted.
Add public imports in C-sort order; commit each leaf separately, no push.

After P4/P5, still construct the polygon by gluing affine node charts, prove
its specified pinching universal property and normalization exact sequence,
and compare that sequence with actual H⁰/H¹ (including P¹ vanishing).
For the relative group, identify the smooth locus with G_m × Z/n over the
base and promote P1's formulas to morphisms with variable unit parameter,
then glue the action and prove the group laws after base change. These need
another source/API split; none follows merely from the supplied cocone in P3.
