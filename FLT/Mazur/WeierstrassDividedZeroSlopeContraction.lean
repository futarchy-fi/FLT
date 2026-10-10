/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroIncidenceInfinity
public import FLT.Mazur.WeierstrassModificationXZeroResidueInfinity

/-!
# The retained start-zero slope has the original cubic contraction

The first retained incidence line restricts to exactly the same affine cubic
functions as the original initial slope chart. This is an equality on every
function, with the original divided coefficients and residue map retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "P" => SlopeOpen a
local notation "z" => slopeZ a
local notation "m" => globalZeroSuccessiveContraction hπ data D j hj hk0 hk
local notation "b" => WeierstrassDilatation.fromOriginal W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)
local notation "f" => zeroResidueOriginalMap D (by omega : 0 < depth) (start + j) hk0
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)

/-- The actual original affine functions restricted to the retained punctured incidence line. -/
@[irreducible] def zeroRetainedSlopeOriginalMap : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] P :=
  ((((Algebra.algHom K (Polynomial K) P).comp
    (fiberIncidenceMap a c)).restrictScalars R).comp m).comp b

omit [IsBezout R] in
/-- The retained slope has exactly the original cubic horizontal coordinate. -/
theorem zeroRetainedSlopeOriginalMap_x :
    zeroRetainedSlopeOriginalMap hπ data D j hj hk0 hk
      (WeierstrassIntegralChart.coord W 2 0) = z * (z + algebraMap K P a) := by
  simp only [zeroRetainedSlopeOriginalMap, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply, WeierstrassDilatation.fromOriginal_x,
    hk0, pow_zero, map_one, one_mul]
  rw [globalZeroSuccessiveContraction_x]
  simp only [map_sub, map_mul, map_add, map_pow, AlgHom.commutes,
    fiberIncidenceMap_v, fiberIncidenceMap_t, zero_pow (by decide : 2 ≠ 0),
    mul_zero, sub_zero]
  rfl

omit [IsBezout R] in
/-- The retained slope has exactly the original cubic vertical coordinate. -/
theorem zeroRetainedSlopeOriginalMap_y :
    zeroRetainedSlopeOriginalMap hπ data D j hj hk0 hk
      (WeierstrassIntegralChart.coord W 2 1) =
        (z * (z + algebraMap K P a)) * z := by
  simp only [zeroRetainedSlopeOriginalMap, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply, WeierstrassDilatation.fromOriginal_y,
    hk0, pow_zero, map_one, one_mul]
  rw [globalZeroSuccessiveContraction_y]
  simp only [map_sub, map_mul, map_add, map_pow, AlgHom.commutes,
    fiberIncidenceMap_v, fiberIncidenceMap_t, zero_pow (by decide : 2 ≠ 0),
    mul_zero, sub_zero]
  rfl

omit [IsBezout R] in
/-- Every original affine function agrees with the original start-zero slope contraction. -/
theorem zeroRetainedSlopeOriginalMap_eq :
    zeroRetainedSlopeOriginalMap hπ data D j hj hk0 hk = f := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · exact (zeroRetainedSlopeOriginalMap_x hπ data D j hj hk0 hk).trans
      (zeroResidueOriginalMap_x D (by omega) (start + j) hk0
        (Data.b3 d) (Data.b4 d) (Data.b6 d)
        (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)).symm
  · exact (zeroRetainedSlopeOriginalMap_y hπ data D j hj hk0 hk).trans
      (zeroResidueOriginalMap_y D (by omega) (start + j) hk0
        (Data.b3 d) (Data.b4 d) (Data.b6 d)
        (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)).symm
  · change zeroRetainedSlopeOriginalMap hπ data D j hj hk0 hk
      (WeierstrassIntegralChart.coord W 2 2) =
      f (WeierstrassIntegralChart.coord W 2 2)
    simp only [WeierstrassIntegralChart.coord_self, map_one]

variable (r : ℕ) (hr : j + 1 + r ≤ n)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The full retained slope chart has the original projective cubic contraction. -/
@[reassoc] theorem zeroRetainedSlope_toCurve :
    olderGlobalZeroSlopeChart hπ data D j hj r hr hk0 hk ≫
      pullback.snd q (finiteGlobalStructure hπ data (j + 1 + r) hr) ≫
        finiteGlobalContraction hπ data (j + 1 + r) hr =
      zeroResidueSlopeContraction D (by omega : 0 < depth) (start + j) hk0
        (Data.b3 d) (Data.b4 d) (Data.b6 d)
        (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) := by
  rw [olderGlobalZeroSlopeChart_toCurve hπ data D j hj r hr hk0 hk]
  rw [← fiberExteriorSlopeChart_incidence a c]
  simp only [Category.assoc]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ ≫ (Spec.map _ ≫ _) = _
  simp only [← Category.assoc, ← Spec.map_comp]
  have H := congrArg (fun g : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] P =>
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ WeierstrassIntegralChart.integralCurveChart W 2)
    (zeroRetainedSlopeOriginalMap_eq hπ data D j hj hk0 hk)
  rw [zeroRetainedSlopeOriginalMap] at H
  exact H

end FLT.Mazur.WeierstrassDividedDepth
