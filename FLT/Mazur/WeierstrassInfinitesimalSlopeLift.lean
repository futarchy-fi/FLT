/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassInfinitesimalChart
public import FLT.Mazur.WeierstrassInfinityAdditionChart

/-!
# Infinitesimal pairs lie in the actual slope domain

The pair of square-zero identity sections factors through the original
localized addition domain. The slope is zero there and the homogeneous output
has the previously computed linear coordinates. No tensor algebra is unfolded.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (W : WeierstrassCurve R) (I : Ideal A) (hI : I ^ 2 = ⊥) (x y : I)

/-- The actual product-algebra point for two infinitesimal parameters. -/
def infinitesimalPairEvaluation : ChartProduct W 1 1 →ₐ[R] A :=
  chartProductEvaluation W 1 1 (infinitesimalChartPoint W I hI x).val
    (infinitesimalChartPoint W I hI y).val

/-- The left input retains its normalized infinitesimal coordinates. -/
@[simp] theorem infinitesimalPairEvaluation_left (i : Fin 3) :
    infinityLeft W (infinitesimalPairEvaluation W I hI x y) i = ![(x : A), 1, 0] i := by
  have h := DFunLike.congr_fun (chartProductEvaluation_left W 1 1
    (infinitesimalChartPoint W I hI x).val (infinitesimalChartPoint W I hI y).val)
    (coord W 1 i)
  exact h.trans (evaluation_coord W 1 _ (infinitesimalChart_equation W I hI x) rfl i)

/-- The right input retains its normalized infinitesimal coordinates. -/
@[simp] theorem infinitesimalPairEvaluation_right (i : Fin 3) :
    infinityRight W (infinitesimalPairEvaluation W I hI x y) i = ![(y : A), 1, 0] i := by
  have h := DFunLike.congr_fun (chartProductEvaluation_right W 1 1
    (infinitesimalChartPoint W I hI x).val (infinitesimalChartPoint W I hI y).val)
    (coord W 1 i)
  exact h.trans (evaluation_coord W 1 _ (infinitesimalChart_equation W I hI y) rfl i)

/-- The slope denominator is invertible on the whole infinitesimal pair. -/
theorem infinitesimalPairEvaluation_den :
    IsUnit (infinityDen W (infinitesimalPairEvaluation W I hI x y)) := by
  simpa only [infinityDen, infinitesimalPairEvaluation_left,
    infinitesimalPairEvaluation_right, Projective.fin3_def_ext] using
    infinitySquareZero_denominator (W.map (algebraMap R A)) I hI y.property

/-- Its slope numerator vanishes. -/
@[simp] theorem infinitesimalPairEvaluation_num :
    infinityNum W (infinitesimalPairEvaluation W I hI x y) = 0 := by
  simpa only [infinityNum, infinitesimalPairEvaluation_left,
    infinitesimalPairEvaluation_right, Projective.fin3_def_ext] using
    infinitySquareZero_numerator (W.map (algebraMap R A)) I hI x.property y.property

/-- Lift the pair to the actual localization used to construct the group law. -/
def infinitesimalSlopeLift : InfinitySlopeOpen W →ₐ[R] A :=
  IsLocalization.Away.liftAlgHom (infinityDen W (AlgHom.id R _))
    (show IsUnit (infinitesimalPairEvaluation W I hI x y
      (infinityDen W (AlgHom.id R _))) by
      rw [infinityDen_map, AlgHom.comp_id]
      exact infinitesimalPairEvaluation_den W I hI x y)

/-- The slope-domain lift retains both original input maps. -/
@[simp] theorem infinitesimalSlopeLift_comp :
    (infinitesimalSlopeLift W I hI x y).comp (infinitySlopeRestriction W) =
      infinitesimalPairEvaluation W I hI x y := by
  apply AlgHom.ext
  intro a
  change infinitesimalSlopeLift W I hI x y (algebraMap _ _ a) = _
  simp only [infinitesimalSlopeLift, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- The first input remains the first infinitesimal section after localization. -/
@[simp] theorem infinitesimalSlopeLift_left (i : Fin 3) :
    infinitesimalSlopeLift W I hI x y (infinityLeft W (infinitySlopeRestriction W) i) =
      ![(x : A), 1, 0] i := by
  exact (DFunLike.congr_fun (infinitesimalSlopeLift_comp W I hI x y)
    (chartProductLeft W 1 1 (coord W 1 i))).trans
    (infinitesimalPairEvaluation_left W I hI x y i)

/-- The second input remains the second infinitesimal section after localization. -/
@[simp] theorem infinitesimalSlopeLift_right (i : Fin 3) :
    infinitesimalSlopeLift W I hI x y (infinityRight W (infinitySlopeRestriction W) i) =
      ![(y : A), 1, 0] i := by
  exact (DFunLike.congr_fun (infinitesimalSlopeLift_comp W I hI x y)
    (chartProductRight W 1 1 (coord W 1 i))).trans
    (infinitesimalPairEvaluation_right W I hI x y i)

/-- The slope is zero on every square-zero pair, including equal inputs. -/
@[simp] theorem infinitesimalSlopeLift_slope :
    infinitesimalSlopeLift W I hI x y (infinitySlope W) = 0 := by
  have h := congrArg (infinitesimalSlopeLift W I hI x y) (infinitySlope_mul_den W)
  simp only [map_mul, infinityDen_map, infinityNum_map, infinitesimalSlopeLift_comp,
    infinitesimalPairEvaluation_num] at h
  exact (infinitesimalPairEvaluation_den W I hI x y).mul_left_eq_zero.mp h

/-- The homogeneous output has the actual linearized addition coordinates. -/
@[simp] theorem infinitesimalSlopeLift_output (i : Fin 3) :
    infinitesimalSlopeLift W I hI x y (infinityOutputCoordinates W i) =
      infinityAdditionXYZ (W.map (algebraMap R A)) x y 0 0 i := by
  have h := infinityAdditionXYZ_map (W.map (algebraMap R (InfinitySlopeOpen W)))
    (infinitesimalSlopeLift W I hI x y).toRingHom
    (infinityLeft W (infinitySlopeRestriction W) 0)
    (infinityRight W (infinitySlopeRestriction W) 0)
    (infinityLeft W (infinitySlopeRestriction W) 2) (infinitySlope W)
  have he : (W.map (algebraMap R (InfinitySlopeOpen W))).map
      (infinitesimalSlopeLift W I hI x y).toRingHom = W.map (algebraMap R A) := by
    ext <;> exact (infinitesimalSlopeLift W I hI x y).commutes _
  rw [he] at h
  simpa only [infinityOutputCoordinates, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    infinitesimalSlopeLift_left, infinitesimalSlopeLift_right, infinitesimalSlopeLift_slope,
    Projective.fin3_def_ext, Function.comp_apply] using congrFun h i

end FLT.Mazur.WeierstrassIntegralChart
