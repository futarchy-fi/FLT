/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityAdditionChart

/-!
# The infinity pair lies in the regular addition neighborhood

The section (infinity,infinity) over the entire base lifts through both
localizations of the new addition domain. Its image under the regular
addition chart map is the actual infinity section of the curve.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The pair of infinity points as an algebra point of the actual product. -/
def infinityPairEvaluation : ChartProduct W 1 1 →ₐ[R] R :=
  chartProductEvaluation W 1 1 (chartInfinityEvaluation W) (chartInfinityEvaluation W)

/-- The first input of the pair section is infinity. -/
@[simp] theorem infinityPairEvaluation_left (i : Fin 3) :
    infinityLeft W (infinityPairEvaluation W) i = ![0, 1, 0] i := by
  have h := DFunLike.congr_fun (chartProductEvaluation_left W 1 1
    (chartInfinityEvaluation (S := R) W) (chartInfinityEvaluation W)) (coord W 1 i)
  exact h.trans (chartInfinityEvaluation_coord W i)

/-- The second input of the pair section is also infinity. -/
@[simp] theorem infinityPairEvaluation_right (i : Fin 3) :
    infinityRight W (infinityPairEvaluation W) i = ![0, 1, 0] i := by
  have h := DFunLike.congr_fun (chartProductEvaluation_right W 1 1
    (chartInfinityEvaluation (S := R) W) (chartInfinityEvaluation W)) (coord W 1 i)
  exact h.trans (chartInfinityEvaluation_coord W i)

/-- The divided-difference denominator is one along the entire pair section. -/
@[simp] theorem infinityPairEvaluation_den :
    infinityDen W (infinityPairEvaluation W) = 1 := by
  simp [infinityDen, infinitySlopeDenominator]

/-- The divided-difference numerator is zero along the pair section. -/
@[simp] theorem infinityPairEvaluation_num :
    infinityNum W (infinityPairEvaluation W) = 0 := by
  simp [infinityNum, infinitySlopeNumerator]

/-- Lift the pair section through the slope denominator localization. -/
def infinityPairSlopeLift : InfinitySlopeOpen W →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom (infinityDen W (AlgHom.id R _))
    (show IsUnit (infinityPairEvaluation W (infinityDen W (AlgHom.id R _))) by
      rw [infinityDen_map, AlgHom.comp_id, infinityPairEvaluation_den]
      exact isUnit_one)

/-- The slope-domain section restricts to the original pair section. -/
@[simp] theorem infinityPairSlopeLift_comp :
    (infinityPairSlopeLift W).comp (infinitySlopeRestriction W) = infinityPairEvaluation W := by
  apply AlgHom.ext
  intro a
  change infinityPairSlopeLift W (algebraMap _ _ a) = infinityPairEvaluation W a
  simp only [infinityPairSlopeLift, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- The lifted section retains the first infinity input. -/
@[simp] theorem infinityPairSlopeLift_left (i : Fin 3) :
    infinityPairSlopeLift W (infinityLeft W (infinitySlopeRestriction W) i) =
      ![0, 1, 0] i := by
  have h := DFunLike.congr_fun (infinityPairSlopeLift_comp W)
    (chartProductLeft W 1 1 (coord W 1 i))
  exact h.trans (infinityPairEvaluation_left W i)

/-- The lifted section retains the second infinity input. -/
@[simp] theorem infinityPairSlopeLift_right (i : Fin 3) :
    infinityPairSlopeLift W (infinityRight W (infinitySlopeRestriction W) i) =
      ![0, 1, 0] i := by
  have h := DFunLike.congr_fun (infinityPairSlopeLift_comp W)
    (chartProductRight W 1 1 (coord W 1 i))
  exact h.trans (infinityPairEvaluation_right W i)

/-- The regular slope is zero at the pair of infinity points. -/
@[simp] theorem infinityPairSlopeLift_slope :
    infinityPairSlopeLift W (infinitySlope W) = 0 := by
  have h := congrArg (infinityPairSlopeLift W) (infinitySlope_mul_den W)
  simpa only [map_mul, infinityDen_map, infinityNum_map, infinityPairSlopeLift_comp,
    infinityPairEvaluation_den, infinityPairEvaluation_num, mul_one] using h

/-- The homogeneous output at the pair section is the normalized point at infinity. -/
@[simp] theorem infinityPairSlopeLift_output (i : Fin 3) :
    infinityPairSlopeLift W (infinityOutputCoordinates W i) = ![0, 1, 0] i := by
  have h := infinityAdditionXYZ_map (W.map (algebraMap R (InfinitySlopeOpen W)))
    (infinityPairSlopeLift W).toRingHom
    (infinityLeft W (infinitySlopeRestriction W) 0)
    (infinityRight W (infinitySlopeRestriction W) 0)
    (infinityLeft W (infinitySlopeRestriction W) 2) (infinitySlope W)
  have he : (W.map (algebraMap R (InfinitySlopeOpen W))).map
      (infinityPairSlopeLift W).toRingHom = W := by
    ext <;> exact (infinityPairSlopeLift W).commutes _
  rw [he] at h
  simpa only [infinityOutputCoordinates, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    infinityPairSlopeLift_left,
    infinityPairSlopeLift_right, infinityPairSlopeLift_slope, Projective.fin3_def_ext,
    infinityAdditionXYZ_zero, Function.comp_apply] using congrFun h i

/-- Lift the whole pair section through the output Y localization as well. -/
def infinityPairAdditionLift : InfinityAdditionOpen W →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom (infinityOutputCoordinates W 1)
    (show IsUnit (infinityPairSlopeLift W (infinityOutputCoordinates W 1)) by
      rw [infinityPairSlopeLift_output]
      exact isUnit_one)

/-- The final lift restricts to the previously constructed slope-domain lift. -/
@[simp] theorem infinityPairAdditionLift_comp :
    (infinityPairAdditionLift W).comp (infinityOutputRestriction W) =
      infinityPairSlopeLift W := by
  apply AlgHom.ext
  intro a
  change infinityPairAdditionLift W (algebraMap _ _ a) = infinityPairSlopeLift W a
  simp only [infinityPairAdditionLift, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- Both localizations together contain the original pair section over the whole base. -/
theorem infinityPairAdditionLift_restriction :
    (infinityPairAdditionLift W).comp (infinityAdditionRestriction W) =
      infinityPairEvaluation W := by
  rw [infinityAdditionRestriction, ← AlgHom.comp_assoc, infinityPairAdditionLift_comp,
    infinityPairSlopeLift_comp]

/-- Addition on the lifted pair section gives the actual infinity section of the curve. -/
theorem infinityAdditionChart_pair :
    (infinityPairAdditionLift W).comp (infinityAdditionChart W) =
      chartInfinityEvaluation W := by
  apply hom_ext
  intro i
  have h := congrArg (infinityPairAdditionLift W) (infinityAdditionChart_mul W i)
  have hr (a) : infinityPairAdditionLift W (infinityOutputRestriction W a) =
      infinityPairSlopeLift W a := DFunLike.congr_fun (infinityPairAdditionLift_comp W) a
  simpa only [map_mul, hr, infinityPairSlopeLift_output, Projective.fin3_def_ext,
    mul_one, AlgHom.comp_apply, chartInfinityEvaluation_coord] using h

end FLT.Mazur.WeierstrassIntegralChart
