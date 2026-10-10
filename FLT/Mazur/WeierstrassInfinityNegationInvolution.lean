/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityNegationChart

/-!
# Negation preserves its infinity neighborhood and is involutive there

The normalizing denominator maps to its reciprocal. Thus the Y-chart negation
lifts to an endomorphism of its own localization, and applying it twice restores
the original coordinates over every coefficient ring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Negation sends its defining denominator to the normalizing reciprocal. -/
theorem infinityNegationChart_den :
    infinityNegationChart W (infinityNegationDen W) = infinityNegationInverse W := by
  change infinityNegationChart W (-coord W 1 1 - algebraMap R _ W.a₁ * coord W 1 0 -
    algebraMap R _ W.a₃ * coord W 1 2) = _
  rw [coord_self]
  simp only [map_sub, map_neg, map_one, map_mul, AlgHom.commutes,
    infinityNegationChart_coord]
  change -1 - algebraMap R _ W.a₁ *
    (infinityNegationInverse W * infinityNegationRestriction W (coord W 1 0)) -
      algebraMap R _ W.a₃ *
        (infinityNegationInverse W * infinityNegationRestriction W (coord W 1 2)) = _
  have h := infinityNegationInverse_mul W
  change infinityNegationInverse W * infinityNegationRestriction W
    (-coord W 1 1 - algebraMap R _ W.a₁ * coord W 1 0 -
      algebraMap R _ W.a₃ * coord W 1 2) = 1 at h
  simp only [coord_self, map_sub, map_neg, map_one, map_mul, AlgHom.commutes] at h
  linear_combination h

/-- The regular infinity formula lifts to its own input neighborhood. -/
def infinityNegationEnd : InfinityNegationOpen W →ₐ[R] InfinityNegationOpen W :=
  IsLocalization.Away.liftAlgHom (infinityNegationDen W)
    (show IsUnit (infinityNegationChart W (infinityNegationDen W)) by
      rw [infinityNegationChart_den]
      exact Units.isUnit _)

/-- The lifted endomorphism retains the normalized chart negation. -/
theorem infinityNegationEnd_restriction :
    (infinityNegationEnd W).comp (infinityNegationRestriction W) = infinityNegationChart W := by
  apply AlgHom.ext
  intro a
  change infinityNegationEnd W (algebraMap _ _ a) = _
  simp only [infinityNegationEnd, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- The lifted endomorphism takes every original coordinate to its negation. -/
theorem infinityNegationEnd_restriction_apply (a : Coordinate W 1) :
    infinityNegationEnd W (infinityNegationRestriction W a) = infinityNegationChart W a :=
  DFunLike.congr_fun (infinityNegationEnd_restriction W) a

/-- Negation exchanges the chosen reciprocal and the original denominator. -/
theorem infinityNegationEnd_inverse :
    infinityNegationEnd W (infinityNegationInverse W) =
      infinityNegationRestriction W (infinityNegationDen W) := by
  have h := congrArg (infinityNegationEnd W) (infinityNegationInverse_mul W)
  rw [map_mul, map_one, infinityNegationEnd_restriction_apply, infinityNegationChart_den] at h
  apply (Units.isUnit (infinityNegationDen_isUnit W).unit⁻¹).mul_left_inj.mp
  exact h.trans ((infinityNegationInverse_mul W).symm.trans (mul_comm _ _))

/-- Applying lifted negation to the normalized output restores the original chart. -/
theorem infinityNegationEnd_chart :
    (infinityNegationEnd W).comp (infinityNegationChart W) = infinityNegationRestriction W := by
  apply hom_ext
  intro i
  fin_cases i
  · change infinityNegationEnd W (infinityNegationChart W (coord W 1 0)) =
      infinityNegationRestriction W (coord W 1 0)
    rw [infinityNegationChart_coord, map_mul, infinityNegationEnd_inverse]
    change _ * infinityNegationEnd W (infinityNegationRestriction W (coord W 1 0)) = _
    rw [infinityNegationEnd_restriction_apply, infinityNegationChart_coord]
    change _ * (infinityNegationInverse W * infinityNegationRestriction W (coord W 1 0)) = _
    linear_combination infinityNegationRestriction W (coord W 1 0) *
      infinityNegationInverse_mul W
  · change ((infinityNegationEnd W).comp (infinityNegationChart W)) (coord W 1 1) =
      infinityNegationRestriction W (coord W 1 1)
    simp only [coord_self, map_one]
  · change infinityNegationEnd W (infinityNegationChart W (coord W 1 2)) =
      infinityNegationRestriction W (coord W 1 2)
    rw [infinityNegationChart_coord, map_mul, infinityNegationEnd_inverse]
    change _ * infinityNegationEnd W (infinityNegationRestriction W (coord W 1 2)) = _
    rw [infinityNegationEnd_restriction_apply, infinityNegationChart_coord]
    change _ * (infinityNegationInverse W * infinityNegationRestriction W (coord W 1 2)) = _
    linear_combination infinityNegationRestriction W (coord W 1 2) *
      infinityNegationInverse_mul W

/-- The lifted endomorphism itself is an involution on the whole localized ring. -/
theorem infinityNegationEnd_comp :
    (infinityNegationEnd W).comp (infinityNegationEnd W) =
      AlgHom.id R (InfinityNegationOpen W) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (infinityNegationDen W))
  change ((infinityNegationEnd W).comp (infinityNegationEnd W)).comp
    (infinityNegationRestriction W) =
      (AlgHom.id R (InfinityNegationOpen W)).comp (infinityNegationRestriction W)
  rw [AlgHom.comp_assoc, infinityNegationEnd_restriction, infinityNegationEnd_chart,
    AlgHom.id_comp]

end FLT.Mazur.WeierstrassIntegralChart
