/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassProjectiveAdditionChart

/-!
# Identity sections for the regular projective addition charts

Both mixed infinity/affine sections lie in the output-Z domain. The normalized
chart maps restrict to the identity algebra homomorphism along these sections,
and hence give the identity scheme morphisms on the affine curve chart.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open AlgebraicGeometry CategoryTheory

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The left infinity lift sends every polynomial coordinate to the affine input coordinate. -/
theorem leftInfinityLift_additionCoord (i : Fin 3) :
    chartProductLeftInfinityLift W
      (additionOutputRestriction W 1 2 2 (chartProductAdditionCoordinates W 1 2 i)) =
      coord W 2 i := by
  rw [show additionOutputRestriction W 1 2 2 =
    IsScalarTower.toAlgHom R (ChartProduct W 1 2) (AdditionOutputOpen W 1 2 2) from rfl]
  change chartProductLeftInfinityLift W (algebraMap _ _ _) = _
  rw [chartProductLeftInfinityLift_restriction]
  simpa only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, coord_self, one_mul] using
    congrFun (chartProductAdditionCoordinates_left_infinity W 2) i

/-- The right infinity lift retains the opposite scale of the polynomial formula. -/
theorem rightInfinityLift_additionCoord (i : Fin 3) :
    chartProductRightInfinityLift W
      (additionOutputRestriction W 2 1 2 (chartProductAdditionCoordinates W 2 1 i)) =
      -coord W 2 i := by
  change chartProductRightInfinityLift W (algebraMap _ _ _) = _
  rw [chartProductRightInfinityLift_restriction]
  simpa only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, coord_self, neg_mul,
    one_mul] using
    congrFun (chartProductAdditionCoordinates_right_infinity W 2) i

/-- The regular addition map is the identity along the whole left infinity section. -/
theorem projectiveAdditionChart_left_identity :
    (chartProductLeftInfinityLift W).comp (projectiveAdditionChart W 1 2 2) =
      AlgHom.id R (Coordinate W 2) := by
  apply projectiveAdditionChart_comp_eq
  intro i
  rw [leftInfinityLift_additionCoord, leftInfinityLift_additionCoord, coord_self,
    AlgHom.id_apply, mul_one]

/-- The opposite projective scale cancels, giving the right identity on the affine chart. -/
theorem projectiveAdditionChart_right_identity :
    (chartProductRightInfinityLift W).comp (projectiveAdditionChart W 2 1 2) =
      AlgHom.id R (Coordinate W 2) := by
  apply projectiveAdditionChart_comp_eq
  intro i
  rw [rightInfinityLift_additionCoord, rightInfinityLift_additionCoord, coord_self,
    AlgHom.id_apply, mul_neg, mul_one]

/-- The polynomial output open carries a genuine morphism to the chosen curve chart. -/
def projectiveAdditionChartSpec (j k t : Fin 3) :
    Spec (CommRingCat.of (AdditionOutputOpen W j k t)) ⟶
      Spec (CommRingCat.of (Coordinate W t)) :=
  Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j k t).toRingHom)

/-- The left section followed by the scheme addition map is the identity. -/
theorem projectiveAdditionChartSpec_left_identity :
    Spec.map (CommRingCat.ofHom (chartProductLeftInfinityLift W).toRingHom) ≫
      projectiveAdditionChartSpec W 1 2 2 = 𝟙 _ := by
  rw [projectiveAdditionChartSpec, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((chartProductLeftInfinityLift W).comp (projectiveAdditionChart W 1 2 2)).toRingHom) = _
  rw [projectiveAdditionChart_left_identity]
  exact Spec.map_id _

/-- The right section followed by the scheme addition map is the identity. -/
theorem projectiveAdditionChartSpec_right_identity :
    Spec.map (CommRingCat.ofHom (chartProductRightInfinityLift W).toRingHom) ≫
      projectiveAdditionChartSpec W 2 1 2 = 𝟙 _ := by
  rw [projectiveAdditionChartSpec, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((chartProductRightInfinityLift W).comp (projectiveAdditionChart W 2 1 2)).toRingHom) = _
  rw [projectiveAdditionChart_right_identity]
  exact Spec.map_id _

end FLT.Mazur.WeierstrassIntegralChart
