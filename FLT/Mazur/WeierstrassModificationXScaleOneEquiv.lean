/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXScaleOneMaps

/-!
# The scale-one chart is the entire localized slope line

The two explicit maps are inverse on the original incidence and slope
coordinates. The equivalence also retains the original cubic functions x and y.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (hs : s = 1) (h2 : W.a₂ = 0) (h3 : b3 = 0) (h4 : b4 = 0) (h6 : b6 = 0)
local notation "A" => Coordinate W s b3 b4 b6
local notation "P" => SlopeOpen W.a₁
local notation "T" => t W s b3 b4 b6
local notation "V" => v W s b3 b4 b6
local notation "forward" => scaleOneToSlope W s b3 b4 b6 hs h2 h3 h4 h6
local notation "backward" => slopeToScaleOne W s b3 b4 b6 hs h2 h3 h4 h6

/-- The actual inverse denominator maps to the original incidence parameter. -/
theorem slopeToScaleOne_inv : backward (slopeInv W.a₁) = T := by
  have h := congrArg backward (slope_mul_inv W.a₁)
  simp only [map_mul, map_add, map_one, AlgHom.commutes, slopeToScaleOne_z] at h
  apply (scaleOne_product_isUnit W s b3 b4 b6 hs h2 h3 h4 h6).mul_left_cancel
  rw [h, mul_comm _ T, scaleOne_relation W s b3 b4 b6 hs h2 h3 h4 h6]

/-- The two maps compose to the identity on the entire original coordinate algebra. -/
theorem slopeToScaleOne_comp : (backward).comp forward = AlgHom.id R A := by
  apply hom_ext
  · change backward (forward T) = T
    rw [scaleOneToSlope_t, slopeToScaleOne_inv]
  · change backward (forward V) = V
    rw [scaleOneToSlope_v, slopeToScaleOne_z]

/-- The two maps compose to the identity on the full localization. -/
theorem scaleOneToSlope_comp : (forward).comp backward = AlgHom.id R P := by
  apply IsLocalization.algHom_ext (Submonoid.powers (slopePolynomial W.a₁))
  apply Polynomial.algHom_ext
  change forward (backward (slopeZ W.a₁)) = slopeZ W.a₁
  rw [slopeToScaleOne_z, scaleOneToSlope_v]

/-- The full scale-one chart, with neither tangent factor restored or discarded. -/
def scaleOneSlopeEquiv : A ≃ₐ[R] P :=
  AlgEquiv.ofAlgHom forward backward
    (scaleOneToSlope_comp W s b3 b4 b6 hs h2 h3 h4 h6)
    (slopeToScaleOne_comp W s b3 b4 b6 hs h2 h3 h4 h6)

/-- The comparison retains the original incidence coordinate. -/
theorem scaleOneSlopeEquiv_t :
    scaleOneSlopeEquiv W s b3 b4 b6 hs h2 h3 h4 h6 T = slopeInv W.a₁ :=
  scaleOneToSlope_t W s b3 b4 b6 hs h2 h3 h4 h6

/-- The comparison retains the original slope coordinate. -/
theorem scaleOneSlopeEquiv_v :
    scaleOneSlopeEquiv W s b3 b4 b6 hs h2 h3 h4 h6 V = slopeZ W.a₁ :=
  scaleOneToSlope_v W s b3 b4 b6 hs h2 h3 h4 h6

/-- The comparison retains the original cubic horizontal function. -/
theorem scaleOneSlopeEquiv_x :
    scaleOneSlopeEquiv W s b3 b4 b6 hs h2 h3 h4 h6 (x W s b3 b4 b6) =
      slopeZ W.a₁ * (slopeZ W.a₁ + algebraMap R P W.a₁) := by
  rw [scaleOne_x W s b3 b4 b6 h2 h3 h4 h6, map_mul, map_add,
    AlgEquiv.commutes, scaleOneSlopeEquiv_v]

/-- The comparison retains the original cubic vertical function. -/
theorem scaleOneSlopeEquiv_y :
    scaleOneSlopeEquiv W s b3 b4 b6 hs h2 h3 h4 h6 (y W s b3 b4 b6) =
      (slopeZ W.a₁ * (slopeZ W.a₁ + algebraMap R P W.a₁)) * slopeZ W.a₁ := by
  rw [y, map_mul, scaleOneSlopeEquiv_x, scaleOneSlopeEquiv_v]

end FLT.Mazur.WeierstrassModificationX
