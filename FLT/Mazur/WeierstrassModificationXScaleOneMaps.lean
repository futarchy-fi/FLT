/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXSlopeOpen

/-!
# Actual coordinate maps for the scale-one horizontal chart

Vanishing specialized coefficients give t*v*(v+a₁)=1. The original
coordinate algebra maps to and from the full localized slope line.
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

include h2 h3 h4 h6 in
/-- The original horizontal function is exactly the product of the two tangent slopes. -/
theorem scaleOne_x : x W s b3 b4 b6 = V * (V + algebraMap R A W.a₁) := by
  simp only [x, h2, h3, h4, h6, map_zero, zero_mul, add_zero, sub_zero]
  ring

include hs h2 h3 h4 h6 in
/-- Scale one gives the full incidence relation, not the positive-scale three-line fiber. -/
theorem scaleOne_relation : T * (V * (V + algebraMap R A W.a₁)) = 1 := by
  rw [← scaleOne_x W s b3 b4 b6 h2 h3 h4 h6, incidence, hs, map_one]

include hs h2 h3 h4 h6 in
/-- The original horizontal coordinate is invertible on the entire scale-one chart. -/
theorem scaleOne_product_isUnit : IsUnit (V * (V + algebraMap R A W.a₁)) :=
  isUnit_of_mul_isUnit_right (by
    rw [scaleOne_relation W s b3 b4 b6 hs h2 h3 h4 h6]
    exact isUnit_one)

/-- The original scale-one equation maps to the full slope localization. -/
def scaleOneToSlope : A →ₐ[R] P :=
  evaluation W s b3 b4 b6 (slopeInv W.a₁) (slopeZ W.a₁) (by
    simp only [hs, h2, h3, h4, h6, map_zero, map_one, zero_mul, add_zero,
      sub_zero]
    calc slopeInv W.a₁ * (slopeZ W.a₁ ^ 2 + algebraMap R P W.a₁ * slopeZ W.a₁) =
        (slopeZ W.a₁ * (slopeZ W.a₁ + algebraMap R P W.a₁)) * slopeInv W.a₁ := by ring
      _ = 1 := slope_mul_inv W.a₁)

/-- The original incidence coordinate is the actual inverse tangent product. -/
@[simp] theorem scaleOneToSlope_t :
    scaleOneToSlope W s b3 b4 b6 hs h2 h3 h4 h6 T = slopeInv W.a₁ :=
  evaluation_t _ _ _ _ _ _ _ _

/-- The original slope is the polynomial parameter. -/
@[simp] theorem scaleOneToSlope_v :
    scaleOneToSlope W s b3 b4 b6 hs h2 h3 h4 h6 V = slopeZ W.a₁ :=
  evaluation_v _ _ _ _ _ _ _ _

/-- The full slope localization maps back to the original equation algebra. -/
def slopeToScaleOne : P →ₐ[R] A :=
  IsLocalization.Away.liftAlgHom (f := aeval V) (slopePolynomial W.a₁) (by
    simpa only [slopePolynomial, map_mul, map_add, aeval_X, aeval_C] using
      scaleOne_product_isUnit W s b3 b4 b6 hs h2 h3 h4 h6)

/-- The reverse map retains every polynomial in the original slope. -/
theorem slopeToScaleOne_base (p : R[X]) :
    slopeToScaleOne W s b3 b4 b6 hs h2 h3 h4 h6 (algebraMap R[X] P p) = aeval V p := by
  rw [slopeToScaleOne, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- The reverse map retains the original slope coordinate itself. -/
theorem slopeToScaleOne_z :
    slopeToScaleOne W s b3 b4 b6 hs h2 h3 h4 h6 (slopeZ W.a₁) = V := by
  rw [slopeZ, slopeToScaleOne_base, aeval_X]

end FLT.Mazur.WeierstrassModificationX
