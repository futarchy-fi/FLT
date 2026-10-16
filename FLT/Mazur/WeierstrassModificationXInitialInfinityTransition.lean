/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXMorphism
public import FLT.Mazur.WeierstrassProductOverlap

/-!
# The original infinity transition on the full initial y localization

The actual projective transition restricts to the entire original initial
boundary. Its X/Y coordinate is the original x times the inverse original y,
with every divided coefficient retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
local notation "A" => Coordinate W s b3 b4 b6
local notation "Y" => Localization.Away (y W s b3 b4 b6)
local notation "F" => fromOriginal W s b3 b4 b6 h3 h4 h6
open WeierstrassIntegralChart

/-- The original affine contraction restricted to the complete y-boundary. -/
def initialInfinityOriginalMap : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] Y :=
  (IsScalarTower.toAlgHom R A Y).comp F

/-- Original y is invertible on precisely this original boundary. -/
theorem initialInfinityOriginalMap_y_isUnit :
    IsUnit (initialInfinityOriginalMap W s b3 b4 b6 h3 h4 h6 (coord W 2 1)) := by
  change IsUnit (algebraMap A Y (F (coord W 2 1)))
  rw [fromOriginal_y]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- Lift the actual contraction to the original projective overlap. -/
def initialInfinityOverlapMap : Overlap W 2 1 →ₐ[R] Y :=
  overlapLift W 2 1 (initialInfinityOriginalMap W s b3 b4 b6 h3 h4 h6)
    (initialInfinityOriginalMap_y_isUnit W s b3 b4 b6 h3 h4 h6)

/-- The overlap lift preserves all original affine functions. -/
theorem initialInfinityOverlapMap_base (w : WeierstrassIntegralChart.Coordinate W 2) :
    initialInfinityOverlapMap W s b3 b4 b6 h3 h4 h6
      (algebraMap _ (Overlap W 2 1) w) = algebraMap A Y (F w) :=
  IsLocalization.Away.lift_eq _
    (initialInfinityOriginalMap_y_isUnit W s b3 b4 b6 h3 h4 h6) w

/-- The entire initial y-boundary with the original projective infinity normalization. -/
def initialInfinityTransition : WeierstrassIntegralChart.Coordinate W 1 →ₐ[R] Y :=
  (initialInfinityOverlapMap W s b3 b4 b6 h3 h4 h6).comp (transitionBase W 2 1)

/-- The projective inverse denominator is the original inverse y function. -/
theorem initialInfinityOverlapMap_inverse :
    initialInfinityOverlapMap W s b3 b4 b6 h3 h4 h6 (overlapInverse W 2 1) =
      IsLocalization.Away.invSelf (y W s b3 b4 b6) := by
  apply (IsLocalization.Away.algebraMap_isUnit (S := Y) (y W s b3 b4 b6)).mul_right_cancel
  have h := congrArg (initialInfinityOverlapMap W s b3 b4 b6 h3 h4 h6)
    (overlapInverse_mul W 2 1)
  rw [map_mul, map_one, overlapCoord, initialInfinityOverlapMap_base, fromOriginal_y] at h
  rw [h, mul_comm, IsLocalization.Away.mul_invSelf]

/-- The actual infinity X/Y is the quotient of the original initial coordinates. -/
theorem initialInfinityTransition_x :
    initialInfinityTransition W s b3 b4 b6 h3 h4 h6 (coord W 1 0) =
      algebraMap A Y (x W s b3 b4 b6) *
        IsLocalization.Away.invSelf (y W s b3 b4 b6) := by
  change initialInfinityOverlapMap W s b3 b4 b6 h3 h4 h6
    (transitionBase W 2 1 (coord W 1 0)) = _
  rw [transitionBase_coord, map_mul, overlapCoord, initialInfinityOverlapMap_base,
    fromOriginal_x, initialInfinityOverlapMap_inverse, mul_comm]

/-- The actual infinity and initial maps agree in the original projective curve. -/
@[reassoc] theorem initialInfinityTransition_toCurve :
    Spec.map (CommRingCat.ofHom
      (initialInfinityTransition W s b3 b4 b6 h3 h4 h6).toRingHom) ≫
        integralCurveChart W 1 =
      Spec.map (CommRingCat.ofHom (algebraMap A Y)) ≫
        toCurve W s b3 b4 b6 h3 h4 h6 := by
  rw [show CommRingCat.ofHom
    (initialInfinityTransition W s b3 b4 b6 h3 h4 h6).toRingHom =
      CommRingCat.ofHom (transitionBase W 2 1).toRingHom ≫
        CommRingCat.ofHom (initialInfinityOverlapMap W s b3 b4 b6 h3 h4 h6).toRingHom
    from rfl]
  rw [Spec.map_comp, Category.assoc, integralCurve_output_transition, ← Category.assoc]
  unfold toCurve
  rw [← Category.assoc, ← Spec.map_comp]
  congr 1
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun w => initialInfinityOverlapMap_base W s b3 b4 b6 h3 h4 h6 w)

end FLT.Mazur.WeierstrassModificationX
