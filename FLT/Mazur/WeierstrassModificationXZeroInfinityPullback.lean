/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInitialInfinityTransition
public import FLT.Mazur.WeierstrassModificationXZeroInfinityTangent
public import FLT.Mazur.WeierstrassModificationXNodeOverlapInfinityIso

/-!
# Pulling back the actual original infinity coordinate to the full node overlap

The localization lift is the previously constructed inclusion-preserving
boundary isomorphism. Thus its X/Y computation concerns that actual geometric
transition, and identifies the original tangent with the reciprocal ratio.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I) (hbot : I = ⊥)
local notation "A" => Coordinate W 0 b3 b4 b6
local notation "Y" => Localization.Away (y W 0 b3 b4 b6)
local notation "O" => PolynomialNodeOverlap W 0
local notation "G" => polynomialNodeOverlapEvaluation W 0 b3 b4 b6 r hr I hI hrI h3
local notation "hy" => polynomialZeroNodeOverlap_y_isUnit W b3 b4 b6 r hr I hI hrI h3 hbot
local notation "e" => polynomialNodeOverlapInfinityIso W 0 b3 b4 b6 r hr I hI hrI h3

/-- Pullback of every original y-localized function to the full node intersection. -/
def polynomialZeroNodeInfinityPullback : Y →ₐ[R] O :=
  IsLocalization.Away.liftAlgHom (y W 0 b3 b4 b6) (f := G) hy

local notation "H" => polynomialZeroNodeInfinityPullback W b3 b4 b6 r hr I hI hrI h3 hbot

/-- The localization pullback retains every original initial affine function. -/
theorem polynomialZeroNodeInfinityPullback_base (a : A) :
    H (algebraMap A Y a) = G a := IsLocalization.Away.lift_eq _ hy a

/-- This explicit pullback induces the actual original boundary comparison isomorphism. -/
theorem polynomialZeroNodeInfinityPullback_spec :
    Spec.map (CommRingCat.ofHom (H).toRingHom) = (e).hom := by
  apply (cancel_mono (polynomialInitialInfinityInclusion W 0 b3 b4 b6)).mp
  rw [polynomialNodeOverlapInfinityIso_hom_inclusion, polynomialNodeOverlapEvaluation_spec]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (polynomialZeroNodeInfinityPullback_base W b3 b4 b6 r hr I hI hrI h3 hbot)

/-- The inverse original y pulls back to the inverse of that same original function. -/
theorem polynomialZeroNodeInfinityPullback_inverse :
    H (IsLocalization.Away.invSelf (y W 0 b3 b4 b6)) = ↑((hy).unit⁻¹) := by
  apply (hy).mul_left_cancel
  have h := congrArg H (IsLocalization.Away.mul_invSelf (S := Y) (y W 0 b3 b4 b6))
  rw [map_mul, map_one, polynomialZeroNodeInfinityPullback_base] at h
  rw [h, (hy).mul_val_inv]

variable (hW3 : W.a₃ = 0 * b3) (hW4 : W.a₄ = 0 * b4) (hW6 : W.a₆ = 0 ^ 2 * b6)
local notation "f" => initialInfinityTransition W 0 b3 b4 b6 hW3 hW4 hW6

/-- The actual projective infinity X/Y pulls back to the exact original quotient. -/
theorem polynomialZeroNodeInfinityPullback_x :
    H (f (WeierstrassIntegralChart.coord W 1 0)) =
      polynomialZeroNodeOverlapXOverY W b3 b4 b6 r hr I hI hrI h3 hbot := by
  rw [initialInfinityTransition_x, map_mul, polynomialZeroNodeInfinityPullback_base,
    polynomialZeroNodeInfinityPullback_inverse]
  rfl

/-- The original infinity tangent, along the actual transition, is the reciprocal full ratio. -/
theorem polynomialZeroNodeInfinityPullback_tangent :
    H (f (1 + algebraMap R (WeierstrassIntegralChart.Coordinate W 1) W.a₁ *
      WeierstrassIntegralChart.coord W 1 0)) =
        (↑((polynomialNodeOverlapRatio W 0 b3 b4 b6 r hr I hI hrI h3)⁻¹) : O) := by
  rw [map_add, map_one, map_mul, AlgHom.commutes, map_add, map_one, map_mul,
    AlgHom.commutes, polynomialZeroNodeInfinityPullback_x]
  exact polynomialZeroNodeOverlap_infinity_tangent W b3 b4 b6 r hr I hI hrI h3 hbot

end FLT.Mazur.WeierstrassModificationX
