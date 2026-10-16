/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFactorRatioMap
public import FLT.Mazur.WeierstrassModificationXOverlapRatioReflection
public import FLT.Mazur.NodalFiberZeroTangentMobiusPuncture

/-!
# Exact reciprocal arithmetic boundaries for the corrected factor coordinates

The full ratio V/U, with its corrected first coordinate, has precisely inverse
boundary parameters under the actual original reflection, at arbitrary smoothing.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (ha : IsUnit W.a₁) (s τ : R) (hτ : s = W.a₁ ^ 2 * τ)
  (b3 b4 b6 : R) (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (g : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (hu : IsUnit (g (polynomialOppositeFactor W s b3 b4 b6 r)))

/-- Evaluate every polygon function in the full original factor-ratio coordinates. -/
def initialFactorRatioEvaluation : PolygonSmoothing.ChartRing τ →ₐ[R] S :=
  NodalFiber.unitNormalizedEvaluation τ τ 1 (by simp)
    (initialFactorRatioBase W ha s τ hτ b3 b4 b6 r hr g hu)

/-- The complete polygon right coordinate is the full original factor ratio. -/
theorem initialFactorRatioEvaluation_right :
    initialFactorRatioEvaluation W ha s τ hτ b3 b4 b6 r hr g hu
      (PolygonSmoothing.rightCoordinate τ) = initialFactorRatio W s b3 b4 b6 r g hu := by
  rw [initialFactorRatioEvaluation, NodalFiber.unitNormalizedEvaluation_right]
  exact NodalFiber.evaluation_q ..

/-- The full first coordinate includes the square of the actual opposite factor. -/
theorem initialFactorRatioEvaluation_left :
    initialFactorRatioEvaluation W ha s τ hτ b3 b4 b6 r hr g hu
      (PolygonSmoothing.leftCoordinate τ) = initialFactorRatioFirst W ha s b3 b4 b6 r g := by
  rw [initialFactorRatioEvaluation, NodalFiber.unitNormalizedEvaluation_left]
  simp only [inv_one, Units.val_one, map_one, one_mul]
  exact NodalFiber.evaluation_p ..

variable (hv : IsUnit (g (polynomialSmallFactor W s b3 b4 b6 r)))
local notation "v" => initialOverlapRatioUnit W s b3 b4 b6 r g hv hu
local notation "g'" => AlgHom.comp g
  (AlgEquiv.toAlgHom (AlgEquiv.restrictScalars R (initialReflection W s b3 b4 b6)))
local notation "hu'" => initialOverlap_reflected_opposite_isUnit W s b3 b4 b6 r g hv
local notation "hv'" => initialOverlap_reflected_small_isUnit W s b3 b4 b6 r g hu

/-- The corrected full polygon map has exactly the original tangent-ratio boundary. -/
@[reassoc] theorem initialFactorRatioEvaluation_boundary :
    Spec.map (CommRingCat.ofHom
      (initialFactorRatioEvaluation W ha s τ hτ b3 b4 b6 r hr g hu).toRingHom) =
        Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) v).toRingHom) ≫
          PolygonSmoothing.rightBranchOpen R τ := by
  apply PolygonSmoothing.boundary_rightBranchOpen
  rw [initialFactorRatioEvaluation_right, initialOverlapRatioUnit_coe]
  rfl

/-- Actual reflection now gives exact inversion, retaining every arithmetic correction. -/
@[reassoc] theorem initialFactorRatioEvaluation_reflected_boundary :
    Spec.map (CommRingCat.ofHom
      (initialFactorRatioEvaluation W ha s τ hτ b3 b4 b6 r hr g' hu').toRingHom) =
        Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) v).toRingHom) ≫
          (PolygonSmoothing.edgeInversion R).hom ≫ PolygonSmoothing.rightBranchOpen R τ := by
  have h := initialFactorRatioEvaluation_boundary W ha s τ hτ b3 b4 b6 r hr g' hu' hv'
  rw [initialOverlapRatioUnit_reflection W s b3 b4 b6 r g hv hu] at h
  rw [NodalFiber.unitParameter_inverse, Category.assoc] at h
  exact h

end FLT.Mazur.WeierstrassModificationX
