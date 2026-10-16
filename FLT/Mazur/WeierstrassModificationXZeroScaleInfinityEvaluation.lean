/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXZeroScaleBaseChange
public import FLT.Mazur.WeierstrassModificationXZeroInfinityPullback
public import FLT.Mazur.WeierstrassModificationXInitialInfinityTensor

/-!
# The actual tensor infinity coordinate on the original zero-node intersection

The original tensor localization is transported without discarding divided
coefficients. Evaluating its actual projective infinity transition gives the
original X/Y quotient and therefore the reciprocal full tangent ratio.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (hs : algebraMap R S s = 0)
local notation "V" => W.map (algebraMap R S)
local notation "c3" => algebraMap R S b3
local notation "c4" => algebraMap R S b4
local notation "c6" => algebraMap R S b6
variable (r : S[X])
  (hr : r ^ 2 + polynomialSlopeLinear (W.map (algebraMap R S)) (algebraMap R S b3) * r =
    polynomialSlopeConstant (W.map (algebraMap R S)) (algebraMap R S b4) (algebraMap R S b6))
  (I : Ideal S) (hI : IsNilpotent I) (hrI : r ∈ I.map C)
  (hc3 : algebraMap R S b3 ∈ I) (hbot : I = ⊥)
local notation "O" => PolynomialNodeOverlap V 0
local notation "A" => Coordinate W s b3 b4 b6
local notation "y" => WeierstrassModificationX.y W s b3 b4 b6
local notation "Y" => Localization.Away y
local notation "G" => polynomialNodeOverlapEvaluation V 0 c3 c4 c6 r hr I hI hrI hc3
local notation "hy" => polynomialZeroNodeOverlap_y_isUnit V c3 c4 c6 r hr I hI hrI hc3 hbot
local notation "v" => polynomialNodeOverlapRatio V 0 c3 c4 c6 r hr I hI hrI hc3
local notation "E" => zeroScaleInfinityBoundaryEquiv W s b3 b4 b6 S hs

/-- All original tensor-boundary functions on the full original zero-node intersection. -/
def zeroScaleNodeInfinityEvaluation :
    Localization.Away ((1 : S) ⊗ₜ[R] y) →ₐ[S] O :=
  (polynomialZeroNodeInfinityPullback V c3 c4 c6 r hr I hI hrI hc3 hbot).comp (E).toAlgHom

local notation "H" => zeroScaleNodeInfinityEvaluation W s b3 b4 b6 S hs r hr I hI hrI hc3 hbot

/-- Every original affine function keeps its exact coefficient-specialized value. -/
theorem zeroScaleNodeInfinityEvaluation_base (a : A) :
    H (PrincipalOpenTensor.coefficient (R := R) S y (algebraMap A Y a)) =
      G (zeroScaleCoefficientMap W s b3 b4 b6 S hs a) := by
  rw [PrincipalOpenTensor.coefficient_base]
  change polynomialZeroNodeInfinityPullback V c3 c4 c6 r hr I hI hrI hc3 hbot
    (E (algebraMap _ _ ((1 : S) ⊗ₜ[R] a))) = _
  rw [zeroScaleInfinityBoundaryEquiv_base, polynomialZeroNodeInfinityPullback_base]
  rfl

/-- The original inverse y is transported as the inverse of the same actual function. -/
theorem zeroScaleNodeInfinityEvaluation_inverse :
    H (PrincipalOpenTensor.coefficient (R := R) S y (IsLocalization.Away.invSelf y)) =
      ↑((hy).unit⁻¹) := by
  apply (hy).mul_left_cancel
  have h := congrArg (fun z => H (PrincipalOpenTensor.coefficient (R := R) S y z))
    (IsLocalization.Away.mul_invSelf (S := Y) y)
  rw [map_mul, map_one, map_mul, map_one, zeroScaleNodeInfinityEvaluation_base,
    zeroScaleCoefficientMap_y] at h
  rw [h, (hy).mul_val_inv]

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
local notation "f" => initialInfinityTensorTransition W s b3 b4 b6 h3 h4 h6 S

/-- The actual original tensor X/Y is the full zero-node overlap's original quotient. -/
theorem zeroScaleNodeInfinityEvaluation_x :
    H (f ((1 : S) ⊗ₜ[R] WeierstrassIntegralChart.coord W 1 0)) =
      polynomialZeroNodeOverlapXOverY V c3 c4 c6 r hr I hI hrI hc3 hbot := by
  rw [initialInfinityTensorTransition_x, map_mul, map_mul,
    zeroScaleNodeInfinityEvaluation_base, zeroScaleCoefficientMap_x,
    zeroScaleNodeInfinityEvaluation_inverse]
  rfl

/-- A named original tensor X/Y coordinate keeps its ambient algebra sealed. -/
def zeroScaleInfinityTensorX : WeierstrassIntegralChart.ChartScalarExtension S W 1 :=
  (1 : S) ⊗ₜ[R] WeierstrassIntegralChart.coord W 1 0

/-- The actual tensor infinity tangent has the original reciprocal ratio on the full overlap. -/
theorem zeroScaleNodeInfinityEvaluation_tangent :
    H (f (1 + algebraMap S (WeierstrassIntegralChart.ChartScalarExtension S W 1) (V).a₁ *
      (zeroScaleInfinityTensorX W S))) = (↑((v)⁻¹) : O) := by
  rw [map_add, map_one, map_mul, AlgHom.commutes, map_add, map_one, map_mul,
    AlgHom.commutes, zeroScaleInfinityTensorX, zeroScaleNodeInfinityEvaluation_x]
  exact polynomialZeroNodeOverlap_infinity_tangent V c3 c4 c6 r hr I hI hrI hc3 hbot

end FLT.Mazur.WeierstrassModificationX
