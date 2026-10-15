/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveTensorLaurentCoordinates
public import FLT.Mazur.WeierstrassDividedPreviousBoundaryAlgebra
public import FLT.Mazur.WeierstrassSuccessiveXDepthTensorOverlap
public import FLT.Mazur.PrincipalOpenTensorEvaluationExt

/-!
# Full original divided tensor transitions on compatible Laurent slopes

The comparison uses the original divided data, the exact depth power, and
both integral overlap equivalences before coefficient extension.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) (k : ℕ)
  (d : Data W π (k + 1)) (e : Data W π (k + 1 + 1))
  (S : Type u) [CommRing S] [Algebra R S]
  (r₀ r₁ : SuccessiveIncidence.Coordinate (algebraMap R S π))
  (h₀ : r₀ ^ 2 + nodeSlopeLinear (W.map (algebraMap R S))
    (algebraMap R S π) (algebraMap R S d.b3) * r₀ =
    nodeSlopeConstant (W.map (algebraMap R S)) (algebraMap R S (π ^ k))
      (algebraMap R S π) (algebraMap R S d.b4) (algebraMap R S d.b6))
  (h₁ : r₁ ^ 2 + nodeSlopeLinear (W.map (algebraMap R S))
    (algebraMap R S π) (algebraMap R S e.b3) * r₁ =
    nodeSlopeConstant (W.map (algebraMap R S)) (algebraMap R S (π ^ (k + 1)))
      (algebraMap R S π) (algebraMap R S e.b4) (algebraMap R S e.b6))
  (h : inverseLeftIncidenceLaurent (algebraMap R S π) r₀ =
    rightIncidenceLaurent (algebraMap R S π) r₁)
local notation "x" => WeierstrassDilatation.x W (π ^ (k + 1)) d.b3 d.b4 d.b6
local notation "t" => coord W (π ^ k) π d.b3 d.b4 d.b6 0
local notation "u" => coord W (π ^ (k + 1)) π e.b3 e.b4 e.b6 2
local notation "A" => PrincipalOpenTensor.transition S x t
  (depthOverlapEquiv W π k d.b3 d.b4 d.b6)
local notation "B" => PrincipalOpenTensor.transition S x u (previousBoundaryEquiv hπ d e)
local notation "L" => tensorInverseLeftSlopeLaurent W (π ^ k) π d.b3 d.b4 d.b6 S r₀ h₀
local notation "U" => tensorRightSlopeLaurent W (π ^ (k + 1)) π e.b3 e.b4 e.b6 S r₁ h₁

include h in
/-- The actual integral tensor transitions agree on every Laurent branch function. -/
theorem adjacentTensorSlope_transition : (L).comp (A).toAlgHom = (U).comp (B).toAlgHom := by
  let f : Localization.Away x →ₐ[R] S[T;T⁻¹] :=
    (((L).comp (A).toAlgHom).restrictScalars R).comp (PrincipalOpenTensor.coefficient S x)
  let g : Localization.Away x →ₐ[R] S[T;T⁻¹] :=
    (((U).comp (B).toAlgHom).restrictScalars R).comp (PrincipalOpenTensor.coefficient S x)
  have he : f = g := by
    apply IsLocalization.algHom_ext (Submonoid.powers x)
    apply WeierstrassDilatation.hom_ext
    · change L (A (PrincipalOpenTensor.coefficient S x (algebraMap _ _ x))) =
        U (B (PrincipalOpenTensor.coefficient S x (algebraMap _ _ x)))
      rw [PrincipalOpenTensor.transition_coefficient, depthOverlapEquiv_x,
        tensorInverseLeftSlopeLaurent_inverse, PrincipalOpenTensor.transition_coefficient,
        previousBoundaryEquiv_base, WeierstrassDilatation.parameterEquiv_x,
        fromDivided_x, tensorRightSlopeLaurent_coordinate]
    · change L (A (PrincipalOpenTensor.coefficient S x (algebraMap _ _
        (WeierstrassDilatation.y W (π ^ (k + 1)) d.b3 d.b4 d.b6)))) =
        U (B (PrincipalOpenTensor.coefficient S x (algebraMap _ _
          (WeierstrassDilatation.y W (π ^ (k + 1)) d.b3 d.b4 d.b6))))
      rw [PrincipalOpenTensor.transition_coefficient, depthOverlapEquiv_y,
        map_mul, map_mul, tensorInverseLeftSlopeLaurent_inverse,
        tensorInverseLeftSlopeLaurent_slope, PrincipalOpenTensor.transition_coefficient,
        previousBoundaryEquiv_base, WeierstrassDilatation.parameterEquiv_y, fromDivided_y,
        map_mul, map_mul, map_mul, tensorRightSlopeLaurent_coordinate,
        tensorRightSlopeLaurent_slope, h]
  apply PrincipalOpenTensor.evaluation_ext S x
  intro z
  exact DFunLike.congr_fun he z

end FLT.Mazur.WeierstrassDividedDepth
