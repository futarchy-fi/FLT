/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveTensorLeftLaurent

/-!
# Original terminal coordinates on the full Laurent boundary

The reciprocal horizontal coordinate and the complete constructed slope
are retained through the actual arithmetic tensor transition.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (π : R)
  (k : ℕ) (b3 b4 b6 : R) (S : Type u) [CommRing S] [Algebra R S]
  (r : SuccessiveIncidence.Coordinate (algebraMap R S π))
  (hr : r ^ 2 + nodeSlopeLinear (W.map (algebraMap R S))
    (algebraMap R S π) (algebraMap R S b3) * r =
    nodeSlopeConstant (W.map (algebraMap R S)) (algebraMap R S (π ^ k))
      (algebraMap R S π) (algebraMap R S b4) (algebraMap R S b6))
local notation "q" => algebraMap R S
local notation "ev" => tensorSlopePolygonRetraction W (π ^ k) π b3 b4 b6 S r hr
local notation "t" => coord W (π ^ k) π b3 b4 b6 0
local notation "T₀" => ScalarExtension W (π ^ k) π b3 b4 b6 S
local notation "x" => WeierstrassDilatation.x W (π ^ (k + 1)) b3 b4 b6
local notation "y" => WeierstrassDilatation.y W (π ^ (k + 1)) b3 b4 b6
local notation "D" => S ⊗[R] WeierstrassDilatation.Coordinate W (π ^ (k + 1)) b3 b4 b6
local notation "a" => depthOverlapEquiv W π k b3 b4 b6
local notation "A" => PrincipalOpenTensor.transition S x t a

local notation "L" => tensorLeftSlopeLaurent W π k b3 b4 b6 S r hr
local notation "f" => PrincipalOpenTensor.coefficient S t
local notation "w" => xOpenUnit W (π ^ k) π b3 b4 b6
local notation "G" => tensorTerminalLaurent W π k b3 b4 b6 S r hr

/-- The original incidence unit restricts to the original positive Laurent parameter. -/
theorem tensorLeftSlopeLaurent_unit : L (f (↑w)) = LaurentPolynomial.T 1 := by
  rw [xOpenUnit_val, PrincipalOpenTensor.coefficient_base]
  change L (algebraMap T₀ _ (tensorCoord W (π ^ k) π b3 b4 b6 S 0)) = _
  rw [tensorLeftSlopeLaurent_base, tensorSlopePolygonRetraction_left,
    PolygonSmoothing.leftLaurentMap_left]

/-- The inverse original incidence restricts to the reciprocal Laurent parameter. -/
theorem tensorLeftSlopeLaurent_inverse : L (f (↑w⁻¹)) = LaurentPolynomial.T (-1) := by
  apply map_inverse_unit ((L).toRingHom.comp (f).toRingHom) w
    (LaurentUnitPoints.pointUnit (AlgHom.id S S[T;T⁻¹]))⁻¹
  exact tensorLeftSlopeLaurent_unit W π k b3 b4 b6 S r hr

/-- The original terminal abscissa is the reciprocal original boundary parameter. -/
theorem tensorTerminalLaurent_x : G ((1 : S) ⊗ₜ[R] x) = LaurentPolynomial.T (-1) := by
  change L (A (algebraMap D _ ((1 : S) ⊗ₜ[R] x))) = _
  rw [← PrincipalOpenTensor.coefficient_base S x x,
    PrincipalOpenTensor.transition_coefficient, depthOverlapEquiv_x]
  exact tensorLeftSlopeLaurent_inverse W π k b3 b4 b6 S r hr

/-- The original terminal ordinate keeps the complete constructed slope on the torus. -/
theorem tensorTerminalLaurent_y : G ((1 : S) ⊗ₜ[R] y) =
    LaurentPolynomial.T (-1) *
      PolygonSmoothing.leftLaurentMap (q π) (SuccessiveIncidence.toPolygon (q π) r) := by
  change L (A (algebraMap D _ ((1 : S) ⊗ₜ[R] y))) = _
  rw [← PrincipalOpenTensor.coefficient_base S x y,
    PrincipalOpenTensor.transition_coefficient, depthOverlapEquiv_y, map_mul, map_mul,
    tensorLeftSlopeLaurent_inverse, PrincipalOpenTensor.coefficient_base]
  change _ * L (algebraMap T₀ _ (tensorCoord W (π ^ k) π b3 b4 b6 S 1)) = _
  rw [tensorLeftSlopeLaurent_base, tensorSlopePolygonRetraction_slope]

end FLT.Mazur.WeierstrassSuccessiveX
