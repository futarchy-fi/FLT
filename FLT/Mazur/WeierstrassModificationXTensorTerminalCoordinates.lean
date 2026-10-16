/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXTensorTerminalLaurent

/-!
# Exact terminal coordinates on the original initial Laurent boundary

The original terminal coordinates are T and T times the full chosen slope.
These identities precede terminal normalization and keep all corrections.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S]
  (r : S[T;T⁻¹])
  (hr : r ^ 2 + laurentSlopeLinear (W.map (algebraMap R S)) (algebraMap R S b3) * r =
    laurentSlopeConstant (W.map (algebraMap R S)) (algebraMap R S s)
      (algebraMap R S b4) (algebraMap R S b6))
local notation "t₀" => t W s b3 b4 b6
local notation "x" => WeierstrassDilatation.x W s b3 b4 b6
local notation "y" => WeierstrassDilatation.y W s b3 b4 b6
local notation "L" => tensorInitialLaurentLocalization W s b3 b4 b6 S r hr
local notation "G" => tensorInitialTerminalLaurent W s b3 b4 b6 S r hr
local notation "f" => PrincipalOpenTensor.coefficient S t₀
local notation "w" => xOpenUnit W s b3 b4 b6

/-- The original incidence unit evaluates to the reciprocal Laurent parameter. -/
theorem tensorInitialLaurentLocalization_unit : L (f (↑w)) = LaurentPolynomial.T (-1) := by
  rw [xOpenUnit_val, PrincipalOpenTensor.coefficient_base,
    tensorInitialLaurentLocalization_base, tensorLaurentSlopeEvaluation_t]

/-- The inverse incidence unit retains the positive original Laurent parameter. -/
theorem tensorInitialLaurentLocalization_inverse : L (f (↑w⁻¹)) = LaurentPolynomial.T 1 := by
  apply map_inverse_unit ((L).toRingHom.comp (f).toRingHom) w
    (LaurentUnitPoints.pointUnit (AlgHom.id S S[T;T⁻¹]))
  exact tensorInitialLaurentLocalization_unit W s b3 b4 b6 S r hr

/-- The original terminal abscissa is the positive Laurent parameter. -/
theorem tensorInitialTerminalLaurent_x : G ((1 : S) ⊗ₜ[R] x) = LaurentPolynomial.T 1 := by
  change L (PrincipalOpenTensor.transition S x t₀ (overlapEquiv W s b3 b4 b6)
    (algebraMap _ _ ((1 : S) ⊗ₜ[R] x))) = _
  rw [← PrincipalOpenTensor.coefficient_base, PrincipalOpenTensor.transition_coefficient]
  change L (f (overlapForward W s b3 b4 b6 (algebraMap _ _ x))) = _
  rw [overlapForward_base, dividedToXOpen, dividedOverlapMap_x]
  exact tensorInitialLaurentLocalization_inverse W s b3 b4 b6 S r hr

/-- The original terminal ordinate keeps the entire chosen Laurent slope. -/
theorem tensorInitialTerminalLaurent_y : G ((1 : S) ⊗ₜ[R] y) =
    LaurentPolynomial.T 1 * r := by
  change L (PrincipalOpenTensor.transition S x t₀ (overlapEquiv W s b3 b4 b6)
    (algebraMap _ _ ((1 : S) ⊗ₜ[R] y))) = _
  rw [← PrincipalOpenTensor.coefficient_base, PrincipalOpenTensor.transition_coefficient]
  change L (f (overlapForward W s b3 b4 b6 (algebraMap _ _ y))) = _
  rw [overlapForward_base, dividedToXOpen, dividedOverlapMap_y, map_mul, map_mul,
    tensorInitialLaurentLocalization_inverse]
  change _ * L (f (algebraMap _ _ (v W s b3 b4 b6))) = _
  rw [PrincipalOpenTensor.coefficient_base, tensorInitialLaurentLocalization_base,
    tensorLaurentSlopeEvaluation_v]

end FLT.Mazur.WeierstrassModificationX
