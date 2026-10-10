/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicBoundaryParameters
public import FLT.Mazur.WeierstrassSuccessiveXTerminalLaurentSmooth

/-!
# The original terminal Laurent coordinate in both ordered conic parameters

The full finite-model boundary map sends the Laurent generator to c*z₁,
whose inverse is z₂. These identities include scale one and retain the
original residue-field coefficient structure.
-/

@[expose] public noncomputable section
open IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
  (h6 : W.a₆ = (π ^ (k + 1)) ^ 2 * b6) (hp : 2 * (k + 1) = n)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "a" => WeierstrassCurve.a₁ W₀
local notation "c" => residue R b6
local notation "C₀" => ConicCoordinate a c
local notation "B" => MiddleConicOpen W₀ c
local notation "hc" => laurentConicComponent_constant_isUnit D k b6 h6 hp
local notation "ψ" => residueLaurentConicMap D k hk b3 b4 b6 h3 h4 h6 hp
local notation "z₁" => conicIncidenceFirstParameter a c hc
local notation "z₂" => conicIncidenceSecondParameter a c hc

omit [IsDomain R] in
/-- The actual incidence-unit inverse is the canonical localization inverse. -/
theorem conicBoundaryUnit_invSelf :
    (↑(conicBoundaryUnit W₀ c)⁻¹ : B) = IsLocalization.Away.invSelf (conicT a c) := by
  apply (IsLocalization.Away.algebraMap_isUnit (S := B) (conicT a c)).mul_left_cancel
  rw [← conicBoundaryUnit_val W₀ c, Units.mul_inv]
  rw [conicBoundaryUnit_val, IsLocalization.Away.mul_invSelf]

/-- The original terminal map pulls back the Laurent generator to the actual slope v/t. -/
theorem residueLaurentConicMap_incidenceSlope :
    ψ (LaurentPolynomial.T 1) = conicIncidenceSlope a c := by
  rw [residueLaurentConicMap_parameter, conicBoundaryUnit_invSelf]
  rfl

/-- The Laurent coordinate is c times the original first ordered conic parameter. -/
theorem residueLaurentConicMap_firstParameter :
    ψ (LaurentPolynomial.T 1) = algebraMap K B c * z₁ := by
  rw [residueLaurentConicMap_incidenceSlope, conicIncidenceSlope_first]

/-- The Laurent coordinate is reciprocal to the original second ordered parameter. -/
theorem residueLaurentConicMap_secondParameter : ψ (LaurentPolynomial.T 1) * z₂ = 1 := by
  rw [residueLaurentConicMap_incidenceSlope, conicIncidenceSlope_second]

/-- The inverse Laurent generator is exactly the original second parameter. -/
theorem residueLaurentConicMap_inverseParameter : ψ (LaurentPolynomial.T (-1)) = z₂ := by
  have hu : IsUnit (ψ (LaurentPolynomial.T 1)) :=
    (LaurentPolynomial.isUnit_T 1).map ψ
  apply hu.mul_left_cancel
  rw [← map_mul, ← LaurentPolynomial.T_add, show (1 : ℤ) + -1 = 0 from rfl,
    LaurentPolynomial.T_zero, map_one, residueLaurentConicMap_secondParameter]

end FLT.Mazur.WeierstrassSuccessiveX
