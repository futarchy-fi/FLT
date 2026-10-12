/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearScaleOneHorizontal
public import FLT.Mazur.WeierstrassDividedPreviousBoundaryAlgebra
public import FLT.Mazur.WeierstrassModificationXTensorOverlapCoordinates

/-!
# Canonical slope formulas on the original initial common boundary

Transport the full parameter-corrected tensor boundary to the slope line.
The first retained and initial projections retain their original functions.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (d : Data W π 0) (e : Data W π (0 + 1))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S e.b3 = 0) (h4 : algebraMap R S e.b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "a" => WeierstrassCurve.a₁ (rootShearCurve (W.map (algebraMap R S)) r)
local notation "P" => SlopeOpen a
local notation "A" => WeierstrassDilatation.Coordinate W (π ^ 0) d.b3 d.b4 d.b6
local notation "T" => S ⊗[R] A
local notation "x" => WeierstrassDilatation.x W (π ^ 0) d.b3 d.b4 d.b6
local notation "y" => WeierstrassDilatation.y W (π ^ 0) d.b3 d.b4 d.b6
local notation "tx" => (1 : S) ⊗ₜ[R] x
local notation "O" => Localization.Away tx
local notation "u" => coord W (π ^ 0) π e.b3 e.b4 e.b6 2
local notation "hs" => (by simp : algebraMap R S (π ^ 0) = 1)
local notation "B" => PrincipalOpenTensor.transition S x u (previousBoundaryEquiv hπ d e)
local notation "H" => tensorShearScaleOneHorizontalEquiv W (π ^ 0) π
  e.b3 e.b4 e.b6 S r hs hp h3 h4 hr

/-- The entire initial common boundary is the canonical punctured slope line. -/
def coefficientShearInitialSlopeBoundaryEquiv : O ≃ₐ[S] P := (B).trans H

local notation "E" => coefficientShearInitialSlopeBoundaryEquiv hπ d e S r hp h3 h4 hr

/-- The original horizontal cubic function is the product of the two sheared slopes. -/
theorem coefficientShearInitialSlopeBoundary_x :
    E (algebraMap T O tx) = slopeZ a * (slopeZ a + algebraMap S P a) := by
  change H (B (algebraMap T O tx)) = _
  rw [← PrincipalOpenTensor.coefficient_base, PrincipalOpenTensor.transition_coefficient,
    previousBoundaryEquiv_base]
  simp only [WeierstrassDilatation.parameterEquiv_x, fromDivided_x]
  rw [PrincipalOpenTensor.coefficient_base]
  exact tensorShearScaleOneHorizontalEquiv_coord W (π ^ 0) π e.b3 e.b4 e.b6
    S r hs hp h3 h4 hr 2

/-- The original vertical function keeps the actual tangent-root shift. -/
theorem coefficientShearInitialSlopeBoundary_y :
    E (algebraMap T O ((1 : S) ⊗ₜ[R] y)) =
      (slopeZ a * (slopeZ a + algebraMap S P a)) *
        (slopeZ a + algebraMap S P r) := by
  change H (B (algebraMap T O ((1 : S) ⊗ₜ[R] y))) = _
  rw [← PrincipalOpenTensor.coefficient_base, PrincipalOpenTensor.transition_coefficient,
    previousBoundaryEquiv_base]
  simp only [WeierstrassDilatation.parameterEquiv_y, fromDivided_y]
  rw [PrincipalOpenTensor.coefficient_base]
  have ht : (1 : S) ⊗ₜ[R]
      (coord W (π ^ 0) π e.b3 e.b4 e.b6 2 * coord W (π ^ 0) π e.b3 e.b4 e.b6 1) =
      ((1 : S) ⊗ₜ[R] coord W (π ^ 0) π e.b3 e.b4 e.b6 2) *
        ((1 : S) ⊗ₜ[R] coord W (π ^ 0) π e.b3 e.b4 e.b6 1) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [ht, map_mul, map_mul]
  change H (algebraMap _ _ (tensorCoord W (π ^ 0) π e.b3 e.b4 e.b6 S 2)) *
    H (algebraMap _ _ (tensorCoord W (π ^ 0) π e.b3 e.b4 e.b6 S 1)) = _
  rw [tensorShearScaleOneHorizontalEquiv_coord, tensorShearScaleOneHorizontalEquiv_coord]
  rfl

/-- The original inverse horizontal function becomes the canonical inverse slope product. -/
theorem coefficientShearInitialSlopeBoundary_inverse :
    E (IsLocalization.Away.invSelf (S := O) tx) = slopeInv a := by
  apply ((slope_units a).1.mul (slope_units a).2.1).mul_left_cancel
  rw [← coefficientShearInitialSlopeBoundary_x hπ d e S r hp h3 h4 hr,
    ← map_mul, IsLocalization.Away.mul_invSelf, map_one,
    coefficientShearInitialSlopeBoundary_x, slope_mul_inv]

local notation "I" => WeierstrassModificationX.Coordinate W (π ^ 0) d.b3 d.b4 d.b6
local notation "t" => WeierstrassModificationX.t W (π ^ 0) d.b3 d.b4 d.b6
local notation "v" => WeierstrassModificationX.v W (π ^ 0) d.b3 d.b4 d.b6
local notation "J" => PrincipalOpenTensor.transition S x t
  (overlapEquiv W (π ^ 0) d.b3 d.b4 d.b6)

/-- The initial projection has exactly its canonical inverse-product incidence. -/
theorem coefficientShearInitialSlopeBoundary_t :
    E ((J).symm (algebraMap (S ⊗[R] I) _ ((1 : S) ⊗ₜ[R] t))) = slopeInv a := by
  rw [tensorOverlap_symm_t, coefficientShearInitialSlopeBoundary_inverse]

/-- The initial projection has exactly its canonical slope with the original root shift. -/
theorem coefficientShearInitialSlopeBoundary_v :
    E ((J).symm (algebraMap (S ⊗[R] I) _ ((1 : S) ⊗ₜ[R] v))) =
      slopeZ a + algebraMap S P r := by
  rw [tensorOverlap_symm_v, map_mul, coefficientShearInitialSlopeBoundary_inverse,
    coefficientShearInitialSlopeBoundary_y, ← mul_assoc, mul_comm (slopeInv a),
    slope_mul_inv, one_mul]

end FLT.Mazur.WeierstrassDividedDepth
