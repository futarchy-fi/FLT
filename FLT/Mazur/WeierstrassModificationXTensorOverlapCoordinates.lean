/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXLocalization
public import FLT.Mazur.PrincipalOpenTensorTransition

/-!
# Original incidence and slope through the tensor overlap

The reverse integral transition retains t = 1/x and v = y/x after arbitrary
coefficient extension, on the actual localized tensor algebras.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type*) [CommRing S] [Algebra R S]
local notation "A" => Coordinate W s b3 b4 b6
local notation "B" => WeierstrassDilatation.Coordinate W s b3 b4 b6
local notation "x" => WeierstrassDilatation.x W s b3 b4 b6
local notation "y" => WeierstrassDilatation.y W s b3 b4 b6
local notation "t₀" => t W s b3 b4 b6
local notation "v₀" => v W s b3 b4 b6
local notation "tx" => (1 : S) ⊗ₜ[R] x
local notation "T₀" => S ⊗[R] A
local notation "B₀" => S ⊗[R] B
local notation "Q" => Localization.Away tx
local notation "e" => PrincipalOpenTensor.transition S x t₀ (overlapEquiv W s b3 b4 b6)

/-- The original divided unit has the usual inverse in the actual tensor localization. -/
theorem tensor_dividedOpenUnit_inverse :
    PrincipalOpenTensor.coefficient S x (↑(dividedOpenUnit W s b3 b4 b6)⁻¹) =
      IsLocalization.Away.invSelf (S := Q) tx := by
  apply (IsLocalization.Away.algebraMap_isUnit (S := Q) tx).mul_left_cancel
  rw [← PrincipalOpenTensor.coefficient_base,
    ← dividedOpenUnit_val, ← map_mul, Units.mul_inv, map_one]
  rw [dividedOpenUnit_val, PrincipalOpenTensor.coefficient_base]
  exact (IsLocalization.Away.mul_invSelf (S := Q) tx).symm

/-- The tensor reverse transition preserves the complete original coordinate restriction. -/
theorem tensorOverlap_symm_base (z : A) :
    (e).symm (algebraMap T₀ _ ((1 : S) ⊗ₜ[R] z)) =
      PrincipalOpenTensor.coefficient S x (xToDividedOpen W s b3 b4 b6 z) := by
  rw [← PrincipalOpenTensor.coefficient_base, PrincipalOpenTensor.transition_symm_coefficient]
  change PrincipalOpenTensor.coefficient S x
    (overlapBackward W s b3 b4 b6 (algebraMap A _ z)) = _
  rw [overlapBackward_base]

/-- The original incidence is exactly the inverse divided tensor coordinate. -/
theorem tensorOverlap_symm_t :
    (e).symm (algebraMap T₀ _ ((1 : S) ⊗ₜ[R] t₀)) =
      IsLocalization.Away.invSelf (S := Q) tx := by
  rw [tensorOverlap_symm_base, xToDividedOpen, xOverlapMap_t,
    tensor_dividedOpenUnit_inverse]

/-- The original slope is exactly the original vertical coordinate divided by x. -/
theorem tensorOverlap_symm_v :
    (e).symm (algebraMap T₀ _ ((1 : S) ⊗ₜ[R] v₀)) =
      IsLocalization.Away.invSelf (S := Q) tx * algebraMap B₀ Q ((1 : S) ⊗ₜ[R] y) := by
  rw [tensorOverlap_symm_base, xToDividedOpen, xOverlapMap_v, map_mul,
    tensor_dividedOpenUnit_inverse]
  congr 1
  exact PrincipalOpenTensor.coefficient_base S x y

end FLT.Mazur.WeierstrassModificationX
