/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXDepthTensorOverlap

/-!
# Normalization of the original integral incidence functions

The actual coefficient map on the integral principal open keeps its unit
and inverse under residue normalization. This fixes the two integral
coordinate substitutions without expanding tensor multiplication.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "c" => residue R b6
local notation "t" => coord W (π ^ k) π b3 b4 b6 0
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 K
local notation "e" => residueMiddleOpenEquiv D k hk0 hk b3 b4 b6 h3 h4
local notation "f" => PrincipalOpenTensor.coefficient (R := R) K t
local notation "a" => xOpenUnit W (π ^ k) π b3 b4 b6
local notation "a₀" => xOpenUnit W₀ 0 0 0 0 c

/-- Integral incidence coordinates normalize through the actual tensor restriction. -/
theorem residueIntegralNormalization_coord (i : Fin 3) :
    e (f (algebraMap _ _ (coord W (π ^ k) π b3 b4 b6 i))) =
      algebraMap _ (XOpen W₀ 0 0 0 0 c) (coord W₀ 0 0 0 0 c i) := by
  rw [PrincipalOpenTensor.coefficient_base]
  change e (algebraMap T _ (tensorCoord W (π ^ k) π b3 b4 b6 K i)) = _
  rw [residueMiddleOpenEquiv, PrincipalOpenTransport.equiv_base,
    residueRetainedFiberEquiv_coord]

/-- The original integral incidence unit becomes exactly the normalized incidence unit. -/
theorem residueIntegralNormalization_unit : e (f (↑a)) = (↑a₀ : XOpen W₀ 0 0 0 0 c) := by
  rw [xOpenUnit_val, residueIntegralNormalization_coord, xOpenUnit_val]

/-- Its inverse also survives the actual tensor comparison unchanged. -/
theorem residueIntegralNormalization_inverse :
    e (f (↑a⁻¹)) = (↑a₀⁻¹ : XOpen W₀ 0 0 0 0 c) := by
  apply map_inverse_unit
    (RingHom.comp (AlgHom.toRingHom (AlgEquiv.toAlgHom e)) (AlgHom.toRingHom f)) a a₀⁻¹
  change e (f (↑a)) = (↑a₀ : XOpen W₀ 0 0 0 0 c)
  exact residueIntegralNormalization_unit D k hk0 hk b3 b4 b6 h3 h4

/-- The tensor base change of the integral horizontal substitution has the normalized value. -/
theorem residueIntegralTransition_normalized_x :
    e (residueIntegralTransition W π k b3 b4 b6
      (algebraMap (WeierstrassDilatation.ScalarExtension W (π ^ (k + 1)) b3 b4 b6 K) _
        (WeierstrassDilatation.tensorX W (π ^ (k + 1)) b3 b4 b6 K))) =
      (↑a₀⁻¹ : XOpen W₀ 0 0 0 0 c) := by
  rw [show algebraMap _ (ResidueDividedOpen (W := W) (π := π) k b3 b4 b6)
      (WeierstrassDilatation.tensorX W (π ^ (k + 1)) b3 b4 b6 K) =
    PrincipalOpenTensor.coefficient (R := R) K
      (WeierstrassDilatation.x W (π ^ (k + 1)) b3 b4 b6)
      (algebraMap _ _ (WeierstrassDilatation.x W (π ^ (k + 1)) b3 b4 b6)) from
        (PrincipalOpenTensor.coefficient_base _ _ _).symm]
  rw [residueIntegralTransition_coefficient, depthOverlapEquiv_x]
  exact residueIntegralNormalization_inverse D k hk0 hk b3 b4 b6 h3 h4

/-- The vertical integral substitution retains the normalized slope/incidence quotient. -/
theorem residueIntegralTransition_normalized_y :
    e (residueIntegralTransition W π k b3 b4 b6
      (algebraMap (WeierstrassDilatation.ScalarExtension W (π ^ (k + 1)) b3 b4 b6 K) _
        (WeierstrassDilatation.tensorY W (π ^ (k + 1)) b3 b4 b6 K))) =
      (↑a₀⁻¹ : XOpen W₀ 0 0 0 0 c) * algebraMap _ _ (coord W₀ 0 0 0 0 c 1) := by
  rw [show algebraMap _ (ResidueDividedOpen (W := W) (π := π) k b3 b4 b6)
      (WeierstrassDilatation.tensorY W (π ^ (k + 1)) b3 b4 b6 K) =
    PrincipalOpenTensor.coefficient (R := R) K
      (WeierstrassDilatation.x W (π ^ (k + 1)) b3 b4 b6)
      (algebraMap _ _ (WeierstrassDilatation.y W (π ^ (k + 1)) b3 b4 b6)) from
        (PrincipalOpenTensor.coefficient_base _ _ _).symm]
  rw [residueIntegralTransition_coefficient, depthOverlapEquiv_y, map_mul, map_mul,
    residueIntegralNormalization_inverse, residueIntegralNormalization_coord]

end FLT.Mazur.WeierstrassSuccessiveX
