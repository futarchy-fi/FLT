/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXZeroConicBoundary
public import FLT.Mazur.WeierstrassSuccessiveXDepthTensorOverlap
public import FLT.Mazur.WeierstrassSuccessiveXResidueConicBoundaryCoordinates

/-!
# Zero-stage normalization of the original integral boundary functions

The scale-one normalization preserves the integral incidence unit and slope.
Consequently the original divided coordinates restrict to t inverse and v/t.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (k : ℕ) (hk0 : k = 0) (hk : 2 * (k + 1) ≤ depth) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "c" => residue R b6
local notation "B" => MiddleConicOpen W₀ c
local notation "C₀" => ConicCoordinate (WeierstrassCurve.a₁ W₀) c
local notation "t" => coord W (π ^ k) π b3 b4 b6 0
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 K
local notation "e" => zeroResidueConicOpenEquiv D k hk0 hk b3 b4 b6 h3 h4
local notation "f" => PrincipalOpenTensor.coefficient (R := R) K t
local notation "a" => xOpenUnit W (π ^ k) π b3 b4 b6
local notation "a₀" => conicBoundaryUnit W₀ c

/-- The original integral incidence coordinate keeps its conic value at scale one. -/
theorem zeroConicIntegralNormalization_t :
    e (f (algebraMap _ _ t)) = algebraMap C₀ B (conicT (WeierstrassCurve.a₁ W₀) c) := by
  rw [PrincipalOpenTensor.coefficient_base]
  change e (algebraMap T _ (tensorCoord W (π ^ k) π b3 b4 b6 K 0)) = _
  rw [zeroResidueConicOpenEquiv_base, zeroResidueFiberEquiv_t, fiberConicMap_t]
  rfl

/-- The original integral slope retains its orientation at scale one. -/
theorem zeroConicIntegralNormalization_v :
    e (f (algebraMap _ _ (coord W (π ^ k) π b3 b4 b6 1))) =
      algebraMap C₀ B (conicV (WeierstrassCurve.a₁ W₀) c) := by
  rw [PrincipalOpenTensor.coefficient_base]
  change e (algebraMap T _ (tensorCoord W (π ^ k) π b3 b4 b6 K 1)) = _
  rw [zeroResidueConicOpenEquiv_base, zeroResidueFiberEquiv_v, fiberConicMap_v]
  rfl

/-- The integral incidence unit is the original conic boundary unit. -/
theorem zeroConicIntegralNormalization_unit : e (f (↑a)) = (↑a₀ : B) := by
  rw [xOpenUnit_val, zeroConicIntegralNormalization_t, conicBoundaryUnit_val]

/-- The inverse unit also survives without changing the original transition. -/
theorem zeroConicIntegralNormalization_inverse : e (f (↑a⁻¹)) = (↑a₀⁻¹ : B) := by
  apply map_inverse_unit
    (RingHom.comp (AlgHom.toRingHom (AlgEquiv.toAlgHom e)) (AlgHom.toRingHom f)) a a₀⁻¹
  exact zeroConicIntegralNormalization_unit D k hk0 hk b3 b4 b6 h3 h4

local notation "U" => WeierstrassDilatation.ScalarExtension W (π ^ (k + 1)) b3 b4 b6 K
local notation "x" => WeierstrassDilatation.x W (π ^ (k + 1)) b3 b4 b6
local notation "y" => WeierstrassDilatation.y W (π ^ (k + 1)) b3 b4 b6
local notation "tx" => WeierstrassDilatation.tensorX W (π ^ (k + 1)) b3 b4 b6 K
local notation "ty" => WeierstrassDilatation.tensorY W (π ^ (k + 1)) b3 b4 b6 K
local notation "m" => residueIntegralTransition W π k b3 b4 b6

/-- The actual integral horizontal substitution has the reciprocal conic incidence value. -/
theorem zeroConicIntegralTransition_x :
    e (m (algebraMap U _ tx)) = (↑a₀⁻¹ : B) := by
  rw [show algebraMap U (ResidueDividedOpen (W := W) (π := π) k b3 b4 b6) tx =
    PrincipalOpenTensor.coefficient (R := R) K x (algebraMap _ _ x) from
      (PrincipalOpenTensor.coefficient_base _ _ _).symm]
  rw [residueIntegralTransition_coefficient, depthOverlapEquiv_x]
  exact zeroConicIntegralNormalization_inverse D k hk0 hk b3 b4 b6 h3 h4

/-- The actual vertical substitution keeps the original slope divided by incidence. -/
theorem zeroConicIntegralTransition_y :
    e (m (algebraMap U _ ty)) =
      (↑a₀⁻¹ : B) * algebraMap C₀ B (conicV (WeierstrassCurve.a₁ W₀) c) := by
  rw [show algebraMap U (ResidueDividedOpen (W := W) (π := π) k b3 b4 b6) ty =
    PrincipalOpenTensor.coefficient (R := R) K x (algebraMap _ _ y) from
      (PrincipalOpenTensor.coefficient_base _ _ _).symm]
  rw [residueIntegralTransition_coefficient, depthOverlapEquiv_y, map_mul, map_mul,
    zeroConicIntegralNormalization_inverse, zeroConicIntegralNormalization_v]

end FLT.Mazur.WeierstrassSuccessiveX
