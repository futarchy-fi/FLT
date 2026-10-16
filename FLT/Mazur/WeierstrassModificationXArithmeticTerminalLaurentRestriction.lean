/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationTensorRingHomExt
public import FLT.Mazur.WeierstrassModificationXArithmeticLaurentRestriction
public import FLT.Mazur.WeierstrassModificationXTensorTerminalCoordinates

/-!
# Original terminal Laurent boundaries commute with arithmetic restriction

Both Boolean labels preserve the full cubic evaluation. The horizontal
coordinate is the positive original Laurent parameter at every order.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (R : Type u) [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6) (opposite : Bool)
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)
local notation "f" => (AlgHom.toRingHom (restriction R π m))
local notation "v₁" => arithmeticInitialLaurentSlope π (m + 1) W s b3 b4 b6
  ha hs h2 h3 h4 h6 opposite
local notation "v₀" => arithmeticInitialLaurentSlope π m W s b3 b4 b6
  ha hs h2 h3 h4 h6 opposite
local notation "hv₁" => arithmeticInitialLaurentSlope_equation π (m + 1) W s b3 b4 b6
  ha hs h2 h3 h4 h6 opposite
local notation "hv₀" => arithmeticInitialLaurentSlope_equation π m W s b3 b4 b6
  ha hs h2 h3 h4 h6 opposite
local notation "G₁" => tensorInitialTerminalLaurent W s b3 b4 b6 Q₁ v₁ hv₁
local notation "G₀" => tensorInitialTerminalLaurent W s b3 b4 b6 Q₀ v₀ hv₀
local notation "T" => WeierstrassDilatation.arithmeticTerminalTensorMap
  R π m W s b3 b4 b6

attribute [local irreducible] tensorInitialTerminalLaurent arithmeticInitialLaurentSlope

/-- The full original terminal boundary retains coefficients, cubic and Boolean label. -/
theorem arithmeticInitialTerminalLaurent_restriction :
    (PolygonScalingNaturality.coeffMap f).comp (G₁).toRingHom =
      (G₀).toRingHom.comp (T).toRingHom := by
  apply WeierstrassDilatation.tensor_coefficient_ringHom_ext
  · intro a
    change PolygonScalingNaturality.coeffMap f (G₁ (algebraMap Q₁ _ a)) =
      G₀ (T (algebraMap Q₁ _ a))
    exact (congrArg (PolygonScalingNaturality.coeffMap f) ((G₁).commutes a)).trans
      ((PolygonScalingNaturality.coeffMap_C f a).trans
        ((congrArg G₀ (WeierstrassDilatation.arithmeticTerminalTensorMap_scalar
          R π m W s b3 b4 b6 a)).trans ((G₀).commutes (f a))).symm)
  · change PolygonScalingNaturality.coeffMap f
      (G₁ ((1 : Q₁) ⊗ₜ[R] WeierstrassDilatation.x W s b3 b4 b6)) =
        G₀ (T ((1 : Q₁) ⊗ₜ[R] WeierstrassDilatation.x W s b3 b4 b6))
    rw [WeierstrassDilatation.arithmeticTerminalTensorMap_tmul, map_one,
      tensorInitialTerminalLaurent_x, tensorInitialTerminalLaurent_x,
      PolygonScalingNaturality.coeffMap_T_one]
  · change PolygonScalingNaturality.coeffMap f
      (G₁ ((1 : Q₁) ⊗ₜ[R] WeierstrassDilatation.y W s b3 b4 b6)) =
        G₀ (T ((1 : Q₁) ⊗ₜ[R] WeierstrassDilatation.y W s b3 b4 b6))
    rw [WeierstrassDilatation.arithmeticTerminalTensorMap_tmul, map_one,
      tensorInitialTerminalLaurent_y, tensorInitialTerminalLaurent_y, map_mul,
      PolygonScalingNaturality.coeffMap_T_one, arithmeticInitialLaurentSlope_restriction]

end FLT.Mazur.WeierstrassModificationX
