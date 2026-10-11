/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothHorizontalConcreteAction
public import FLT.Mazur.WeierstrassSmoothHorizontalLaurentEvaluation
public import FLT.Mazur.WeierstrassHorizontalFractionHomExt

/-!
# Whole affine action maps on the constructed conic residue product

Both genuine output residue maps, composed with the integral action lift,
are exactly Laurent substitutions on the original conic punctures. Equality
holds for every original horizontal fraction function, not only its generators.
-/

@[expose] public noncomputable section
open IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth k : ℕ} (D : SplitNodeDepth W π depth)
  (d : WeierstrassDividedDepth.Data W π k) (hk0 : 0 < k) (hk : 2 * k < depth) (hπ : π ≠ 0)
local notation "K" => ResidueField R
local notation "C" => SmoothHorizontalResidueRing D
local notation "S" => SmoothHorizontalProductRing W (π ^ k)
local notation "e₁" => smoothHorizontalFirstResidue D k hk0 hk hπ
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6
local notation "e₂" => smoothHorizontalSecondResidue D k hk0 hk hπ
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6
local notation "ψ" => smoothHorizontalInput W (π ^ k)
open WeierstrassModificationReesCoordinates WeierstrassModificationX

local notation "H" => HorizontalSourceRing W (π ^ k)
local notation "M" => smoothHorizontalActionLift d
local notation "E₁" => smoothHorizontalFirstOutputResidue D d hk0 hk hπ
local notation "E₂" => smoothHorizontalSecondOutputResidue D d hk0 hk hπ
local notation "τ" => smoothHorizontalTangentUnit D
local notation "z" => smoothHorizontalConicUnit D
local notation "q₁" => smoothHorizontalLaurentEvaluation D (τ * z)
local notation "q₂" => smoothHorizontalLaurentEvaluation D (τ⁻¹ * z)
local notation "f₁" => horizontalConicFirstResidue D k hk0 hk hπ
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6
local notation "f₂" => horizontalConicSecondResidue D k hk0 hk hπ
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6

/-- The actual first residue action is an algebra map on the original horizontal fraction ring. -/
def smoothHorizontalFirstAction : H →ₐ[R] C :=
  { (E₁).comp M with
    commutes' := fun r => by
      change E₁ (M (algebraMap R H r)) = algebraMap R C r
      rw [smoothHorizontalActionLift_coefficient,
        IsScalarTower.algebraMap_apply R S _, smoothHorizontalFirstOutputResidue_base,
        AlgHom.commutes] }

/-- The opposite residue action is an algebra map on the same original fraction ring. -/
def smoothHorizontalSecondAction : H →ₐ[R] C :=
  { (E₂).comp M with
    commutes' := fun r => by
      change E₂ (M (algebraMap R H r)) = algebraMap R C r
      rw [smoothHorizontalActionLift_coefficient,
        IsScalarTower.algebraMap_apply R S _, smoothHorizontalSecondOutputResidue_base,
        AlgHom.commutes] }

/-- Every first-branch function transforms by the product tau times the conic parameter. -/
theorem smoothHorizontalFirstAction_eq :
    smoothHorizontalFirstAction D d hk0 hk hπ = ((q₁).restrictScalars R).comp f₁ := by
  apply horizontalFraction_algHom_ext W (π ^ k) d.b3 d.b4 d.b6
    d.factor3 d.factor4 d.factor6 (pow_ne_zero k hπ)
  · change E₁ (M (horizontalScale W (π ^ k))) = q₁ (f₁ (horizontalScale W (π ^ k)))
    rw [horizontalConicFirstResidue_scale, smoothHorizontalLaurentEvaluation_first]
    exact smoothHorizontalFirstOutputResidue_scale D d hk0 hk hπ
  · change E₁ (M (horizontalVertical W (π ^ k))) = q₁ (f₁ (horizontalVertical W (π ^ k)))
    rw [horizontalConicFirstResidue_slope, map_zero]
    exact (smoothHorizontalFirstOutputResidue_action D d hk0 hk hπ).2

/-- Every opposite-branch function transforms by the inverse smooth character. -/
theorem smoothHorizontalSecondAction_eq :
    smoothHorizontalSecondAction D d hk0 hk hπ = ((q₂).restrictScalars R).comp f₂ := by
  apply horizontalFraction_algHom_ext W (π ^ k) d.b3 d.b4 d.b6
    d.factor3 d.factor4 d.factor6 (pow_ne_zero k hπ)
  · change E₂ (M (horizontalScale W (π ^ k))) = q₂ (f₂ (horizontalScale W (π ^ k)))
    rw [horizontalConicSecondResidue_scale, smoothHorizontalLaurentEvaluation_second]
    exact smoothHorizontalSecondOutputResidue_scale D d hk0 hk hπ
  · change E₂ (M (horizontalVertical W (π ^ k))) = q₂ (f₂ (horizontalVertical W (π ^ k)))
    rw [horizontalConicSecondResidue_slope, map_neg, smoothHorizontalLaurentEvaluation_C]
    exact (smoothHorizontalSecondOutputResidue_action D d hk0 hk hπ).2

end FLT.Mazur.WeierstrassIntegralChart
