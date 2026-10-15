/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SuccessiveIncidenceLaurentRestriction
public import FLT.Mazur.WeierstrassSuccessiveArithmeticOppositeRetraction
public import FLT.Mazur.WeierstrassSuccessiveArithmeticTensorBranches

/-!
# Both full arithmetic branch slopes commute with quotient restriction

The Boolean label is retained before and after evaluating on the original
Laurent boundary. All nilpotent correction terms remain present.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
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
local notation "q₀" => algebraMap R Q₀
local notation "q₁" => algebraMap R Q₁
local notation "f" => (AlgHom.toRingHom (restriction R π m))
local notation "v₁" => arithmeticBranchSlope π (m + 1) W s b3 b4 b6
  ha hs h2 h3 h4 h6 opposite
local notation "v₀" => arithmeticBranchSlope π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite

/-- Either full constructed branch slope retains its label under restriction. -/
theorem arithmeticBranchSlope_restriction :
    SuccessiveIncidence.coefficientRingMap f (q₁ π) v₁ = v₀ := by
  cases opposite
  · exact arithmeticNodeSlope_restriction R π m W s b3 b4 b6 ha hs h2 h3 h4 h6
  · exact arithmeticOppositeNodeSlope_restriction R π m W s b3 b4 b6 ha hs h2 h3 h4 h6

/-- Restriction preserves the full slope on the original Laurent boundary. -/
theorem arithmeticBranchSlope_laurent_restriction :
    PolygonScalingNaturality.coeffMap f
      (PolygonSmoothing.leftLaurentMap (q₁ π) (SuccessiveIncidence.toPolygon (q₁ π) v₁)) =
    PolygonSmoothing.leftLaurentMap (q₀ π) (SuccessiveIncidence.toPolygon (q₀ π) v₀) := by
  rw [SuccessiveIncidence.leftLaurent_coefficientRingMap]
  exact congrArg (fun z ↦ PolygonSmoothing.leftLaurentMap (q₀ π)
    (SuccessiveIncidence.toPolygon (q₀ π) z))
      (arithmeticBranchSlope_restriction R π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite)

end FLT.Mazur.WeierstrassSuccessiveX
