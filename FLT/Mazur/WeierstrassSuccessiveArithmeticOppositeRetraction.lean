/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveArithmeticRetractionRestriction
public import FLT.Mazur.WeierstrassSuccessiveArithmeticOppositeNodeChart

/-!
# Opposite retractions on the original arithmetic node charts

The constructed retractions commute with the original quotient restriction
on constants and each of the three retained coordinates.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open PolygonArithmeticStages
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (R : Type u) [CommRing R] (π : R) (m : ℕ)
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)
local notation "q₀" => algebraMap R Q₀
local notation "q₁" => algebraMap R Q₁
local notation "f" => (AlgHom.toRingHom (restriction R π m))

variable (W : WeierstrassCurve R) (s b3 b4 b6 : R)

variable (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)

local notation "v₁" => oppositeNodeSlope (W.map q₁) (q₁ s) (q₁ π)
  (q₁ b3) (q₁ b4) (q₁ b6) (ideal Q₁ (parameter R π (m + 1)))
  (arithmeticParameterIdeal_nilpotent π (m + 1)) (ha.map q₁)
  (arithmeticCoefficient_mem π (m + 1) hs) (arithmeticCoefficient_mem π (m + 1) h2)
  (arithmeticCoefficient_mem π (m + 1) h3) (arithmeticCoefficient_mem π (m + 1) h4)
  (arithmeticCoefficient_mem π (m + 1) h6)
local notation "v₀" => oppositeNodeSlope (W.map q₀) (q₀ s) (q₀ π)
  (q₀ b3) (q₀ b4) (q₀ b6) (ideal Q₀ (parameter R π m))
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q₀)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
  (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
  (arithmeticCoefficient_mem π m h6)

local notation "hv₁" => oppositeNodeSlope_equation (W.map q₁) (q₁ s) (q₁ π)
  (q₁ b3) (q₁ b4) (q₁ b6) (ideal Q₁ (parameter R π (m + 1)))
  (arithmeticParameterIdeal_nilpotent π (m + 1)) (ha.map q₁)
  (arithmeticCoefficient_mem π (m + 1) hs) (arithmeticCoefficient_mem π (m + 1) h2)
  (arithmeticCoefficient_mem π (m + 1) h3) (arithmeticCoefficient_mem π (m + 1) h4)
  (arithmeticCoefficient_mem π (m + 1) h6)
local notation "hv₀" => oppositeNodeSlope_equation (W.map q₀) (q₀ s) (q₀ π)
  (q₀ b3) (q₀ b4) (q₀ b6) (ideal Q₀ (parameter R π m))
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q₀)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
  (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
  (arithmeticCoefficient_mem π m h6)

local notation "e₁" => simpleSlopeRetraction (W.map q₁) (q₁ s) (q₁ π)
  (q₁ b3) (q₁ b4) (q₁ b6) v₁ hv₁
local notation "e₀" => simpleSlopeRetraction (W.map q₀) (q₀ s) (q₀ π)
  (q₀ b3) (q₀ b4) (q₀ b6) v₀ hv₀

/-- The opposite arithmetic slope restricts on the same original branch. -/
theorem arithmeticOppositeNodeSlope_restriction :
    SuccessiveIncidence.coefficientRingMap f (q₁ π) v₁ = v₀ := by
  simp only [oppositeNodeSlope, QuadraticRootBranchLocalization.oppositeRoot,
    map_sub, map_neg, arithmeticNodeSlopeLinear_restriction,
    arithmeticNodeSlope_restriction R π m W s b3 b4 b6 ha hs h2 h3 h4 h6]

/-- Restriction preserves the original arithmetic retraction on all three coordinates. -/
theorem arithmeticOppositeNodeRetraction_restriction :
    (SuccessiveIncidence.coefficientRingMap f (q₁ π)).comp (e₁).toRingHom =
      (e₀).toRingHom.comp
        (coefficientRingMap f (W.map q₁) (q₁ s) (q₁ π) (q₁ b3) (q₁ b4) (q₁ b6)) := by
  apply coefficient_ringHom_ext
  · intro r
    change SuccessiveIncidence.coefficientRingMap f (q₁ π) (e₁ (algebraMap Q₁ _ r)) =
      e₀ (coefficientRingMap f (W.map q₁) (q₁ s) (q₁ π) (q₁ b3) (q₁ b4) (q₁ b6)
        (algebraMap Q₁ _ r))
    rw [AlgHom.commutes, arithmeticCoefficientRingMap_algebraMap, AlgHom.commutes,
      SuccessiveIncidence.coefficientRingMap_algebraMap]
    rfl
  · intro i
    change SuccessiveIncidence.coefficientRingMap f (q₁ π)
      (e₁ (coord (W.map q₁) (q₁ s) (q₁ π) (q₁ b3) (q₁ b4) (q₁ b6) i)) =
      e₀ (coefficientRingMap f (W.map q₁) (q₁ s) (q₁ π) (q₁ b3) (q₁ b4) (q₁ b6)
        (coord (W.map q₁) (q₁ s) (q₁ π) (q₁ b3) (q₁ b4) (q₁ b6) i))
    rw [arithmeticCoefficientRingMap_coord]
    simp only [simpleSlopeRetraction_coord]
    fin_cases i
    · exact SuccessiveIncidence.coefficientRingMap_t f (q₁ π)
    · exact arithmeticOppositeNodeSlope_restriction R π m W s b3 b4 b6 ha hs h2 h3 h4 h6
    · exact SuccessiveIncidence.coefficientRingMap_u f (q₁ π)

end FLT.Mazur.WeierstrassSuccessiveX
