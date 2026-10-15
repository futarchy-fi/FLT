/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveArithmeticSlopeRestriction

/-!
# Retractions on the original arithmetic node charts

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

/-- Arithmetic restriction retains the named coordinates over the lower quotient. -/
theorem arithmeticCoefficientRingMap_coord (i : Fin 3) :
    coefficientRingMap f (W.map q₁) (q₁ s) (q₁ π) (q₁ b3) (q₁ b4) (q₁ b6)
      (coord (W.map q₁) (q₁ s) (q₁ π) (q₁ b3) (q₁ b4) (q₁ b6) i) =
        coord (W.map q₀) (q₀ s) (q₀ π) (q₀ b3) (q₀ b4) (q₀ b6) i :=
  coefficientRingMap_coord f (W.map q₁) (q₁ s) (q₁ π) (q₁ b3) (q₁ b4) (q₁ b6) i

/-- Constants use the original quotient map and the lower arithmetic algebra structure. -/
theorem arithmeticCoefficientRingMap_algebraMap (r : Q₁) :
    coefficientRingMap f (W.map q₁) (q₁ s) (q₁ π) (q₁ b3) (q₁ b4) (q₁ b6)
      (algebraMap Q₁ _ r) =
        algebraMap Q₀ (ExtendedCoordinate W s π b3 b4 b6 Q₀) (f r) :=
  coefficientRingMap_algebraMap f (W.map q₁) (q₁ s) (q₁ π)
    (q₁ b3) (q₁ b4) (q₁ b6) r

variable (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)

local notation "e₁" => nilpotentNodeRetraction (W.map q₁) (q₁ s) (q₁ π)
  (q₁ b3) (q₁ b4) (q₁ b6) (ideal Q₁ (parameter R π (m + 1)))
  (arithmeticParameterIdeal_nilpotent π (m + 1)) (ha.map q₁)
  (arithmeticCoefficient_mem π (m + 1) hs) (arithmeticCoefficient_mem π (m + 1) h2)
  (arithmeticCoefficient_mem π (m + 1) h3) (arithmeticCoefficient_mem π (m + 1) h4)
  (arithmeticCoefficient_mem π (m + 1) h6)
local notation "e₀" => nilpotentNodeRetraction (W.map q₀) (q₀ s) (q₀ π)
  (q₀ b3) (q₀ b4) (q₀ b6) (ideal Q₀ (parameter R π m))
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q₀)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
  (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
  (arithmeticCoefficient_mem π m h6)

/-- Restriction preserves the original arithmetic retraction on all three coordinates. -/
theorem arithmeticNodeRetraction_restriction :
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
    simp only [nilpotentNodeRetraction_coord]
    fin_cases i
    · exact SuccessiveIncidence.coefficientRingMap_t f (q₁ π)
    · exact arithmeticNodeSlope_restriction R π m W s b3 b4 b6 ha hs h2 h3 h4 h6
    · exact SuccessiveIncidence.coefficientRingMap_u f (q₁ π)

end FLT.Mazur.WeierstrassSuccessiveX
