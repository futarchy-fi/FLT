/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegralWeierstrassAuxiliaryLevel
public import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# A two-chart coefficient cover retaining characteristic two

The principal opens D(2) and D(3) cover the actual discriminant-only coefficient
scheme. The latter chart retains an explicit characteristic-two specialization.
This is coefficient coverage; auxiliary-basis and original-family coverage remain separate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.IntegralWeierstrassParameter

/-- The two coefficients whose principal opens cover every characteristic. -/
def characteristicFactor : Fin 2 → SmoothRing := ![2, 3]

/-- The two characteristic denominators generate the unit ideal. -/
theorem characteristicFactor_span : Ideal.span (Set.range characteristicFactor) = ⊤ := by
  apply Ideal.eq_top_of_isUnit_mem _ (x := (1 : SmoothRing)) _ isUnit_one
  have h₂ : (2 : SmoothRing) ∈ Ideal.span (Set.range characteristicFactor) :=
    Ideal.subset_span ⟨0, rfl⟩
  have h₃ : (3 : SmoothRing) ∈ Ideal.span (Set.range characteristicFactor) :=
    Ideal.subset_span ⟨1, rfl⟩
  convert (Ideal.span (Set.range characteristicFactor)).sub_mem h₃ h₂ using 1
  ring

/-- Actual affine charts away from two and away from three cover the integral coefficient scheme. -/
def characteristicCover : parameterBase.AffineOpenCover :=
  Scheme.affineOpenCoverOfSpanRangeEqTop characteristicFactor characteristicFactor_span

/-- The coefficient ring of the chart which will carry odd auxiliary level. -/
abbrev OddChartRing := Localization.Away (3 : SmoothRing)

/-- Three is invertible on the odd auxiliary coefficient chart. -/
theorem oddChart_three_isUnit : IsUnit (3 : OddChartRing) := by
  simpa only [map_ofNat] using
    (IsLocalization.Away.algebraMap_isUnit (3 : SmoothRing) :
      IsUnit (algebraMap SmoothRing OddChartRing 3))

/-- The actual universal equation on the odd auxiliary coefficient chart. -/
def oddChartEquation : WeierstrassCurve OddChartRing :=
  smoothEquation.map (algebraMap SmoothRing OddChartRing)

/-- The odd chart retains unit discriminant over its original coefficient ring. -/
theorem oddChart_discriminant : IsUnit oddChartEquation.Δ := by
  rw [oddChartEquation, WeierstrassCurve.map_Δ]
  exact smoothEquation_discriminant.map _

/-- The characteristic-two specialization extends to the chart where three is invertible. -/
def oddChartCharacteristicTwo : OddChartRing →+* ZMod 2 :=
  IsLocalization.Away.lift (3 : SmoothRing)
    (show IsUnit (characteristicTwoMap 3) by
      rw [map_ofNat]
      rw [show (3 : ZMod 2) = 1 by decide]
      exact isUnit_one)

/-- The odd-chart characteristic-two point retains the original cubic equation. -/
theorem oddChartCharacteristicTwo_equation :
    oddChartEquation.map oddChartCharacteristicTwo = characteristicTwoEquation := by
  rw [oddChartEquation, WeierstrassCurve.map_map]
  convert characteristicTwo_specialization using 2
  exact IsLocalization.Away.lift_comp _ _

end FLT.Mazur.IntegralWeierstrassParameter
