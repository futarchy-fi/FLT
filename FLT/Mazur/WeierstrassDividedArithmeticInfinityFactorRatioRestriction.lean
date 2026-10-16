/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioInfinity
public import FLT.Mazur.WeierstrassDividedCanonicalInfinityFactorRatioTransport
public import FLT.Mazur.WeierstrassChartArithmeticRestriction

/-!
# The full infinity comparison at consecutive arithmetic orders

The canonical roots at the two orders are independently constructed. Their
coefficient identity supplies the square for the unchanged full infinity map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX WeierstrassIntegralChart
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s)
  (h2 : π ∣ W.a₂) (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
  (h3a : π ∣ W.a₃) (h4a : π ∣ W.a₄) (h6a : π ∣ W.a₆) (k : ℕ)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "τ" => arithmeticInitialMobiusSmoothing W ha s π m
local notation "hn" => Fact.mk (arithmeticInitialFactorRatioSmoothing_nilpotent W ha s π m hs)
attribute [local irreducible] fullFactorRatioInfinityPolygonMap polynomialSlopeRoot

/-- The complete original infinity comparison follows the actual consecutive quotient map. -/
@[reassoc] theorem arithmeticFactorRatioInfinityPolygonMap_restriction :
    arithmeticFactorRatioInfinityPolygonMap π m W s b3 b4 b6
      ha hs h2 h3 h4 h6 h3a h4a h6a k ≫
        arithmeticFactorRatioPolygonRestriction π m W s ha hs k =
      arithmeticChartRestriction R π m W 1 ≫
        arithmeticFactorRatioInfinityPolygonMap π (m + 1) W s b3 b4 b6
          ha hs h2 h3 h4 h6 h3a h4a h6a k := by
  let _ := hn
  let _ : Fact (IsNilpotent (initialTangentSmoothing (W.map q) (ha.map q) (q s))) := hn
  let _ : Fact (IsNilpotent (arithmeticInitialMobiusSmoothing W ha s π (m + 1))) :=
    ⟨arithmeticInitialFactorRatioSmoothing_nilpotent W ha s π (m + 1) hs⟩
  unfold arithmeticFactorRatioInfinityPolygonMap arithmeticFactorRatioPolygonRestriction
    arithmeticChartRestriction arithmeticChartCoefficientRingMap arithmeticInitialMobiusSmoothing
  let q₁ := algebraMap R (Quotient R π (m + 1))
  let _ : Fact (IsNilpotent (initialTangentSmoothing (W.map q₁) (ha.map q₁) (q₁ s))) :=
    ⟨arithmeticInitialFactorRatioSmoothing_nilpotent W ha s π (m + 1) hs⟩
  apply canonicalFactorRatioInfinityPolygonMap_coefficient_of_eq
  · exact (restriction R π m).commutes s
  · exact (restriction R π m).commutes b3
  · exact (restriction R π m).commutes b4
  · exact (restriction R π m).commutes b6
  · exact arithmeticParameterIdeal_restriction R π m

end FLT.Mazur.WeierstrassDividedDepth
