/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXCanonicalFactorRatioTransport
public import FLT.Mazur.WeierstrassModificationXArithmeticInitialNodeRestriction

/-!
# Corrected full polygon charts at consecutive arithmetic orders

The original canonical polynomial roots define the factor-ratio chart at every
quotient order. Its full coefficient square preserves the exact normalized smoothing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (h2 : π ∣ W.a₂) (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)

/-- The actual arithmetic initial node with the corrected factor-ratio polygon coordinates. -/
def arithmeticInitialFactorRatioChart : Spec (.of (PolynomialNodeOpen (W.map q) (q s))) ⟶
    PolygonSmoothing.chart Q (arithmeticInitialMobiusSmoothing W ha s π m) :=
  canonicalFactorRatioChart (W.map q) (ha.map q) (q s) (q b3) (q b4) (q b6) J
    (arithmeticParameterIdeal_nilpotent π m) (arithmeticCoefficient_mem π m h2)
    (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
    (arithmeticCoefficient_mem π m h6)

instance arithmeticInitialFactorRatioChart_isOpenImmersion :
    IsOpenImmersion (arithmeticInitialFactorRatioChart π m W s b3 b4 b6 ha h2 h3 h4 h6) :=
  canonicalFactorRatioChart_isOpenImmersion ..

/-- All original coefficients survive the corrected arithmetic polygon comparison. -/
@[reassoc] theorem arithmeticInitialFactorRatioChart_structure :
    arithmeticInitialFactorRatioChart π m W s b3 b4 b6 ha h2 h3 h4 h6 ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap Q (PolygonSmoothing.ChartRing (arithmeticInitialMobiusSmoothing W ha s π m)))) =
          Spec.map (CommRingCat.ofHom (algebraMap Q (PolynomialNodeOpen (W.map q) (q s)))) :=
  canonicalFactorRatioChart_structure ..

attribute [local irreducible] canonicalFactorRatioChart

/-- The corrected entire initial chart follows the actual consecutive arithmetic quotient map. -/
@[reassoc] theorem arithmeticInitialFactorRatioChart_restriction :
    arithmeticFullInitialNodeQuotient R π m W s ≫
      arithmeticInitialFactorRatioChart π (m + 1) W s b3 b4 b6 ha h2 h3 h4 h6 =
        arithmeticInitialFactorRatioChart π m W s b3 b4 b6 ha h2 h3 h4 h6 ≫
          Spec.map (CommRingCat.ofHom (PolygonSmoothing.ringMap (restriction R π m).toRingHom
            (arithmeticInitialMobiusSmoothing W ha s π (m + 1))
            (arithmeticInitialMobiusSmoothing W ha s π m)
            (arithmeticInitialMobiusSmoothing_restriction W ha s π m))) := by
  unfold arithmeticFullInitialNodeQuotient arithmeticInitialFactorRatioChart
    arithmeticInitialMobiusSmoothing
  apply canonicalFactorRatioChart_coefficient_of_eq
    (restriction R π m).toRingHom (W.map (algebraMap R (Quotient R π (m + 1)))) _
    _ _ _ _ (W.map q) _ _ _ _ _ (arithmeticInitialCurve_restriction R π m W)
    ((restriction R π m).commutes s) ((restriction R π m).commutes b3)
    ((restriction R π m).commutes b4) ((restriction R π m).commutes b6)
  exact arithmeticParameterIdeal_restriction R π m

end FLT.Mazur.WeierstrassModificationX
