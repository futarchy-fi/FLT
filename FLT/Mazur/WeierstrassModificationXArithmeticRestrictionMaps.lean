/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXCoefficientTransport
public import FLT.Mazur.WeierstrassModificationXNodeOpenCoefficientTransport
public import FLT.Mazur.WeierstrassSuccessiveArithmeticRestrictionMaps

/-!
# Quotient restrictions of the entire original initial chart

The target curve is the independently specialized lower-order curve. The maps
retain the whole initial equation and its full node neighborhood.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages
universe u
variable (R : Type u) [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)
local notation "q₀" => algebraMap R Q₀
local notation "q₁" => algebraMap R Q₁
local notation "f" => AlgHom.toRingHom (restriction R π m)

/-- Consecutive arithmetic quotients identify the entire original target curve. -/
theorem arithmeticInitialCurve_restriction : (W.map q₁).map f = W.map q₀ := by
  rw [WeierstrassCurve.map_map]
  exact congrArg W.map (restriction R π m).comp_algebraMap

/-- The coefficient quotient map on the full initial coordinate algebra. -/
def arithmeticInitialCoefficientRingMap : ExtendedCoordinate W s b3 b4 b6 Q₁ →+*
    ExtendedCoordinate W s b3 b4 b6 Q₀ :=
  coefficientRingMapTo f (W.map q₁) (q₁ s) (q₁ b3) (q₁ b4) (q₁ b6)
    (W.map q₀) (q₀ s) (q₀ b3) (q₀ b4) (q₀ b6)
    (arithmeticInitialCurve_restriction R π m W) ((restriction R π m).commutes s)
    ((restriction R π m).commutes b3) ((restriction R π m).commutes b4)
    ((restriction R π m).commutes b6)

/-- The full initial arithmetic scheme uses the actual coefficient quotient restriction. -/
def arithmeticInitialRestriction :
    Spec (.of (ExtendedCoordinate W s b3 b4 b6 Q₀)) ⟶
      Spec (.of (ExtendedCoordinate W s b3 b4 b6 Q₁)) :=
  Spec.map (CommRingCat.ofHom (arithmeticInitialCoefficientRingMap R π m W s b3 b4 b6))

/-- The original quotient restriction on the entire initial node neighborhood. -/
def arithmeticFullInitialNodeQuotient :
    Spec (.of (PolynomialNodeOpen (W.map q₀) (q₀ s))) ⟶
      Spec (.of (PolynomialNodeOpen (W.map q₁) (q₁ s))) :=
  Spec.map (CommRingCat.ofHom (nodeOpenCoefficientRingMapTo f (W.map q₁) (q₁ s)
    (W.map q₀) (q₀ s) (arithmeticInitialCurve_restriction R π m W)
    ((restriction R π m).commutes s)))

/-- Every scalar of the full initial algebra follows the actual quotient homomorphism. -/
theorem arithmeticInitialCoefficientRingMap_scalar (a : Q₁) :
    arithmeticInitialCoefficientRingMap R π m W s b3 b4 b6 (algebraMap Q₁ _ a) =
      algebraMap Q₀ _ (restriction R π m a) :=
  coefficientRingMapTo_algebraMap ..

/-- The original incidence function is preserved at every quotient order. -/
theorem arithmeticInitialCoefficientRingMap_t :
    arithmeticInitialCoefficientRingMap R π m W s b3 b4 b6
      (t (W.map q₁) (q₁ s) (q₁ b3) (q₁ b4) (q₁ b6)) =
        t (W.map q₀) (q₀ s) (q₀ b3) (q₀ b4) (q₀ b6) :=
  coefficientRingMapTo_t ..

/-- The original slope function is preserved at every quotient order. -/
theorem arithmeticInitialCoefficientRingMap_v :
    arithmeticInitialCoefficientRingMap R π m W s b3 b4 b6
      (v (W.map q₁) (q₁ s) (q₁ b3) (q₁ b4) (q₁ b6)) =
        v (W.map q₀) (q₀ s) (q₀ b3) (q₀ b4) (q₀ b6) :=
  coefficientRingMapTo_v ..

end FLT.Mazur.WeierstrassModificationX
