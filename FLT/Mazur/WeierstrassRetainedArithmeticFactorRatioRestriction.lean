/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedArithmeticFactorRatio
public import FLT.Mazur.WeierstrassRetainedNodeFactorRatioTransport
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedPolygon

/-!
# The original full retained chart commutes with arithmetic restriction

The integral witness for divisibility is chosen once before passing to either
quotient. Thus the actual divisor follows the original restriction map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages PolygonSmoothing WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s c3 c4 c6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ c3) (h4 : π ∣ c4) (h6 : π ∣ c6)
local notation "τ" => arithmeticInitialMobiusSmoothing W ha s π m
local notation "τ₁" => arithmeticInitialMobiusSmoothing W ha s π (m + 1)
local notation "C" => arithmeticRetainedFactorRatioChart π m W s c3 c4 c6 ha hs h2 h3 h4 h6
local notation "C₁" => arithmeticRetainedFactorRatioChart π (m + 1)
  W s c3 c4 c6 ha hs h2 h3 h4 h6

/-- The full retained square uses the actual restriction and exact corrected smoothing. -/
@[reassoc] theorem arithmeticRetainedFactorRatioChart_restriction :
    arithmeticPolygonNodeRestriction R π m ≫ C₁ =
      C ≫ Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom τ₁ τ
        (arithmeticInitialMobiusSmoothing_restriction W ha s π m))) := by
  have hn : arithmeticPolygonNodeRestriction R π m = Spec.map (CommRingCat.ofHom
      (ringMap (restriction R π m).toRingHom (parameter R π (m + 1))
        (parameter R π m) (restriction_parameter R π m))) := by
    let _ := (restriction R π m).toRingHom.toAlgebra
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (ringMap_eq_coefficientMap (S := Quotient R π m) (parameter R π (m + 1))).symm
  rw [hn]
  unfold arithmeticRetainedFactorRatioChart
  apply retainedFactorRatioChart_coefficients_of_eq
    (arithmeticParameterIdeal_restriction R π m)
    (arithmeticInitialCurve_restriction R π m W) (restriction_parameter R π m)
    ((restriction R π m).commutes s) ((restriction R π m).commutes c3)
    ((restriction R π m).commutes c4) ((restriction R π m).commutes c6)
    ((restriction R π m).commutes (Classical.choose hs))

end FLT.Mazur.WeierstrassModificationX
