/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXLaurentCoefficientNaturality
public import FLT.Mazur.WeierstrassSuccessiveArithmeticRestrictionMaps

/-!
# Both original initial Laurent slopes form a compatible arithmetic system

The actual consecutive quotient map preserves the small and opposite labels
and every nilpotent correction of the original initial boundary parameter.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
/-- Explicit target coefficients avoid reducing independently constructed roots during transport. -/
theorem laurentBranchSlope_coefficient_of_eq
    {A B : Type*} [CommRing A] [CommRing B] {f : A →+* B}
    {W : WeierstrassCurve A} {U : WeierstrassCurve B}
    {s b3 b4 b6 : A} {s' b3' b4' b6' : B}
    {I : Ideal A} {J : Ideal B} {hI : IsNilpotent I} {hJ : IsNilpotent J}
    (hf : I ≤ J.comap f) {ha : IsUnit W.a₁} {ha' : IsUnit U.a₁}
    {hs : s ∈ I} {h2 : W.a₂ ∈ I} {h3 : b3 ∈ I} {h4 : b4 ∈ I} {h6 : b6 ∈ I}
    {hs' : s' ∈ J} {h2' : U.a₂ ∈ J} {h3' : b3' ∈ J} {h4' : b4' ∈ J} {h6' : b6' ∈ J}
    {opposite : Bool} (hW : W.map f = U) (hS : f s = s')
    (hB3 : f b3 = b3') (hB4 : f b4 = b4') (hB6 : f b6 = b6') :
    PolygonScalingNaturality.coeffMap f
      (laurentBranchSlope W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 opposite) =
      laurentBranchSlope U s' b3' b4' b6' J hJ ha' hs' h2' h3' h4' h6' opposite := by
  subst U s' b3' b4' b6'
  exact laurentBranchSlope_coefficient f W s b3 b4 b6 I J hf hI hJ ha hs h2 h3 h4 h6 opposite

variable {R : Type*} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6) (opposite : Bool)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)
local notation "hJ" => arithmeticParameterIdeal_nilpotent π m

/-- The full original initial slope at the specified arithmetic order and Boolean label. -/
def arithmeticInitialLaurentSlope : Q[T;T⁻¹] :=
  laurentBranchSlope (W.map q) (q s) (q b3) (q b4) (q b6) J hJ (ha.map q)
    (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
    (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
    (arithmeticCoefficient_mem π m h6) opposite

/-- The full arithmetic slope solves the original initial Laurent equation. -/
theorem arithmeticInitialLaurentSlope_equation :
    arithmeticInitialLaurentSlope π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite ^ 2 +
      laurentSlopeLinear (W.map q) (q b3) *
        arithmeticInitialLaurentSlope π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite =
      laurentSlopeConstant (W.map q) (q s) (q b4) (q b6) :=
  by
    rw [arithmeticInitialLaurentSlope]
    exact laurentBranchSlope_equation ..

attribute [local irreducible] laurentBranchSlope nilpotentLaurentSlope

/-- Consecutive quotient restriction retains the entire original initial slope and its label. -/
theorem arithmeticInitialLaurentSlope_restriction :
    PolygonScalingNaturality.coeffMap (restriction R π m).toRingHom
      (arithmeticInitialLaurentSlope π (m + 1) W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite) =
      arithmeticInitialLaurentSlope π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite := by
  rw [arithmeticInitialLaurentSlope, arithmeticInitialLaurentSlope]
  apply laurentBranchSlope_coefficient_of_eq (arithmeticParameterIdeal_restriction R π m)
  · rw [WeierstrassCurve.map_map]
    exact congrArg W.map (restriction R π m).comp_algebraMap
  · exact (restriction R π m).commutes s
  · exact (restriction R π m).commutes b3
  · exact (restriction R π m).commutes b4
  · exact (restriction R π m).commutes b6

end FLT.Mazur.WeierstrassModificationX
