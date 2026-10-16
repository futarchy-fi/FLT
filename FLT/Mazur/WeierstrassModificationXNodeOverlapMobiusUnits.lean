/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOverlapOppositeCoordinates
public import FLT.Mazur.NodalFiberTangentFraction

/-!
# Exact fractional units on both full original initial-node overlap legs

Both units retain the original polynomial factors. The opposite denominator
is the complete opposite factor minus the tangent, at every arithmetic order.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "L" => PolynomialNodeOpen W s
local notation "O" => PolynomialNodeOverlap W s
local notation "G" => polynomialNodeOverlapEvaluation W s b3 b4 b6 r hr I hI hrI h3
local notation "H" => polynomialNodeOverlapOppositeEvaluation W s b3 b4 b6 r hr I hI hrI h3
local notation "V" => polynomialSmallFactor W s b3 b4 b6 r
local notation "U" => polynomialOppositeFactor W s b3 b4 b6 r
local notation "a" => algebraMap R O W.a₁

/-- The first full intersection fraction is invertible because the original small factor is. -/
theorem polynomialNodeOverlap_fraction_isUnit :
    IsUnit (algebraMap L O (NodalFiber.tangentFraction s W.a₁)) := by
  rw [NodalFiber.tangentFraction, map_mul]
  apply IsUnit.mul
  · change IsUnit (algebraMap L O
      (algebraMap (NodalFiber.Coordinate s) L (NodalFiber.q s)))
    exact IsLocalization.Away.algebraMap_isUnit _
  · exact (Units.isUnit _).map (algebraMap L O)

/-- The actual reflected overlap fraction is invertible because the whole opposite factor is. -/
theorem polynomialNodeOverlap_opposite_fraction_isUnit :
    IsUnit (H (NodalFiber.tangentFraction s W.a₁)) := by
  rw [NodalFiber.tangentFraction, map_mul]
  apply IsUnit.mul
  · change IsUnit (H (algebraMap (NodalFiber.Coordinate s) L (NodalFiber.q s)))
    rw [polynomialNodeOverlapOppositeEvaluation_q]
    exact (polynomialNodeOverlap_opposite_isUnit W s b3 b4 b6 r hr I hI hrI h3).neg
  · exact (Units.isUnit _).map H

/-- The first full fractional overlap parameter, with its actual localization inverse. -/
def polynomialNodeOverlapMobiusUnit : Oˣ :=
  (polynomialNodeOverlap_fraction_isUnit W s).unit

/-- The actual opposite overlap parameter, retaining all reflected corrections. -/
def polynomialNodeOverlapOppositeMobiusUnit : Oˣ :=
  (polynomialNodeOverlap_opposite_fraction_isUnit W s b3 b4 b6 r hr I hI hrI h3).unit

/-- The first fraction is small factor divided by small factor plus the original tangent. -/
theorem polynomialNodeOverlapMobiusUnit_denominator :
    (polynomialNodeOverlapMobiusUnit W s : O) * (G V + a) = G V := by
  rw [polynomialNodeOverlapMobiusUnit, IsUnit.unit_spec,
    polynomialNodeOverlapEvaluation_small]
  have h := congrArg (algebraMap L O) (NodalFiber.tangentFraction_denominator s W.a₁)
  simpa only [map_mul, map_add, NodalFiber.tangentQ,
    ← IsScalarTower.algebraMap_apply R L O] using h

/-- The reflected fraction is opposite factor divided by opposite factor minus the tangent. -/
theorem polynomialNodeOverlapOppositeMobiusUnit_denominator :
    (polynomialNodeOverlapOppositeMobiusUnit W s b3 b4 b6 r hr I hI hrI h3 : O) *
      (G U - a) = G U := by
  rw [polynomialNodeOverlapOppositeMobiusUnit, IsUnit.unit_spec]
  have h := congrArg H (NodalFiber.tangentFraction_denominator s W.a₁)
  simp only [map_mul, map_add, AlgHom.commutes, NodalFiber.tangentQ] at h
  rw [polynomialNodeOverlapOppositeEvaluation_q] at h
  linear_combination -h

/-- Both exact overlap parameters avoid the deleted value one whenever the tangent is a unit. -/
theorem polynomialNodeOverlapMobiusUnit_sub_one_isUnit (ha : IsUnit W.a₁) :
    IsUnit ((polynomialNodeOverlapMobiusUnit W s : O) - 1) := by
  rw [polynomialNodeOverlapMobiusUnit, IsUnit.unit_spec, ← map_one (algebraMap L O),
    ← map_sub]
  exact (NodalFiber.tangentFraction_sub_one_isUnit s W.a₁ ha).map (algebraMap L O)

/-- The actual reflected parameter also avoids one over the full coefficient ring. -/
theorem polynomialNodeOverlapOppositeMobiusUnit_sub_one_isUnit (ha : IsUnit W.a₁) :
    IsUnit ((polynomialNodeOverlapOppositeMobiusUnit W s b3 b4 b6 r hr I hI hrI h3 : O) -
      1) := by
  rw [polynomialNodeOverlapOppositeMobiusUnit, IsUnit.unit_spec, ← map_one H, ← map_sub]
  exact (NodalFiber.tangentFraction_sub_one_isUnit s W.a₁ ha).map H

end FLT.Mazur.WeierstrassModificationX
