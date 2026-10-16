/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOverlapOppositeCoordinates
public import FLT.Mazur.WeierstrassModificationXZeroMobiusChart

/-!
# The original overlap factors on the zero arithmetic fiber

The opposite factor becomes q+a₁ on the entire first node. On the original
intersection the geometric opposite restriction has second coordinate -q-a₁
and tangent denominator -q. Thus the two fractional parameters are reciprocal.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I) (hbot : I = ⊥)
local notation "N" => NodalFiber.Coordinate s
local notation "L" => PolynomialNodeOpen W s
local notation "O" => PolynomialNodeOverlap W s
local notation "V" => polynomialSmallFactor W s b3 b4 b6 r
local notation "U" => polynomialOppositeFactor W s b3 b4 b6 r
local notation "E" => polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3
local notation "G" => polynomialNodeOverlapEvaluation W s b3 b4 b6 r hr I hI hrI h3
local notation "H" => polynomialNodeOverlapOppositeEvaluation W s b3 b4 b6 r hr I hI hrI h3

include hbot

/-- The entire opposite tangent factor loses exactly its zero-ideal corrections. -/
theorem polynomialNodeForwardBase_opposite_of_bot :
    E U = algebraMap N L (NodalFiber.q s) + algebraMap R L W.a₁ := by
  have hr0 : r = 0 := by simpa only [hbot, Ideal.map_bot, Ideal.mem_bot] using hrI
  have h30 : b3 = 0 := Ideal.mem_bot.mp (hbot ▸ h3)
  change polynomialNodeEvaluation W s b3 b4 b6 r hr I hI hrI h3 _ _ _ _ U = _
  rw [polynomialNodeEvaluation_opposite]
  simp only [hr0, h30, eval₂_zero, map_zero, zero_mul, add_zero]

/-- Both actual overlap factors differ by precisely the original tangent coefficient. -/
theorem polynomialNodeOverlapEvaluation_opposite_of_bot :
    G U = G V + algebraMap R O W.a₁ := by
  change algebraMap L O (E U) = _
  rw [polynomialNodeForwardBase_opposite_of_bot W s b3 b4 b6 r hr I hI hrI h3 hbot,
    map_add, ← IsScalarTower.algebraMap_apply R L O, polynomialNodeOverlapEvaluation_small]

/-- The actual opposite overlap denominator is minus the first small factor on the zero fiber. -/
theorem polynomialNodeOverlapOppositeEvaluation_denominator_of_bot :
    H (algebraMap N L (NodalFiber.q s) + algebraMap R L W.a₁) = -G V := by
  rw [map_add, polynomialNodeOverlapOppositeEvaluation_q, AlgHom.commutes,
    polynomialNodeOverlapEvaluation_opposite_of_bot W s b3 b4 b6 r hr I hI hrI h3 hbot]
  ring

end FLT.Mazur.WeierstrassModificationX
