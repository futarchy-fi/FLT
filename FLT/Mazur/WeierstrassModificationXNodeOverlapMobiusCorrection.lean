/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOverlapMobiusUnits

/-!
# Exact arithmetic correction to reciprocal overlap fractions

The original two full fractions are reciprocal modulo the nilpotent coefficient
ideal. Their exact product error is controlled by the full polynomial factor gap.
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
local notation "V" => G (polynomialSmallFactor W s b3 b4 b6 r)
local notation "U" => G (polynomialOppositeFactor W s b3 b4 b6 r)
local notation "a" => algebraMap R O W.a₁
local notation "u" => polynomialNodeOverlapMobiusUnit W s
local notation "w" => polynomialNodeOverlapOppositeMobiusUnit W s b3 b4 b6 r hr I hI hrI h3
local notation "J" => I.map (algebraMap R O)

/-- The exact denominator-cleared deviation from inverse overlap parameters. -/
theorem polynomialNodeOverlapMobius_product_error :
    ((u : O) * (w : O) - 1) * (V + a) * (U - a) = -a * (U - V - a) := by
  have h₁ := polynomialNodeOverlapMobiusUnit_denominator W s b3 b4 b6 r hr I hI hrI h3
  have h₂ := polynomialNodeOverlapOppositeMobiusUnit_denominator W s b3 b4 b6 r hr I hI hrI h3
  linear_combination (w : O) * (U - a) * h₁ + V * h₂

/-- The complete original factor gap belongs to the original arithmetic coefficient ideal. -/
theorem polynomialNodeOverlap_factor_gap_mem : U - V - a ∈ J := by
  simp only [polynomialOppositeFactor, polynomialSmallFactor, map_add, map_sub,
    hom_polynomial_incidence]
  simp only [polynomialSlopeLinear, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X]
  have hr := NilpotentPolynomialInverse.eval₂_mem I (algebraMap R O) r hrI
    (G (t W s b3 b4 b6))
  have hb : algebraMap R O b3 * G (t W s b3 b4 b6) ∈ J :=
    (J).mul_mem_right _ (Ideal.mem_map_of_mem _ h3)
  convert (J).add_mem ((J).add_mem hr hr) hb using 1
  ring

/-- The first fractional denominator remains a unit on the complete original overlap. -/
theorem polynomialNodeOverlapMobius_denominator_isUnit : IsUnit (V + a) := by
  rw [polynomialNodeOverlapEvaluation_small]
  have h := (NodalFiber.tangent_denominator_isUnit s W.a₁).map (algebraMap L O)
  simpa only [map_add, NodalFiber.tangentQ,
    ← IsScalarTower.algebraMap_apply R L O] using h

/-- The actual opposite denominator is also invertible, retaining all factor corrections. -/
theorem polynomialNodeOverlapOppositeMobius_denominator_isUnit : IsUnit (U - a) := by
  have h := (NodalFiber.tangent_denominator_isUnit s W.a₁).map H
  simp only [map_add, AlgHom.commutes, NodalFiber.tangentQ] at h
  rw [polynomialNodeOverlapOppositeEvaluation_q] at h
  convert h.neg using 1
  ring

/-- Reciprocity holds modulo the coefficient ideal, with the full error explicitly retained. -/
theorem polynomialNodeOverlapMobius_product_sub_one_mem : (u : O) * (w : O) - 1 ∈ J := by
  apply ((J).mul_unit_mem_iff_mem
    (polynomialNodeOverlapMobius_denominator_isUnit W s b3 b4 b6 r hr I hI hrI h3)).mp
  apply ((J).mul_unit_mem_iff_mem
    (polynomialNodeOverlapOppositeMobius_denominator_isUnit
      W s b3 b4 b6 r hr I hI hrI h3)).mp
  rw [polynomialNodeOverlapMobius_product_error]
  exact (J).mul_mem_left _
    (polynomialNodeOverlap_factor_gap_mem W s b3 b4 b6 r hr I hI hrI h3)

end FLT.Mazur.WeierstrassModificationX
