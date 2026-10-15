/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInvolution
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Two complementary full initial node neighborhoods

The reflected denominator and the original denominator have unit sum.
Thus they cover the entire original arithmetic initial chart, including t=0.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X])
local notation "A" => Coordinate W s b3 b4 b6

/-- The denominator of the reflected full node neighborhood. -/
def polynomialOppositeDenominator : A :=
  -polynomialOppositeFactor W s b3 b4 b6 r + algebraMap R A W.a₁

/-- The denominator is the actual reflected first denominator. -/
theorem initialReflection_denominator :
    initialReflection W s b3 b4 b6
      (polynomialSmallFactor W s b3 b4 b6 r + algebraMap R A W.a₁) =
        polynomialOppositeDenominator W s b3 b4 b6 r := by
  rw [map_add, initialReflection_small]
  exact congrArg (-polynomialOppositeFactor W s b3 b4 b6 r + ·)
    (((initialReflection W s b3 b4 b6).restrictScalars R).commutes W.a₁)

/-- The two denominators have a sum depending only on the incidence parameter. -/
theorem polynomialNodeDenominators_sum :
    (polynomialSmallFactor W s b3 b4 b6 r + algebraMap R A W.a₁) +
      polynomialOppositeDenominator W s b3 b4 b6 r =
        algebraMap R[X] A (C W.a₁ + (-r - r - C b3 * X)) := by
  simp only [polynomialSmallFactor, polynomialOppositeDenominator, polynomialOppositeFactor,
    polynomialSlopeLinear, map_add, map_sub, map_neg, map_mul]
  have hc : algebraMap R[X] A (C W.a₁) = algebraMap R A W.a₁ :=
    (IsScalarTower.algebraMap_apply R R[X] A W.a₁).symm
  rw [hc]
  ring

variable (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁)
  (hrI : r ∈ I.map C) (h3 : b3 ∈ I)

include hI ha hrI h3 in
/-- The denominator sum is a unit on the complete initial chart. -/
theorem polynomialNodeDenominators_sum_unit :
    IsUnit ((polynomialSmallFactor W s b3 b4 b6 r + algebraMap R A W.a₁) +
      polynomialOppositeDenominator W s b3 b4 b6 r) := by
  rw [polynomialNodeDenominators_sum]
  have hn : -r - r - C b3 * X ∈ polynomialArithmeticIdeal I :=
    (polynomialArithmeticIdeal I).sub_mem
      ((polynomialArithmeticIdeal I).sub_mem ((polynomialArithmeticIdeal I).neg_mem hrI) hrI)
      ((polynomialArithmeticIdeal I).mul_mem_right _ (Ideal.mem_map_of_mem _ h3))
  exact ((NilpotentQuadraticRoot.element_nilpotent _
    (polynomialArithmeticIdeal_nilpotent I hI) hn).isUnit_add_left_of_commute
      (ha.map C) (mul_comm _ _)).map (algebraMap R[X] A)

include hI ha hrI h3 in
/-- Every original prime belongs to at least one of the full node principal opens. -/
theorem polynomialNodeDenominators_cover (p : PrimeSpectrum A) :
    polynomialSmallFactor W s b3 b4 b6 r + algebraMap R A W.a₁ ∉ p.asIdeal ∨
      polynomialOppositeDenominator W s b3 b4 b6 r ∉ p.asIdeal := by
  by_contra h
  push Not at h
  exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (p.asIdeal.add_mem h.1 h.2)
    (polynomialNodeDenominators_sum_unit W s b3 b4 b6 r I hI ha hrI h3))

end FLT.Mazur.WeierstrassModificationX
