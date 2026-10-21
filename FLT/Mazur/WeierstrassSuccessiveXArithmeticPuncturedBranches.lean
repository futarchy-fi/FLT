/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXTensorPuncturedBranches
public import FLT.Mazur.PolygonArithmeticStageCoefficients
public import FLT.Mazur.WeierstrassDividedExactCoefficientDepth

/-!
# Branches on every arithmetic puncture at positive depth

Nilpotence of the arithmetic parameter supplies the closed-fiber condition
at every prime. No pre-middle bound or coefficient-vanishing premise is needed.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassSuccessiveX
open PolygonArithmeticStages WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section ArithmeticPrimes
variable {R : Type*} [CommRing R] (π : R) (m : ℕ)
  (A : Type*) [CommRing A] [Algebra R A] [Algebra (Quotient R π m) A]
  [IsScalarTower R (Quotient R π m) A] (p : PrimeSpectrum A)

include m in
/-- Every arithmetic prime contains the original parameter, by its explicit nilpotence. -/
theorem arithmeticPrime_parameter_mem : algebraMap R A π ∈ p.asIdeal := by
  apply p.isPrime.mem_of_pow_mem (m + 1)
  have h := congrArg (algebraMap (Quotient R π m) A) (parameter_pow R π m)
  rw [map_pow, map_zero] at h
  change (algebraMap (Quotient R π m) A (algebraMap R (Quotient R π m) π)) ^ _ = 0 at h
  rw [← IsScalarTower.algebraMap_apply] at h
  rw [h]
  exact p.asIdeal.zero_mem

include m in
/-- Every multiple of the parameter vanishes at all primes of an arithmetic algebra. -/
theorem arithmeticPrime_coefficient_mem (b : R) (hb : b ∈ Ideal.span {π}) :
    algebraMap R A b ∈ p.asIdeal := by
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hb
  rw [hv, map_mul]
  exact p.asIdeal.mul_mem_right _ (arithmeticPrime_parameter_mem π m A p)

end ArithmeticPrimes

variable {R : Type*} [CommRing R] [IsLocalRing R] {W : WeierstrassCurve R} {π : R}
  {depth : ℕ} (D : SplitNodeDepth W π depth) (m k : ℕ) (b3 b4 b6 : R)
local notation "Q" => Quotient R π m
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 Q
local notation "v" => tensorCoord W (π ^ k) π b3 b4 b6 Q 1
local notation "u" => tensorCoord W (π ^ k) π b3 b4 b6 Q 2
local notation "α" => algebraMap R T W.a₁

include D in
/-- The original arithmetic input determines one of the two slope branches. -/
theorem arithmeticPunctured_slope_cases (hk : 0 < k) (p : PrimeSpectrum T)
    (hu : u ∉ p.asIdeal) : v ∈ p.asIdeal ∨ v + α ∈ p.asIdeal := by
  apply tensorPunctured_slope_cases W (π ^ k) π b3 b4 b6 Q p
    (arithmeticPrime_parameter_mem π m T p) hu
  · rw [map_pow]
    exact p.asIdeal.pow_mem_of_mem (arithmeticPrime_parameter_mem π m T p) k (by omega)
  · exact arithmeticPrime_coefficient_mem π m T p W.a₂ (D.maximalIdeal_eq ▸ D.a₂_mem)

include D in
/-- The contracted original ordinate has a branch without any extra depth bound. -/
theorem arithmeticPunctured_contracted_cases (hk : 0 < k) (p : PrimeSpectrum T)
    (hu : u ∉ p.asIdeal) :
    u * v ∈ p.asIdeal ∨ u * v + α * u ∈ p.asIdeal := by
  apply tensorPunctured_contracted_cases W (π ^ k) π b3 b4 b6 Q p
    (arithmeticPrime_parameter_mem π m T p) hu
  · rw [map_pow]
    exact p.asIdeal.pow_mem_of_mem (arithmeticPrime_parameter_mem π m T p) k (by omega)
  · exact arithmeticPrime_coefficient_mem π m T p W.a₂ (D.maximalIdeal_eq ▸ D.a₂_mem)

include D in
/-- The two branches are disjoint at every punctured arithmetic input. -/
theorem arithmeticPunctured_contracted_not_both (p : PrimeSpectrum T) (hu : u ∉ p.asIdeal) :
    ¬ (u * v ∈ p.asIdeal ∧ u * v + α * u ∈ p.asIdeal) :=
  tensorPunctured_contracted_not_both W (π ^ k) π b3 b4 b6 Q p hu D.a₁_unit

end FLT.Mazur.WeierstrassSuccessiveX
