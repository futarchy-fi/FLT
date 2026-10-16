/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointNumeratorLaurentBounds
public import FLT.Mazur.PolygonSmoothingBranchCoefficients

/-!
# Exact parameter factors in the retained numerator tails

The Laurent terms outside the degree interval are not discarded. Each is
the prescribed power of the original parameter times a coefficient on the
other branch of an original chart, with the marked transition sign retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry Scheme.Modules
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing FCurve ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i : Fin n)
local notation "t" => parameter K m
local notation "L" => originalStageSinglePointLine K n h m i
local notation "N" => completePointStageChartNumerator K n h m i
local notation "p" => Equiv.symm (finRotate n) i

/-- The lower tail is the actual incoming branch coefficient times its parameter power. -/
theorem completePointStageNumerator_lower_parameter (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) (k : ℕ) :
    (leftLaurentMap (t) (N i d s)).coeff (-(k : ℤ)) =
      (t) ^ k * (precedingLaurentMap (Ring K m) (t) (N i d s)).coeff (-(k : ℤ)) :=
  branch_coefficient_nonpos (t) _ k

/-- The upper tail uses the unchanged predecessor numerator and the exact marking sign. -/
theorem completePointStageNumerator_upper_parameter (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) (k : ℕ) :
    (leftLaurentMap (t) (N i d s)).coeff ((k : ℤ) + d) =
      (-1 : Ring K m) ^ d * (t) ^ k *
        (leftLaurentMap (t) (N (p) d s)).coeff k := by
  have hm := completePointStageNumerator_marked_coefficient K n h m i d s (k : ℤ)
  rw [branch_coefficient_nonneg] at hm
  have hs : (-1 : Ring K m) ^ d * (-1 : Ring K m) ^ d = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  calc
    _ = ((-1 : Ring K m) ^ d * (-1 : Ring K m) ^ d) *
        (leftLaurentMap (t) (N i d s)).coeff ((k : ℤ) + d) := by rw [hs, one_mul]
    _ = _ := by rw [mul_assoc, ← hm, ← mul_assoc]

/-- At order one, the negative end coefficient is killed by the original parameter. -/
theorem completePointFirstNumerator_lower_annihilated (d : ℕ)
    (s : Γ(tensorPower (originalStageSinglePointLine K n h 1 i) d, ⊤)) :
    parameter K 1 * (leftLaurentMap (parameter K 1)
      (completePointStageChartNumerator K n h 1 i i d s)).coeff (-1) = 0 := by
  rw [show (-1 : ℤ) = -(1 : ℕ) by rfl,
    completePointStageNumerator_lower_parameter, pow_one, ← mul_assoc,
    ← pow_two, parameter_pow, zero_mul]

/-- At order one, the upper end coefficient is also killed without cancelling the parameter. -/
theorem completePointFirstNumerator_upper_annihilated (d : ℕ)
    (s : Γ(tensorPower (originalStageSinglePointLine K n h 1 i) d, ⊤)) :
    parameter K 1 * (leftLaurentMap (parameter K 1)
      (completePointStageChartNumerator K n h 1 i i d s)).coeff (1 + (d : ℤ)) = 0 := by
  rw [show (1 : ℤ) = (1 : ℕ) by rfl, completePointStageNumerator_upper_parameter,
    pow_one, mul_assoc, mul_left_comm (parameter K 1), ← mul_assoc (parameter K 1),
    ← pow_two, parameter_pow, zero_mul, mul_zero]

end FLT.Mazur.PolygonInfinitesimalStages
