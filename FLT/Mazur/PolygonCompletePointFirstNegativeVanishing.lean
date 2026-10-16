/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstAdjacentCoefficients

/-!
# Vanishing of the actual first-order negative numerator coefficient

The two-gon has two marked charts on its second edge. Multiplying that
full overlap equation by the parameter cancels both first-order corrections.
Together with the unmarked-next-chart case this treats every n at least two.
-/

@[expose] public noncomputable section
open AlgebraicGeometry Scheme.Modules
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing FCurve ModuleLineBundleTensorPullback LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "t" => parameter K 1
local notation "L" => originalStageSinglePointLine K n h 1 i
local notation "N" => completePointStageChartNumerator K n h 1 i
local notation "p" => Equiv.symm (finRotate n) i

/-- The second marked edge forces negative vanishing without assuming distinct third charts. -/
theorem completePointFirstNumerator_negative_twoCycle
    (hcycle : (finRotate n).symm ((finRotate n).symm i) = i)
    (d : ℕ) (s : Γ(tensorPower (L) d, ⊤)) :
    (leftLaurentMap (t) (N i d s)).coeff (-1) = 0 := by
  have he := completePointStageChartNumerator_laurent K n h 1 i (p) d s
  rw [hcycle] at he
  have he' : (C (t) * T (-1) - 1) ^ d *
      precedingLaurentMap (Ring K 1) (t) (N i d s) =
      (C (t) * T 1 - 1) ^ d * leftLaurentMap (t) (N (p) d s) := by
    simpa only [PolygonInfinitesimal.chartMarkingEquation, PolygonCyclicAtlas.prev_ne h i,
      ite_false, ite_true, inv_one, Units.val_one, map_sub, map_one,
      leftLaurentMap_right, precedingLaurentMap_left] using he
  have ht := congrArg (fun z ↦ C (t) * z) he'
  rw [LaurentSquareZeroMarking.parameter_marking_pow_mul (t) (parameter_pow K 1),
    LaurentSquareZeroMarking.parameter_marking_pow_mul (t) (parameter_pow K 1)] at ht
  have hc := congrArg (fun z : (Ring K 1)[T;T⁻¹] ↦ z.coeff (-1)) ht
  simp only [← single_eq_C, AddMonoidAlgebra.coeff_single_mul_apply,
    neg_zero, zero_add] at hc
  have hz : (t) * (leftLaurentMap (t) (N (p) d s)).coeff (-1) = 0 := by
    rw [show (-1 : ℤ) = -(1 : ℕ) by rfl, branch_coefficient_nonpos, pow_one,
      ← mul_assoc, ← pow_two, parameter_pow, zero_mul]
  have hl := branch_coefficient_nonpos (t) (N i d s) 1
  simp only [pow_one, Nat.cast_one] at hl
  apply (((isUnit_one : IsUnit (1 : Ring K 1)).neg).pow d).isRegular.left
  dsimp only
  rw [mul_zero, hl, ← mul_assoc, mul_comm ((-1 : Ring K 1) ^ d) (t), hc,
    mul_comm (t), mul_assoc, hz, mul_zero]

/-- The actual outgoing coefficient at -1 vanishes for every polygon with at least two sides. -/
theorem completePointFirstNumerator_negative_vanishes (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    (leftLaurentMap (t) (N i d s)).coeff (-1) = 0 := by
  let j := finRotate n i
  have hj : (finRotate n).symm j = i := Equiv.symm_apply_apply _ _
  have hji : j ≠ i := by
    intro he
    exact PolygonCyclicAtlas.prev_ne h i (he ▸ hj)
  by_cases hjp : j = (p)
  · exact completePointFirstNumerator_negative_twoCycle K n h i (hjp ▸ hj) d s
  · exact completePointFirstNumerator_negative_eq_zero K n h i j hj hji hjp d s

/-- All negative outgoing coefficients of the retained first-order numerator vanish. -/
theorem completePointFirstNumerator_coefficient_negative (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) (k : ℤ) (hk : k < 0) :
    (leftLaurentMap (t) (N i d s)).coeff k = 0 := by
  by_cases he : k = -1
  · rw [he, completePointFirstNumerator_negative_vanishes K n h i d s]
  · exact leftLaurentMap_coefficient_below (t) 1 (parameter_pow K 1) _ k (by omega)

/-- The retained first-order numerator has polynomial Laurent support in [0,d+1]. -/
theorem completePointFirstNumerator_polynomial_support (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    (leftLaurentMap (t) (N i d s)).coeff.support ⊆ Finset.Icc (0 : ℤ) ((d : ℤ) + 1) := by
  intro k hk
  have hn := Finsupp.mem_support_iff.mp hk
  have hb := Finset.mem_Icc.mp (completePointStageNumerator_support K n h 1 i d s hk)
  apply Finset.mem_Icc.mpr
  constructor
  · by_contra he
    exact hn (completePointFirstNumerator_coefficient_negative K n h i d s k (by omega))
  · exact hb.2

end FLT.Mazur.PolygonInfinitesimalStages
