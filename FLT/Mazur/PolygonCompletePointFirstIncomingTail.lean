/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstPolynomialNumerator
public import FLT.Mazur.LaurentSquareZeroCrossCoefficients
public import FLT.Mazur.PolygonSmoothingFirstLaurentLifts

/-!
# The retained incoming tail, including both factors of the two-gon edge

The incoming numerator on the marked chart has no terms below minus one.
On a two-cycle its remaining coefficient is computed from the original
outgoing degree coefficients; no complete lift is replaced.
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

/-- Both original marking factors contribute to every incoming two-cycle coefficient. -/
theorem completePointFirstNumerator_twoCycle_coefficient
    (hcycle : (finRotate n).symm ((finRotate n).symm i) = i)
    (d : ℕ) (s : Γ(tensorPower (L) d, ⊤)) (k : ℤ) :
    (precedingLaurentMap (Ring K 1) (t) (N i d s)).coeff k =
      (leftLaurentMap (t) (N (p) d s)).coeff k + (d : Ring K 1) * (t) *
        ((leftLaurentMap (t) (N (p) d s)).coeff (k + 1) -
          (leftLaurentMap (t) (N (p) d s)).coeff (k - 1)) := by
  have he := completePointStageChartNumerator_laurent K n h 1 i (p) d s
  rw [hcycle] at he
  have he' : (C (t) * T (-1) - 1) ^ d *
      precedingLaurentMap (Ring K 1) (t) (N i d s) =
      (C (t) * T 1 - 1) ^ d * leftLaurentMap (t) (N (p) d s) := by
    simpa only [PolygonInfinitesimal.chartMarkingEquation, PolygonCyclicAtlas.prev_ne h i,
      ite_false, ite_true, inv_one, Units.val_one, map_sub, map_one,
      leftLaurentMap_right, precedingLaurentMap_left] using he
  simpa only [sub_neg_eq_add] using LaurentSquareZeroMarking.cross_coefficient
    (t) (parameter_pow K 1) (-1) 1 d _ _ he' k

/-- The exact incoming two-cycle coefficient retains the original degree and lower term. -/
theorem completePointFirstNumerator_twoCycle_incoming
    (hcycle : (finRotate n).symm ((finRotate n).symm i) = i)
    (d : ℕ) (s : Γ(tensorPower (L) d, ⊤)) :
    (precedingLaurentMap (Ring K 1) (t) (N i d s)).coeff (-1) =
      (-1 : Ring K 1) ^ d * (t) *
        ((leftLaurentMap (t) (N i d s)).coeff ((d : ℤ) - 1) +
          (d : Ring K 1) * (leftLaurentMap (t) (N i d s)).coeff d) := by
  rw [completePointFirstNumerator_twoCycle_coefficient K n h i hcycle,
    show (-1 + 1 : ℤ) = 0 by decide,
    leftLaurentMap_coefficient_below (t) 1 (parameter_pow K 1) _ (-1 - 1) (by decide),
    sub_zero, show (-1 : ℤ) = -(1 : ℕ) by rfl,
    branch_coefficient_nonpos, pow_one, Nat.cast_one,
    completePointStageNumerator_marked_coefficient K n h 1 i d s (-1)]
  have hc := completePointStageNumerator_marked_coefficient K n h 1 i d s 0
  have hz := branch_coefficient_nonneg (t) (N (p) d s) 0
  simp only [Nat.cast_zero, pow_zero, one_mul] at hz
  rw [hz, zero_add] at hc
  rw [hc, show (-1 + (d : ℤ)) = (d : ℤ) - 1 by omega]
  ring

/-- No further incoming negative term survives in the full first-stage marked numerator. -/
theorem completePointFirstNumerator_incoming_below (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) (k : ℤ) (hk : k < -1) :
    (precedingLaurentMap (Ring K 1) (t) (N i d s)).coeff k = 0 := by
  let j := finRotate n i
  have hj : (finRotate n).symm j = i := Equiv.symm_apply_apply _ _
  have hji : j ≠ i := by
    intro he
    exact PolygonCyclicAtlas.prev_ne h i (he ▸ hj)
  by_cases hjp : j = (p)
  · rw [completePointFirstNumerator_twoCycle_coefficient K n h i (hjp ▸ hj),
      leftLaurentMap_coefficient_below (t) 1 (parameter_pow K 1) _ k hk,
      leftLaurentMap_coefficient_below (t) 1 (parameter_pow K 1) _ (k - 1) (by omega),
      sub_zero, zero_add, mul_assoc,
      parameter_leftLaurentMap_negative (t) (parameter_pow K 1) _ (k + 1) (by omega),
      mul_zero]
  · rw [completePointFirstNumerator_next_coefficient K n h i j hj hji hjp,
      leftLaurentMap_coefficient_below (t) 1 (parameter_pow K 1) _ k hk,
      leftLaurentMap_coefficient_below (t) 1 (parameter_pow K 1) _ (k - 1) (by omega),
      mul_zero, sub_zero, mul_zero]

end FLT.Mazur.PolygonInfinitesimalStages
