/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointNumeratorParameterTails
public import FLT.Mazur.LaurentSquareZeroMarking

/-!
# First-order coefficient equations at the next unmarked chart

When the next chart is distinct from both marked charts, the original
cyclic overlap computes its exact coefficient recurrence. It forces the
negative outgoing end coefficient of the retained marked numerator to vanish.
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
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i j : Fin n)
variable (hprev : (finRotate n).symm j = i)
variable (hji : j ≠ i) (hjp : j ≠ (finRotate n).symm i)
include hprev hji hjp
local notation "t" => parameter K 1
local notation "L" => originalStageSinglePointLine K n h 1 i
local notation "N" => completePointStageChartNumerator K n h 1 i

/-- The full original overlap with the next unmarked chart has this exact marking factor. -/
theorem completePointFirstNumerator_next_transition (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    precedingLaurentMap (Ring K 1) (t) (N i d s) =
      (C (t) * T 1 - 1) ^ d * leftLaurentMap (t) (N j d s) := by
  have he := completePointStageChartNumerator_laurent K n h 1 i j d s
  rw [hprev] at he
  simpa only [PolygonInfinitesimal.chartMarkingEquation, hji, hjp, ite_false, ite_true,
    Units.val_one, map_one, one_pow, one_mul, map_sub, precedingLaurentMap_left] using he

/-- Every incoming coefficient obeys the exact neighboring first-order recurrence. -/
theorem completePointFirstNumerator_next_coefficient (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) (k : ℤ) :
    (precedingLaurentMap (Ring K 1) (t) (N i d s)).coeff k =
      (-1 : Ring K 1) ^ d * ((leftLaurentMap (t) (N j d s)).coeff k -
        (d : Ring K 1) * (t) * (leftLaurentMap (t) (N j d s)).coeff (k - 1)) := by
  rw [completePointFirstNumerator_next_transition K n h i j hprev hji hjp]
  exact LaurentSquareZeroMarking.marking_pow_mul_coefficient (t) (parameter_pow K 1) 1 d _ k

/-- The negative end of the incoming numerator is the actual adjacent negative coefficient. -/
theorem completePointFirstNumerator_next_negative (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    (precedingLaurentMap (Ring K 1) (t) (N i d s)).coeff (-1) =
      (-1 : Ring K 1) ^ d * (leftLaurentMap (t) (N j d s)).coeff (-1) := by
  rw [completePointFirstNumerator_next_coefficient K n h i j hprev hji hjp]
  rw [leftLaurentMap_coefficient_below (t) 1 (parameter_pow K 1) _ (-1 - 1) (by decide),
    mul_zero, sub_zero]

/-- The outgoing negative end actually vanishes when the next chart is unmarked. -/
theorem completePointFirstNumerator_negative_eq_zero (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    (leftLaurentMap (t) (N i d s)).coeff (-1) = 0 := by
  rw [show (-1 : ℤ) = -(1 : ℕ) by rfl, branch_coefficient_nonpos, pow_one, Nat.cast_one]
  rw [completePointFirstNumerator_next_negative K n h i j hprev hji hjp]
  rw [show (-1 : ℤ) = -(1 : ℕ) by rfl, branch_coefficient_nonpos, pow_one,
    mul_left_comm (t), ← mul_assoc (t), ← pow_two, parameter_pow, zero_mul, mul_zero]

end FLT.Mazur.PolygonInfinitesimalStages
