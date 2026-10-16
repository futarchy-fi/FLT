/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstIncomingTail
public import FLT.Mazur.PolygonSmoothingFirstIncomingCoefficients

/-!
# The complementary outgoing coefficients on the original predecessor chart

The other marked chart retains the correction from both factors of a
two-cycle. On longer cycles its outgoing linear coefficient vanishes;
all its higher outgoing coefficients vanish at the first stage.
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
local notation "q" => Equiv.symm (finRotate n) (p)

/-- An unmarked outgoing positive coefficient is annihilated by the parameter. -/
theorem completePointFirstNumerator_unmarked_parameter_outgoing
    (j : Fin n) (hji : j ≠ i) (hjp : j ≠ (p))
    (d : ℕ) (s : Γ(tensorPower (L) d, ⊤)) (k : ℤ) (hk : 0 < k) :
    (t) * (leftLaurentMap (t) (N j d s)).coeff k = 0 := by
  have he := completePointStageChartNumerator_laurent K n h 1 i j d s
  have hpp : (finRotate n).symm j ≠ (p) :=
    fun hh ↦ hji ((finRotate n).symm.injective hh)
  have hz := parameter_precedingLaurentMap_positive (t) (parameter_pow K 1)
    (N ((finRotate n).symm j) d s) k hk
  by_cases hpi : (finRotate n).symm j = i
  · have he' : precedingLaurentMap (Ring K 1) (t) (N ((finRotate n).symm j) d s) =
        (C (t) * T 1 - 1) ^ d * leftLaurentMap (t) (N j d s) := by
      simpa only [PolygonInfinitesimal.chartMarkingEquation, ite_eq_right hji,
        ite_eq_right hjp, ite_eq_left hpi, Units.val_one, map_sub, map_one,
        precedingLaurentMap_left, one_pow, one_mul] using he
    have hh := congrArg (fun z ↦ C (t) * z) he'
    rw [LaurentSquareZeroMarking.parameter_marking_pow_mul (t) (parameter_pow K 1)] at hh
    have hc := congrArg (fun z : (Ring K 1)[T;T⁻¹] ↦ z.coeff k) hh
    simp only [← single_eq_C, AddMonoidAlgebra.coeff_single_mul_apply,
      neg_zero, zero_add] at hc
    apply (((isUnit_one : IsUnit (1 : Ring K 1)).neg).pow d).isRegular.left
    dsimp only
    rw [mul_zero, ← mul_assoc, mul_comm ((-1 : Ring K 1) ^ d) (t), ← hc, hz]
  · have he' : precedingLaurentMap (Ring K 1) (t) (N ((finRotate n).symm j) d s) =
        leftLaurentMap (t) (N j d s) := by
      simpa only [PolygonInfinitesimal.chartMarkingEquation, hji, hjp, hpi, hpp,
        ite_false, map_one, one_pow, one_mul] using he
    rw [← he']
    exact hz

/-- The solved predecessor edge includes both corrections when the cycle has length two. -/
theorem completePointFirstNumerator_preceding_coefficient (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) (k : ℤ) :
    (leftLaurentMap (t) (N (p) d s)).coeff k =
      if (q) = i then
        (precedingLaurentMap (Ring K 1) (t) (N (q) d s)).coeff k +
          (d : Ring K 1) * (t) *
            ((precedingLaurentMap (Ring K 1) (t) (N (q) d s)).coeff (k - 1) -
              (precedingLaurentMap (Ring K 1) (t) (N (q) d s)).coeff (k + 1))
      else (-1 : Ring K 1) ^ d *
        ((precedingLaurentMap (Ring K 1) (t) (N (q) d s)).coeff k -
          (d : Ring K 1) * (t) *
            (precedingLaurentMap (Ring K 1) (t) (N (q) d s)).coeff (k + 1)) := by
  have he := completePointStageChartNumerator_laurent K n h 1 i (p) d s
  by_cases hqi : (q) = i
  · rw [ite_eq_left hqi]
    have he' : (C (t) * T (-1) - 1) ^ d *
        precedingLaurentMap (Ring K 1) (t) (N (q) d s) =
        (C (t) * T 1 - 1) ^ d * leftLaurentMap (t) (N (p) d s) := by
      simpa only [PolygonInfinitesimal.chartMarkingEquation,
        PolygonCyclicAtlas.prev_ne h i, ite_eq_left hqi, ite_false, ite_true,
        inv_one, Units.val_one, map_sub, map_one,
        leftLaurentMap_right, precedingLaurentMap_left] using he
    simpa only [sub_neg_eq_add] using LaurentSquareZeroMarking.cross_coefficient
      (t) (parameter_pow K 1) 1 (-1) d _ _ he'.symm k
  · rw [ite_eq_right hqi]
    have he' : (C (t) * T (-1) - 1) ^ d *
        precedingLaurentMap (Ring K 1) (t) (N (q) d s) =
        leftLaurentMap (t) (N (p) d s) := by
      simpa only [PolygonInfinitesimal.chartMarkingEquation, PolygonCyclicAtlas.prev_ne h i,
        hqi, PolygonCyclicAtlas.prev_ne h (p), ite_false, ite_true, inv_one,
        Units.val_one, map_sub, map_one, leftLaurentMap_right, one_pow, one_mul] using he
    rw [← he']
    simpa only [sub_neg_eq_add] using
      LaurentSquareZeroMarking.marking_pow_mul_coefficient (t) (parameter_pow K 1) (-1) d _ k

/-- The predecessor has no outgoing tail beyond degree one in the full first-stage ring. -/
theorem completePointFirstNumerator_preceding_above (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) (k : ℤ) (hk : 1 < k) :
    (leftLaurentMap (t) (N (p) d s)).coeff k = 0 := by
  rw [completePointFirstNumerator_preceding_coefficient K n h i]
  rw [precedingLaurentMap_coefficient_above (t) 1 (parameter_pow K 1) _ k hk,
    precedingLaurentMap_coefficient_above (t) 1 (parameter_pow K 1) _ (k + 1) (by omega)]
  split_ifs
  · rw [sub_zero, zero_add, mul_assoc,
      parameter_precedingLaurentMap_positive (t) (parameter_pow K 1) _ (k - 1) (by omega),
      mul_zero]
  · rw [mul_zero, sub_zero, mul_zero]

/-- The remaining predecessor linear coefficient is the exact original two-cycle term. -/
theorem completePointFirstNumerator_preceding_linear (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    (leftLaurentMap (t) (N (p) d s)).coeff 1 =
      if (q) = i then (t) * ((leftLaurentMap (t) (N i d s)).coeff 1 +
        (d : Ring K 1) * (leftLaurentMap (t) (N i d s)).coeff 0) else 0 := by
  have hq0 := branch_coefficient_nonneg (t) (N (q) d s) 0
  have hq1 := branch_coefficient_nonneg (t) (N (q) d s) 1
  simp only [Nat.cast_zero, pow_zero, one_mul] at hq0
  simp only [Nat.cast_one, pow_one] at hq1
  have hq2 := precedingLaurentMap_coefficient_above (t) 1 (parameter_pow K 1)
    (N (q) d s) 2 (by decide)
  rw [completePointFirstNumerator_preceding_coefficient K n h i]
  simp only [Int.reduceSub, Int.reduceAdd, hq0, hq1, hq2, mul_zero, sub_zero]
  split_ifs with hqi
  · rw [hqi]
    ring
  · rw [completePointFirstNumerator_unmarked_parameter_outgoing K n h i (q) hqi
      (PolygonCyclicAtlas.prev_ne h (p)) d s 1 (by decide), mul_zero]

end FLT.Mazur.PolygonInfinitesimalStages
