/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstPolynomialNumerator
public import FLT.Mazur.PolygonSmoothingFirstConstantCoefficients

/-!
# Constant terms on every unmarked first-order edge

The original overlap equations give a signed constant recurrence. Both
possible marking factors are retained, including when they occur on the
same edge of a two-gon.
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

/-- The constant recurrence retains each original marking sign at an unmarked edge. -/
theorem completePointFirstNumerator_constant_edge (j : Fin n) (hji : j ≠ i)
    (d : ℕ) (s : Γ(tensorPower (L) d, ⊤)) :
    (if j = (p) then (-1 : Ring K 1) ^ d else 1) *
        (leftLaurentMap (t) (N ((finRotate n).symm j) d s)).coeff 0 =
      (if (finRotate n).symm j = i then (-1 : Ring K 1) ^ d else 1) *
        (leftLaurentMap (t) (N j d s)).coeff 0 := by
  have he := completePointStageChartNumerator_laurent K n h 1 i j d s
  have hpp : (finRotate n).symm j ≠ (p) := fun he ↦ hji ((finRotate n).symm.injective he)
  simp only [PolygonInfinitesimal.chartMarkingEquation, ite_eq_right hji, ite_eq_right hpp] at he
  by_cases hjp : j = (p) <;> by_cases hpi : (finRotate n).symm j = i
  · simp only [ite_eq_left hjp, ite_eq_left hpi] at he ⊢
    simpa only [inv_one, Units.val_one, map_sub, map_one, leftLaurentMap_right,
      precedingLaurentMap_left,
      first_incoming_marking_constant (t) (parameter_pow K 1),
      first_outgoing_marking_constant (t) (parameter_pow K 1)] using
      congrArg (fun z : (Ring K 1)[T;T⁻¹] ↦ z.coeff 0) he
  · simp only [ite_eq_left hjp, ite_eq_right hpi, one_mul] at he ⊢
    simpa only [inv_one, Units.val_one, map_sub, map_one, leftLaurentMap_right,
      one_pow, one_mul, first_incoming_marking_constant (t) (parameter_pow K 1)] using
      congrArg (fun z : (Ring K 1)[T;T⁻¹] ↦ z.coeff 0) he
  · simp only [ite_eq_right hjp, ite_eq_left hpi, one_mul] at he ⊢
    simpa only [Units.val_one, map_sub, map_one, precedingLaurentMap_left,
      one_pow, one_mul, branch_coefficient_zero,
      first_outgoing_marking_constant (t) (parameter_pow K 1)] using
      congrArg (fun z : (Ring K 1)[T;T⁻¹] ↦ z.coeff 0) he
  · simp only [ite_eq_right hjp, ite_eq_right hpi, one_mul] at he ⊢
    simpa only [map_one, one_pow, one_mul, branch_coefficient_zero] using
      congrArg (fun z : (Ring K 1)[T;T⁻¹] ↦ z.coeff 0) he

/-- A sign correction makes every edge except the original marked edge constant. -/
theorem completePointFirstNumerator_weighted_constant_edge (j : Fin n) (hji : j ≠ i)
    (d : ℕ) (s : Γ(tensorPower (L) d, ⊤)) :
    (if j = i ∨ j = (p) then (-1 : Ring K 1) ^ d else 1) *
        (leftLaurentMap (t) (N j d s)).coeff 0 =
      (if (finRotate n).symm j = i ∨ (finRotate n).symm j = (p)
        then (-1 : Ring K 1) ^ d else 1) *
        (leftLaurentMap (t) (N ((finRotate n).symm j) d s)).coeff 0 := by
  have he := completePointFirstNumerator_constant_edge K n h i j hji d s
  have hpp : (finRotate n).symm j ≠ (p) := fun he ↦ hji ((finRotate n).symm.injective he)
  have hs : (-1 : Ring K 1) ^ d * (-1 : Ring K 1) ^ d = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  simp only [hji, hpp, false_or, or_false]
  by_cases hjp : j = (p) <;> by_cases hpi : (finRotate n).symm j = i
  · simp only [ite_eq_left hjp, ite_eq_left hpi] at he ⊢
    exact he.symm
  · simp only [ite_eq_left hjp, ite_eq_right hpi, one_mul] at he ⊢
    rw [← he, ← mul_assoc, hs, one_mul]
  · simp only [ite_eq_right hjp, ite_eq_left hpi, one_mul] at he ⊢
    rw [he, ← mul_assoc, hs, one_mul]
  · simpa only [ite_eq_right hjp, ite_eq_right hpi, one_mul] using he.symm

end FLT.Mazur.PolygonInfinitesimalStages
