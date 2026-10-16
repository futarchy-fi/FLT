/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstNodeCoordinateNumerators
public import FLT.Mazur.PolygonCompletePointNodePoleEquations

/-!
# Original node coordinates from the unchanged localized pole functions

The exact numerator cancellation descends to the same original localization.
Only the actual common marking unit is inverted to recover each coordinate.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "t" => parameter K 1
local notation "ρ" => algebraMap (Ring K 1) (ChartRing (t))
local notation "σ" => algebraMap (ChartRing (t)) (StageNodeLocalization K 1)
local notation "x" => (σ) (leftCoordinate (t))
local notation "y" => (σ) (rightCoordinate (t))
local notation "p" => Equiv.symm (finRotate n) i
local notation "P₂" => leftLaurentMap (t)
  (completePointStagePoleTwoChartNumerator K n h 1 i i)
local notation "P₃" => leftLaurentMap (t)
  (completePointStagePoleThreeChartNumerator K n h 1 i i)
local notation "u" => completePointStageCommonMarkingUnit K n h 1 i
local notation "λ" => (u : Ring K 1)
local notation "A" => (σ) ((ρ) (AddMonoidAlgebra.coeff (P₂) 2))
local notation "B" => (σ) ((ρ) (AddMonoidAlgebra.coeff (P₃) 3))
local notation "C₀" => (σ) ((ρ) (AddMonoidAlgebra.coeff (P₃) 2 + 3 * AddMonoidAlgebra.coeff (P₃) 3))
local notation "a" => (σ) ((ρ) ((λ) ^ 2))
local notation "b" => (σ) ((ρ) ((λ) ^ 3))
local notation "f₂" => completePointNodeLocalizedPoleTwo K n h 1 i
local notation "f₃" => completePointNodeLocalizedPoleThree K n h 1 i

/-- The original localized quadratic and cubic extract the outgoing node coordinate exactly. -/
theorem completePointFirstNodePoles_extract_left :
    ((x) - 1) ^ 3 * ((a) * (f₃ i - (B)) - (C₀) * (f₂ i - (A))) =
      (σ) ((ρ) ((λ) ^ 5)) * (x) := by
  have he := congrArg (σ) (completePointFirstPoleNumerators_extract_left K n h i)
  simp only [map_mul, map_sub, map_pow, map_one] at he ⊢
  rw [← completePointNodePoleTwo_own_equation,
    ← completePointNodePoleThree_own_equation] at he
  convert he using 1
  ring

/-- The same retained functions on the predecessor extract the incoming coordinate. -/
theorem completePointFirstNodePoles_extract_preceding_right :
    ((y) - 1) ^ 3 * ((a) * (f₃ (p) - (B)) - ((C₀) - (b)) * (f₂ (p) - (A))) =
      -(σ) ((ρ) ((λ) ^ 5)) * (y) := by
  have he := congrArg (σ)
    (completePointFirstPoleNumerators_extract_preceding_right K n h i)
  simp only [map_mul, map_sub, map_pow, map_one, map_neg] at he ⊢
  rw [← completePointNodePoleTwo_preceding_equation,
    ← completePointNodePoleThree_preceding_equation] at he
  convert he using 1
  ring

/-- The inverse fifth marking unit cancels its original coefficient in the same localization. -/
theorem completePointFirstNodeMarkingUnit_inv_fifth :
    (σ) ((ρ) (((u)⁻¹ : (Ring K 1)ˣ) ^ 5)) * (σ) ((ρ) ((λ) ^ 5)) = 1 := by
  rw [← map_mul, ← map_mul]
  simp only [← mul_pow, Units.inv_mul, one_pow, map_one]

/-- The outgoing coordinate is an explicit expression in the unchanged original pole functions. -/
theorem completePointFirstNodePoles_recover_left :
    (x) = (σ) ((ρ) (((u)⁻¹ : (Ring K 1)ˣ) ^ 5)) * ((x) - 1) ^ 3 *
      ((a) * (f₃ i - (B)) - (C₀) * (f₂ i - (A))) := by
  rw [mul_assoc, completePointFirstNodePoles_extract_left, ← mul_assoc,
    completePointFirstNodeMarkingUnit_inv_fifth, one_mul]

/-- The incoming coordinate is recovered with the same original unit and its prescribed sign. -/
theorem completePointFirstNodePoles_recover_preceding_right :
    (y) = -(σ) ((ρ) (((u)⁻¹ : (Ring K 1)ˣ) ^ 5)) * ((y) - 1) ^ 3 *
      ((a) * (f₃ (p) - (B)) - ((C₀) - (b)) * (f₂ (p) - (A))) := by
  rw [mul_assoc, completePointFirstNodePoles_extract_preceding_right, ← mul_assoc,
    neg_mul_neg, completePointFirstNodeMarkingUnit_inv_fifth, one_mul]

end FLT.Mazur.PolygonInfinitesimalStages
