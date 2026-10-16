/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstCentralCoefficients

/-!
# Exact retained numerator forms relative to the marking equation

The quadratic and cubic numerators split into their original regular terms
and the actual value at T=1. The latter is not set to one: identifying it
with the comparison unit still requires the original chart-frame transport.
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
local notation "N₂" => leftLaurentMap (t)
  (completePointStagePoleTwoChartNumerator K n h 1 i i)
local notation "N₃" => leftLaurentMap (t)
  (completePointStagePoleThreeChartNumerator K n h 1 i i)

/-- The quadratic numerator is its retained constant lift plus the actual marking term. -/
theorem completePointFirstPoleTwo_marking_form :
    (N₂) = C ((N₂).coeff 2) * (T 1 - 1) ^ 2 +
      C (eval₂ (RingHom.id (Ring K 1)) 1 (N₂)) * T 1 := by
  conv_lhs => rw [completePointFirstPoleTwo_polynomial K n h i]
  rw [completePointFirstPoleTwo_marking_value]
  simp only [map_add, map_mul, map_ofNat]
  have ht : (T (2 : ℤ) : (Ring K 1)[T;T⁻¹]) = T 1 ^ 2 := by
    rw [T_pow]
    norm_num
  rw [ht]
  ring

/-- The cubic numerator keeps its original regular and lower-pole coefficients. -/
theorem completePointFirstPoleThree_marking_form :
    (N₃) = C ((N₃).coeff 3) * (T 1 - 1) ^ 3 +
      C ((N₃).coeff 2 + 3 * (N₃).coeff 3) * T 1 * (T 1 - 1) +
      C (eval₂ (RingHom.id (Ring K 1)) 1 (N₃)) * T 1 := by
  conv_lhs => rw [completePointFirstPoleThree_polynomial K n h i]
  rw [completePointFirstPoleThree_marking_value]
  simp only [map_add, map_mul, map_ofNat]
  have ht2 : (T (2 : ℤ) : (Ring K 1)[T;T⁻¹]) = T 1 ^ 2 := by
    rw [T_pow]
    norm_num
  have ht3 : (T (3 : ℤ) : (Ring K 1)[T;T⁻¹]) = T 1 ^ 3 := by
    rw [T_pow]
    norm_num
  rw [ht2, ht3]
  ring

end FLT.Mazur.PolygonInfinitesimalStages
