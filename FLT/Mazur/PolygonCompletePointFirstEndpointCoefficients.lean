/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstConstantEdges
public import FLT.Mazur.CyclicOmittedEdgeConstancy

/-!
# The first-order numerator endpoint relation around the entire cycle

Transporting the constant coefficient across all edges except the marked
one equates the original chart and predecessor constants. The marked edge
then gives the exact signed relation between the two endpoint coefficients.
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


/-- The constants at the two original marked charts agree after traversing the full cycle. -/
theorem completePointFirstNumerator_constant_cycle (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    (leftLaurentMap (t) (N (p) d s)).coeff 0 =
      (leftLaurentMap (t) (N i d s)).coeff 0 := by
  let v : Fin n → Ring K 1 := fun j ↦
    (if j = i ∨ j = (p) then (-1 : Ring K 1) ^ d else 1) *
      (leftLaurentMap (t) (N j d s)).coeff 0
  have hn : 0 < n := by omega
  have hv (j : Fin n) (hj : PolygonPinching.next hn j ≠ i) :
      v (PolygonPinching.next hn j) = v j := by
    have hnxt (k : Fin n) : PolygonPinching.next hn k = finRotate n k := by
      rw [PolygonPinching.next_eq_add_one, finRotate_apply]
    rw [hnxt] at hj ⊢
    have he := completePointFirstNumerator_weighted_constant_edge K n h i
      (finRotate n j) hj d s
    simpa only [Equiv.symm_apply_apply] using he
  have he := PolygonPinching.eq_of_omitted_edge hn v i hv (p)
  dsimp only [v] at he
  simp only [true_or, or_true, ite_true] at he
  exact (((isUnit_one : IsUnit (1 : Ring K 1)).neg).pow d).isRegular.left he

/-- The central polynomial has the original signed equality of its endpoint coefficients. -/
theorem completePointFirstNumerator_endpoints (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    (leftLaurentMap (t) (N i d s)).coeff 0 =
      (-1 : Ring K 1) ^ d * (leftLaurentMap (t) (N i d s)).coeff d := by
  have he := completePointStageNumerator_marked_coefficient K n h 1 i d s 0
  rw [zero_add, branch_coefficient_zero,
    completePointFirstNumerator_constant_cycle K n h i d s] at he
  exact he

/-- The unchanged pole-two numerator has equal constant and quadratic coefficients. -/
theorem completePointFirstPoleTwo_endpoints :
    (leftLaurentMap (t) (N i 2 (completePointStagePoleTwo K n h 1 i))).coeff 0 =
      (leftLaurentMap (t) (N i 2 (completePointStagePoleTwo K n h 1 i))).coeff 2 := by
  simpa using completePointFirstNumerator_endpoints K n h i 2
    (completePointStagePoleTwo K n h 1 i)

/-- The unchanged pole-three numerator has opposite constant and cubic coefficients. -/
theorem completePointFirstPoleThree_endpoints :
    (leftLaurentMap (t) (N i 3 (completePointStagePoleThree K n h 1 i))).coeff 0 =
      -(leftLaurentMap (t) (N i 3 (completePointStagePoleThree K n h 1 i))).coeff 3 := by
  simpa only [Odd.neg_pow (by decide : Odd 3), one_pow, neg_one_mul, Nat.cast_ofNat]
    using completePointFirstNumerator_endpoints K n h i 3
    (completePointStagePoleThree K n h 1 i)

end FLT.Mazur.PolygonInfinitesimalStages
