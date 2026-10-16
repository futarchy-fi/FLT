/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstNegativeVanishing

/-!
# Exact degree bounds for first-order retained polynomial numerators

The other unmarked edge kills the upper end coefficient, also for the
two-gon. The outgoing Laurent numerator is its original polynomial of
degree at most d; its central coefficients are retained, not normalized.
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

/-- The outgoing coefficient at 1 on the predecessor is killed by the parameter. -/
theorem completePointFirstNumerator_predecessor_one (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    (t) * (leftLaurentMap (t) (N (p) d s)).coeff 1 = 0 := by
  have he := completePointStageChartNumerator_laurent K n h 1 i (p) d s
  have hz : (t) * (precedingLaurentMap (Ring K 1) (t) (N (q) d s)).coeff 1 = 0 := by
    rw [show (1 : ℤ) = (1 : ℕ) by rfl, branch_coefficient_nonneg, pow_one,
      ← mul_assoc, ← pow_two, parameter_pow, zero_mul]
  by_cases hqi : (q) = i
  · have he' : (C (t) * T (-1) - 1) ^ d *
        precedingLaurentMap (Ring K 1) (t) (N (q) d s) =
        (C (t) * T 1 - 1) ^ d * leftLaurentMap (t) (N (p) d s) := by
      simpa only [PolygonInfinitesimal.chartMarkingEquation, PolygonCyclicAtlas.prev_ne h i,
        hqi, ite_false, ite_true, inv_one, Units.val_one, map_sub, map_one,
        leftLaurentMap_right, precedingLaurentMap_left] using he
    have ht := congrArg (fun z ↦ C (t) * z) he'
    rw [LaurentSquareZeroMarking.parameter_marking_pow_mul (t) (parameter_pow K 1),
      LaurentSquareZeroMarking.parameter_marking_pow_mul (t) (parameter_pow K 1)] at ht
    have hc := congrArg (fun z : (Ring K 1)[T;T⁻¹] ↦ z.coeff 1) ht
    simp only [← single_eq_C, AddMonoidAlgebra.coeff_single_mul_apply,
      neg_zero, zero_add] at hc
    apply (((isUnit_one : IsUnit (1 : Ring K 1)).neg).pow d).isRegular.left
    dsimp only
    rw [mul_zero, ← mul_assoc, mul_comm ((-1 : Ring K 1) ^ d) (t), ← hc,
      mul_comm (t), mul_assoc, hz, mul_zero]
  · have he' : (C (t) * T (-1) - 1) ^ d *
        precedingLaurentMap (Ring K 1) (t) (N (q) d s) =
        leftLaurentMap (t) (N (p) d s) := by
      simpa only [PolygonInfinitesimal.chartMarkingEquation, PolygonCyclicAtlas.prev_ne h i,
        hqi, PolygonCyclicAtlas.prev_ne h (p), ite_false, ite_true, inv_one,
        Units.val_one, map_sub, map_one, leftLaurentMap_right, one_pow, one_mul] using he
    have ht := congrArg (fun z ↦ C (t) * z) he'
    rw [LaurentSquareZeroMarking.parameter_marking_pow_mul (t) (parameter_pow K 1)] at ht
    have hc := congrArg (fun z : (Ring K 1)[T;T⁻¹] ↦ z.coeff 1) ht
    simp only [← single_eq_C, AddMonoidAlgebra.coeff_single_mul_apply,
      neg_zero, zero_add] at hc
    rw [← hc, mul_comm (t), mul_assoc, hz, mul_zero]

/-- The actual coefficient beyond the original degree vanishes on every first-stage polygon. -/
theorem completePointFirstNumerator_upper_vanishes (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    (leftLaurentMap (t) (N i d s)).coeff ((d : ℤ) + 1) = 0 := by
  have hu := completePointStageNumerator_upper_parameter K n h 1 i d s 1
  simp only [Nat.cast_one, pow_one, add_comm (1 : ℤ)] at hu
  rw [hu, mul_assoc,
    completePointFirstNumerator_predecessor_one K n h i d s, mul_zero]

/-- The unchanged retained numerator has precisely the original degree bound at order one. -/
theorem completePointFirstNumerator_degree_support (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    (leftLaurentMap (t) (N i d s)).coeff.support ⊆ Finset.Icc (0 : ℤ) d := by
  intro k hk
  have hb := Finset.mem_Icc.mp (completePointFirstNumerator_polynomial_support K n h i d s hk)
  refine Finset.mem_Icc.mpr ⟨hb.1, ?_⟩
  by_contra he
  have hk' : k = (d : ℤ) + 1 := by omega
  exact (Finsupp.mem_support_iff.mp hk)
    (by rw [hk', completePointFirstNumerator_upper_vanishes K n h i d s])

/-- The outgoing retained numerator is the finite polynomial of its unchanged degree-d data. -/
theorem completePointFirstNumerator_degree_expansion (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    leftLaurentMap (t) (N i d s) = ∑ k ∈ Finset.Icc (0 : ℤ) d,
      C ((leftLaurentMap (t) (N i d s)).coeff k) * T k := by
  have hs := completePointFirstNumerator_degree_support K n h i d s
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single (leftLaurentMap (t) (N i d s))]
  change (leftLaurentMap (t) (N i d s)).coeff.sum AddMonoidAlgebra.single = _
  rw [Finsupp.sum_of_support_subset _ hs
    (fun k r ↦ (AddMonoidAlgebra.single k r : (Ring K 1)[T;T⁻¹]))
    (by intro k _; exact AddMonoidAlgebra.single_zero k)]
  simp only [single_eq_C_mul_T]

end FLT.Mazur.PolygonInfinitesimalStages
