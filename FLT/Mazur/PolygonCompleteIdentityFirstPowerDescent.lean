/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentBoundaryTailShift
public import FLT.Mazur.PolygonCompleteIdentityFirstDefectDerivation
public import FLT.Mazur.PolygonCompleteIdentityFirstPrincipalCoordinates

/-!
# Unconditional original action descent on high coordinate powers

The original coefficient defect is a derivation with finite Laurent values.
Positive powers of each actual node coordinate clear its poles, so some
positive power of each coordinate has an original action image in the full
node subalgebra. This is partial preservation, not descent of either generator.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentFirstStageParameter
open LaurentNodePrincipalParts LaurentBoundaryTailShift
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "e" => parameter (R) 1
local notation "N" => ChartRing (0 : R)
local notation "O" => completeIdentityFiniteMulObstruction K n h i 0
local notation "Q" => completeIdentityFirstReciprocalError K n h i
local notation "D" => completeIdentityFirstDefectCoefficient K n h i
local notation "A" => completeIdentityFirstReducedScaling K
local notation "a" => reduction (R) 1 (Units.val (parameterUnit K))
local notation "b" => reduction (R) 1 (Units.val (parameterUnit K)⁻¹)

/-- Exact power rule for the canonical coefficient of the unchanged original action defect. -/
theorem completeIdentityFirstDefectCoefficient_pow (z : N) (m : ℕ) :
    (D) (z ^ (m + 1)) = (m + 1) • ((A) z ^ m * (D) z) := by
  let _ := (A).toRingHom.toAlgebra
  have he := (completeIdentityFirstDefectDerivation K n h i).leibniz_pow z (m + 1)
  change (D) (z ^ (m + 1)) = (m + 1) • ((A) (z ^ (m + 1 - 1)) * (D) z) at he
  simpa only [Nat.add_sub_cancel, map_pow] using he

/-- The surviving left coordinate of reduced scaling retains the original parameter. -/
theorem completeIdentityFirstReducedScaling_left_fst :
    ((A) (leftCoordinate (0 : R))).1 = C (a) * T 1 := by
  change leftLaurentMap (0 : R) (reciprocalScale (0 : R) _ (leftCoordinate (0 : R))) = _
  rw [reciprocalScale_left, map_mul, AlgHom.commutes, leftLaurentMap_left]
  rfl

/-- The surviving right coordinate retains the inverse original parameter. -/
theorem completeIdentityFirstReducedScaling_right_snd :
    ((A) (rightCoordinate (0 : R))).2 = C (b) * T 1 := by
  change leftLaurentMap (0 : R) (branchSwapMap (0 : R)
    (reciprocalScale (0 : R) _ (rightCoordinate (0 : R)))) = _
  rw [reciprocalScale_right, map_mul, AlgHom.commutes, branchSwapMap_right,
    map_mul, AlgHom.commutes, leftLaurentMap_left]
  rfl

/-- The exact left-power coefficient has no contribution on the opposite branch. -/
theorem completeIdentityFirstDefectCoefficient_left_pow (m : ℕ) :
    (D) (leftCoordinate (0 : R) ^ (m + 1)) =
      ((m + 1) • ((C (a) * T 1) ^ m * (O)), 0) := by
  rw [completeIdentityFirstDefectCoefficient_pow, completeIdentityFirstDefectCoefficient_left]
  apply Prod.ext
  · change (m + 1) • (((A) (leftCoordinate (0 : R))).1 ^ m * (O)) = _
    rw [completeIdentityFirstReducedScaling_left_fst]
  · change (m + 1) • (((A) (leftCoordinate (0 : R))).2 ^ m * 0) = 0
    rw [mul_zero, nsmul_zero]

/-- The exact right-power coefficient likewise has only its original surviving branch. -/
theorem completeIdentityFirstDefectCoefficient_right_pow (m : ℕ) :
    (D) (rightCoordinate (0 : R) ^ (m + 1)) =
      (0, (m + 1) • ((C (b) * T 1) ^ m * (Q))) := by
  rw [completeIdentityFirstDefectCoefficient_pow, completeIdentityFirstDefectCoefficient_right]
  apply Prod.ext
  · change (m + 1) • (((A) (rightCoordinate (0 : R))).1 ^ m * 0) = 0
    rw [mul_zero, nsmul_zero]
  · change (m + 1) • (((A) (rightCoordinate (0 : R))).2 ^ m * (Q)) = _
    rw [completeIdentityFirstReducedScaling_right_snd]

/-- Some positive power of the original left coordinate descends under the unchanged action. -/
theorem completeIdentityFirstAction_left_power_descent :
    ∃ m : ℕ, 0 < m ∧ completeIdentityFirstActionBranchEquiv K n h i
      (firstNodeBranchPair (R) (leftCoordinate (e) ^ m)) ∈ firstNodeBranchSubalgebra (R) := by
  obtain ⟨m, _, hm⟩ := exists_scaled_power (a) (O)
  refine ⟨m + 1, by omega, ?_⟩
  apply (completeIdentityFirstNodeObstruction_eq_zero_iff K n h i _).mp
  apply (completeIdentityFirstPrincipalObstruction_eq_zero_iff K n h i _).mp
  change principalParts ((D) (firstNodeReduction (R) (leftCoordinate (e) ^ (m + 1)))) = 0
  rw [(firstNodeReduction (R)).map_pow, firstNodeReduction_left,
    completeIdentityFirstDefectCoefficient_left_pow]
  apply (firstNodeParameterPair_mem_iff (R) _).mp
  change (firstLaurentParameterLift (R) _, firstLaurentParameterLift (R) 0) ∈ _
  rw [firstLaurentParameterLift_zero, firstNodeBranchSubalgebra_parameter_left_iff]
  exact tail_nsmul_zero _ _ hm

/-- Some positive power of the original right coordinate also descends unconditionally. -/
theorem completeIdentityFirstAction_right_power_descent :
    ∃ m : ℕ, 0 < m ∧ completeIdentityFirstActionBranchEquiv K n h i
      (firstNodeBranchPair (R) (rightCoordinate (e) ^ m)) ∈ firstNodeBranchSubalgebra (R) := by
  obtain ⟨m, _, hm⟩ := exists_scaled_power (b) (Q)
  refine ⟨m + 1, by omega, ?_⟩
  apply (completeIdentityFirstNodeObstruction_eq_zero_iff K n h i _).mp
  apply (completeIdentityFirstPrincipalObstruction_eq_zero_iff K n h i _).mp
  change principalParts ((D) (firstNodeReduction (R) (rightCoordinate (e) ^ (m + 1)))) = 0
  rw [(firstNodeReduction (R)).map_pow, firstNodeReduction_right,
    completeIdentityFirstDefectCoefficient_right_pow]
  apply (firstNodeParameterPair_mem_iff (R) _).mp
  change (firstLaurentParameterLift (R) 0, firstLaurentParameterLift (R) _) ∈ _
  rw [firstLaurentParameterLift_zero, firstNodeBranchSubalgebra_parameter_right_iff]
  exact tail_nsmul_zero _ _ hm

end FLT.Mazur.PolygonInfinitesimalStages
