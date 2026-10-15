/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstLaurentPairProduct
public import FLT.Mazur.PolygonCompleteIdentityFirstPrincipalObstruction
public import FLT.Mazur.PolygonSmoothingScalingNaturality

/-!
# Product rule for the unchanged original reduced defect

The full original defect has square-zero values. Extracting its canonical
parameter coefficient gives a derivation relative to the original reduced
scaling. The product rule holds on every reduced node function, independently
of the still-unproved descent of these Laurent values to node functions.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentFirstStageParameter PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) 1
local notation "e" => parameter (R) 1
local notation "B" => ChartRing (e)
local notation "N" => ChartRing (0 : R)
local notation "D" => completeIdentityFirstActionNodeDefect K n h i
local notation "G" z => firstNodeBranchPair (R) (reciprocalScale (e) (parameterUnit K) z)

/-- Every full original defect value is annihilated by the smoothing parameter. -/
theorem completeIdentityFirstActionNodeDefect_parameter (z : B) : (e) • (D) z = 0 := by
  rw [← completeIdentityFirstReducedDefect_reduction K n h i z]
  exact completeIdentityFirstReducedDefect_parameter K n h i _

/-- Products of full original defect values vanish, not just their reductions. -/
theorem completeIdentityFirstActionNodeDefect_mul_zero (z w : B) : (D) z * (D) w = 0 :=
  firstNodePair_annihilator_mul (R) _ _
    (completeIdentityFirstActionNodeDefect_parameter K n h i z)
    (completeIdentityFirstActionNodeDefect_parameter K n h i w)

/-- The unchanged full action defect obeys the square-zero product rule. -/
theorem completeIdentityFirstActionNodeDefect_mul (z w : B) :
    (D) (z * w) = (D) z * (G w) + (D) w * (G z) := by
  have hz := completeIdentityFirstActionNodeDefect_mul_zero K n h i z w
  simp only [completeIdentityFirstActionNodeDefect_apply, map_mul] at hz ⊢
  linear_combination hz

/-- The reduced scaling used for the original coefficient-valued product rule. -/
def completeIdentityFirstReducedScaling : (N) →ₐ[R] ((R)[T;T⁻¹] × (R)[T;T⁻¹]) :=
  ((leftLaurentMap (0 : R)).prod
    ((leftLaurentMap (0 : R)).comp (branchSwapMap (0 : R)))).comp
      (reciprocalScale (0 : R)
        (Units.map (reduction (R) 1).toRingHom.toMonoidHom (parameterUnit K)))

/-- Reduction of the actual full scaling is exactly this unchanged reduced scaling. -/
theorem completeIdentityFirstReducedScaling_reduction (z : B) :
    completeIdentityFirstReducedScaling K (firstNodeReduction (R) z) =
      firstNodePairReduction (R) (G z) := by
  have hs := RingHom.congr_fun
    (ringMap_reciprocalScale (reduction (R) 1).toRingHom (e) 0
      (reduction_parameter (R) 1) (parameterUnit K)) z
  change firstNodeReduction (R) (reciprocalScale (e) (parameterUnit K) z) =
    reciprocalScale (0 : R)
      (Units.map (reduction (R) 1).toRingHom.toMonoidHom (parameterUnit K))
        (firstNodeReduction (R) z) at hs
  apply Prod.ext
  · change leftLaurentMap (0 : R) _ =
      coeffMap (reduction (R) 1).toRingHom
        (leftLaurentMap (e) (reciprocalScale (e) (parameterUnit K) z))
    rw [firstNodeReduction_leftLaurent, hs]
    rfl
  · change leftLaurentMap (0 : R) (branchSwapMap (0 : R) _) =
      coeffMap (reduction (R) 1).toRingHom
        (leftLaurentMap (e) (branchSwapMap (e)
          (reciprocalScale (e) (parameterUnit K) z)))
    rw [firstNodeReduction_leftLaurent, firstNodeReduction_swap, hs]
    rfl

/-- The actual coefficient map can be evaluated on any lift of a reduced node function. -/
theorem completeIdentityFirstDefectCoefficient_reduction (z : B) :
    completeIdentityFirstDefectCoefficient K n h i (firstNodeReduction (R) z) =
      firstNodePairCoefficient (R) ((D) z) := by
  change firstNodePairCoefficient (R)
    (completeIdentityFirstReducedDefect K n h i (firstNodeReduction (R) z)) = _
  rw [completeIdentityFirstReducedDefect_reduction]

/-- The canonical original coefficient defect satisfies the product rule on the entire node. -/
theorem completeIdentityFirstDefectCoefficient_mul (z w : N) :
    completeIdentityFirstDefectCoefficient K n h i (z * w) =
      completeIdentityFirstDefectCoefficient K n h i z *
        completeIdentityFirstReducedScaling K w +
      completeIdentityFirstDefectCoefficient K n h i w *
        completeIdentityFirstReducedScaling K z := by
  obtain ⟨a, rfl⟩ := firstNodeReduction_surjective (R) z
  obtain ⟨b, rfl⟩ := firstNodeReduction_surjective (R) w
  rw [← (firstNodeReduction (R)).map_mul,
    completeIdentityFirstDefectCoefficient_reduction,
    completeIdentityFirstActionNodeDefect_mul, map_add,
    firstNodePairCoefficient_mul (R) _ _
      (completeIdentityFirstActionNodeDefect_parameter K n h i a),
    firstNodePairCoefficient_mul (R) _ _
      (completeIdentityFirstActionNodeDefect_parameter K n h i b),
    completeIdentityFirstDefectCoefficient_reduction,
    completeIdentityFirstDefectCoefficient_reduction,
    completeIdentityFirstReducedScaling_reduction,
    completeIdentityFirstReducedScaling_reduction]

end FLT.Mazur.PolygonInfinitesimalStages
