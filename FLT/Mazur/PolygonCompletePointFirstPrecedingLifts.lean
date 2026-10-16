/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstPrecedingCoefficients
public import FLT.Mazur.PolygonCompletePointFirstCentralCoefficients
public import FLT.Mazur.LaurentReciprocalFiniteLifts

/-!
# Complementary lifts on the original predecessor chart

The outgoing part includes the exact two-cycle correction. The incoming
quadratic and cubic parts retain the original central coefficients and signs.
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
local notation "ρ" => algebraMap (Ring K 1) (ChartRing (t))
local notation "x" => leftCoordinate (t)
local notation "y" => rightCoordinate (t)
local notation "p" => Equiv.symm (finRotate n) i
local notation "twoCycle" => Equiv.symm (finRotate n) (p) = i
local notation "L" => originalStageSinglePointLine K n h 1 i
local notation "N" => completePointStageChartNumerator K n h 1 i
local notation "N₂" => completePointStagePoleTwoChartNumerator K n h 1 i
local notation "N₃" => completePointStagePoleThreeChartNumerator K n h 1 i
local notation "P₂" => leftLaurentMap (t) (N₂ i)
local notation "P₃" => leftLaurentMap (t) (N₃ i)

/-- The exact outgoing lift on the predecessor retains its original constant and linear term. -/
theorem completePointFirstNumerator_preceding_outgoing_lift (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    outgoingPolynomialLift (t) (leftLaurentMap (t) (N (p) d s)) =
      (ρ) ((leftLaurentMap (t) (N i d s)).coeff 0) +
      (ρ) (if twoCycle then (t) * ((leftLaurentMap (t) (N i d s)).coeff 1 +
        (d : Ring K 1) * (leftLaurentMap (t) (N i d s)).coeff 0) else 0) * (x) := by
  rw [outgoingPolynomialLift_linear (t) _
      (completePointFirstNumerator_preceding_above K n h i d s),
    completePointFirstNumerator_constant_cycle K n h i d s,
    completePointFirstNumerator_preceding_linear K n h i d s]

/-- The incoming quadratic lift retains the actual central constant and linear coefficient. -/
theorem completePointFirstPoleTwo_preceding_incoming_lift :
    incomingPolynomialLift (t) (precedingLaurentMap (Ring K 1) (t) (N₂ (p))) =
      (ρ) ((P₂).coeff 2) * (y) ^ 2 + (ρ) ((P₂).coeff 1) * (y) := by
  change incomingPolynomialLift (t) (precedingLaurentMap (Ring K 1) (t)
    (N (p) 2 (completePointStagePoleTwo K n h 1 i))) = _
  rw [completePointStageNumerator_marked_transition K n h 1 i]
  change incomingPolynomialLift (t) ((-T (-1)) ^ 2 * (P₂)) = _
  conv_lhs => rw [completePointFirstPoleTwo_polynomial K n h i]
  exact incomingPolynomialLift_reciprocal_quadratic (t) _ _

/-- The incoming cubic lift keeps all three original lower coefficients with their exact signs. -/
theorem completePointFirstPoleThree_preceding_incoming_lift :
    incomingPolynomialLift (t) (precedingLaurentMap (Ring K 1) (t) (N₃ (p))) =
      (ρ) ((P₃).coeff 3) * (y) ^ 3 - (ρ) ((P₃).coeff 1) * (y) ^ 2 -
        (ρ) ((P₃).coeff 2) * (y) := by
  change incomingPolynomialLift (t) (precedingLaurentMap (Ring K 1) (t)
    (N (p) 3 (completePointStagePoleThree K n h 1 i))) = _
  rw [completePointStageNumerator_marked_transition K n h 1 i]
  change incomingPolynomialLift (t) ((-T (-1)) ^ 3 * (P₃)) = _
  conv_lhs => rw [completePointFirstPoleThree_polynomial K n h i]
  exact incomingPolynomialLift_reciprocal_cubic (t) _ _ _

end FLT.Mazur.PolygonInfinitesimalStages
