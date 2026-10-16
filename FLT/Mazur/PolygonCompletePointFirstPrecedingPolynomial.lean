/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstPrecedingLifts

/-!
# Full retained numerators on the predecessor marked chart

Both branches reconstruct the unchanged original node element. All lower
coefficients and the extra outgoing term on a two-cycle remain explicit.
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
local notation "N₂" => completePointStagePoleTwoChartNumerator K n h 1 i
local notation "N₃" => completePointStagePoleThreeChartNumerator K n h 1 i
local notation "P₂" => leftLaurentMap (t) (N₂ i)
local notation "P₃" => leftLaurentMap (t) (N₃ i)

/-- Both branches reconstruct the original predecessor quadratic with its two-cycle term. -/
theorem completePointFirstPoleTwo_preceding_node_polynomial :
    (N₂ (p)) = (ρ) ((P₂).coeff 2) +
      (ρ) (if twoCycle then (t) * ((P₂).coeff 1 + 2 * (P₂).coeff 2) else 0) * (x) +
      ((ρ) ((P₂).coeff 2) * (y) ^ 2 + (ρ) ((P₂).coeff 1) * (y)) := by
  calc
    (N₂ (p)) = outgoingPolynomialLift (t) (leftLaurentMap (t) (N₂ (p))) +
        incomingPolynomialLift (t) (precedingLaurentMap (Ring K 1) (t) (N₂ (p))) :=
      laurent_reconstruction (t) _
    _ = _ := by
      rw [completePointFirstPoleTwo_preceding_incoming_lift K n h i]
      have he := completePointFirstNumerator_preceding_outgoing_lift K n h i 2
        (completePointStagePoleTwo K n h 1 i)
      rw [completePointFirstPoleTwo_endpoints K n h i] at he
      simpa only [Nat.cast_ofNat, completePointStagePoleTwoChartNumerator] using
        congrArg (fun z ↦ z + ((ρ) ((P₂).coeff 2) * (y) ^ 2 +
          (ρ) ((P₂).coeff 1) * (y))) he

/-- The full original predecessor cubic retains its signed coefficients on both branches. -/
theorem completePointFirstPoleThree_preceding_node_polynomial :
    (N₃ (p)) = -(ρ) ((P₃).coeff 3) +
      (ρ) (if twoCycle then (t) * ((P₃).coeff 1 - 3 * (P₃).coeff 3) else 0) * (x) +
      ((ρ) ((P₃).coeff 3) * (y) ^ 3 - (ρ) ((P₃).coeff 1) * (y) ^ 2 -
        (ρ) ((P₃).coeff 2) * (y)) := by
  calc
    (N₃ (p)) = outgoingPolynomialLift (t) (leftLaurentMap (t) (N₃ (p))) +
        incomingPolynomialLift (t) (precedingLaurentMap (Ring K 1) (t) (N₃ (p))) :=
      laurent_reconstruction (t) _
    _ = _ := by
      rw [completePointFirstPoleThree_preceding_incoming_lift K n h i]
      have he := completePointFirstNumerator_preceding_outgoing_lift K n h i 3
        (completePointStagePoleThree K n h 1 i)
      rw [completePointFirstPoleThree_endpoints K n h i] at he
      simp only [Nat.cast_ofNat, map_neg, mul_neg, ← sub_eq_add_neg] at he
      exact congrArg (fun z ↦ z + ((ρ) ((P₃).coeff 3) * (y) ^ 3 -
          (ρ) ((P₃).coeff 1) * (y) ^ 2 - (ρ) ((P₃).coeff 2) * (y))) he

end FLT.Mazur.PolygonInfinitesimalStages
