/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstNodePolynomial
public import FLT.Mazur.PolygonCompletePointFirstIncomingValues

/-!
# Complete first-order marked forms in the original node ring

Both original Laurent branches are reconstructed. The two-cycle correction
is retained explicitly, with the unchanged common unit and lower coefficients.
These identities hold before quotienting the node ring or changing any lift.
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
local notation "N₂" => completePointStagePoleTwoChartNumerator K n h 1 i i
local notation "N₃" => completePointStagePoleThreeChartNumerator K n h 1 i i
local notation "P₂" => leftLaurentMap (t) (N₂)
local notation "P₃" => leftLaurentMap (t) (N₃)
local notation "λ" => (completePointStageCommonMarkingUnit K n h 1 i : Ring K 1)
local notation "twoCycle" => Equiv.symm (finRotate n) (Equiv.symm (finRotate n) i) = i

/-- The original quadratic node numerator includes its exact incoming two-cycle term. -/
theorem completePointFirstPoleTwo_node_marking_form :
    (N₂) = (ρ) ((P₂).coeff 2) * ((x) - 1) ^ 2 + (ρ) ((λ) ^ 2) * (x) +
      (ρ) (if twoCycle then (t) * (λ) ^ 2 else 0) * (y) := by
  conv_lhs => rw [completePointFirstPoleTwo_node_polynomial K n h i]
  rw [completePointFirstPoleTwo_incoming_value K n h i,
    ← completePointFirstPoleTwo_coefficient_unit K n h i]
  simp only [map_add, map_mul, map_ofNat]
  ring

/-- The original cubic node numerator keeps the actual lower coefficient on both branches. -/
theorem completePointFirstPoleThree_node_marking_form :
    (N₃) = (ρ) ((P₃).coeff 3) * ((x) - 1) ^ 3 +
      (ρ) ((P₃).coeff 2 + 3 * (P₃).coeff 3) * (x) * ((x) - 1) +
      (ρ) ((λ) ^ 3) * (x) +
      (ρ) (if twoCycle then -(t) * ((P₃).coeff 2 + 3 * (P₃).coeff 3) else 0) * (y) := by
  conv_lhs => rw [completePointFirstPoleThree_node_polynomial K n h i]
  rw [completePointFirstPoleThree_incoming_value K n h i,
    ← completePointFirstPoleThree_coefficient_unit K n h i]
  simp only [map_add, map_mul, map_ofNat]
  ring

end FLT.Mazur.PolygonInfinitesimalStages
