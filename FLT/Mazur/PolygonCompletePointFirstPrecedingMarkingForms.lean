/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstPrecedingPolynomial
public import FLT.Mazur.PolygonCompletePointFirstIncomingValues

/-!
# Exact first-order marking forms on the predecessor node

The original common unit and lower coefficients determine both incoming
polynomials and their outgoing two-cycle corrections. No section is changed.
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
local notation "λ" => (completePointStageCommonMarkingUnit K n h 1 i : Ring K 1)

/-- The full predecessor quadratic has the same unit and its exact outgoing correction. -/
theorem completePointFirstPoleTwo_preceding_node_marking_form :
    (N₂ (p)) = (ρ) ((P₂).coeff 2) * ((y) - 1) ^ 2 + (ρ) ((λ) ^ 2) * (y) +
      (ρ) (if twoCycle then (t) * (λ) ^ 2 else 0) * (x) := by
  conv_lhs => rw [completePointFirstPoleTwo_preceding_node_polynomial K n h i]
  rw [← completePointFirstPoleTwo_coefficient_unit K n h i]
  have hc : (P₂).coeff 1 + 2 * (P₂).coeff 2 = 2 * (P₂).coeff 2 + (P₂).coeff 1 :=
    add_comm _ _
  rw [hc]
  simp only [map_add, map_mul, map_ofNat]
  ring

/-- The full predecessor cubic keeps the signed unit term and the two-cycle correction. -/
theorem completePointFirstPoleThree_preceding_node_marking_form :
    (N₃ (p)) = (ρ) ((P₃).coeff 3) * ((y) - 1) ^ 3 +
      (ρ) ((P₃).coeff 2 + 3 * (P₃).coeff 3 - (λ) ^ 3) * (y) * ((y) - 1) -
      (ρ) ((λ) ^ 3) * (y) +
      (ρ) (if twoCycle then (t) *
        ((λ) ^ 3 - ((P₃).coeff 2 + 3 * (P₃).coeff 3)) else 0) * (x) := by
  conv_lhs => rw [completePointFirstPoleThree_preceding_node_polynomial K n h i]
  rw [← completePointFirstPoleThree_coefficient_unit K n h i]
  have hc : (P₃).coeff 1 - 3 * (P₃).coeff 3 =
      (P₃).coeff 1 + (P₃).coeff 2 - ((P₃).coeff 2 + 3 * (P₃).coeff 3) := by ring
  rw [hc]
  simp only [map_add, map_sub, map_mul, map_ofNat]
  ring

end FLT.Mazur.PolygonInfinitesimalStages
