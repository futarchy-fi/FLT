/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstPrecedingMarkingForms
public import FLT.Mazur.PolygonCompletePointNodePoleEquations

/-!
# Marking forms of the unchanged predecessor node-localized functions

The reconstructed predecessor node numerators clear the actual original localized
pole functions with their specified denominators. Every lower coefficient
and the outgoing two-cycle correction remain present in these equations.
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
local notation "P₂" => leftLaurentMap (t)
  (completePointStagePoleTwoChartNumerator K n h 1 i i)
local notation "P₃" => leftLaurentMap (t)
  (completePointStagePoleThreeChartNumerator K n h 1 i i)
local notation "λ" => (completePointStageCommonMarkingUnit K n h 1 i : Ring K 1)
local notation "p" => Equiv.symm (finRotate n) i
local notation "twoCycle" => Equiv.symm (finRotate n) (Equiv.symm (finRotate n) i) = i

/-- The unchanged quadratic node function satisfies the full two-branch marked equation. -/
theorem completePointFirstNodePoleTwo_preceding_marking_form :
    ((y) - 1) ^ 2 * completePointNodeLocalizedPoleTwo K n h 1 i (p) =
      (σ) ((ρ) ((P₂).coeff 2)) * ((y) - 1) ^ 2 +
      (σ) ((ρ) ((λ) ^ 2)) * (y) +
      (σ) ((ρ) (if twoCycle then (t) * (λ) ^ 2 else 0)) * (x) := by
  conv_lhs => rw [completePointNodePoleTwo_preceding_equation,
    completePointFirstPoleTwo_preceding_node_marking_form K n h i]
  simp only [map_add, map_mul, map_pow, map_sub, map_one]

/-- The unchanged cubic node function retains the actual common unit and both lower terms. -/
theorem completePointFirstNodePoleThree_preceding_marking_form :
    ((y) - 1) ^ 3 * completePointNodeLocalizedPoleThree K n h 1 i (p) =
      (σ) ((ρ) ((P₃).coeff 3)) * ((y) - 1) ^ 3 +
      (σ) ((ρ) ((P₃).coeff 2 + 3 * (P₃).coeff 3 - (λ) ^ 3)) * (y) * ((y) - 1) -
      (σ) ((ρ) ((λ) ^ 3)) * (y) +
      (σ) ((ρ) (if twoCycle then (t) * ((λ) ^ 3 - ((P₃).coeff 2 + 3 * (P₃).coeff 3))
        else 0)) * (x) := by
  conv_lhs => rw [completePointNodePoleThree_preceding_equation,
    completePointFirstPoleThree_preceding_node_marking_form K n h i]
  simp only [map_add, map_mul, map_pow, map_sub, map_one]

end FLT.Mazur.PolygonInfinitesimalStages
