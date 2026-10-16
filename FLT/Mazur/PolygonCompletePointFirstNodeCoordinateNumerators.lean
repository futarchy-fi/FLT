/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodePoleCoordinateExtraction
public import FLT.Mazur.PolygonCompletePointFirstNodeMarkingForms
public import FLT.Mazur.PolygonCompletePointFirstPrecedingMarkingForms

/-!
# Extract original node coordinates from the retained pole numerators

A triangular combination eliminates the actual lower cubic coefficient.
Both two-cycle corrections cancel in the full node ring using t squared,
without dividing by t or changing any complete section.
-/

@[expose] public noncomputable section
open AlgebraicGeometry Scheme.Modules
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing FCurve ModuleLineBundleTensorPullback LaurentPolynomial
open NodePoleCoordinateExtraction
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
local notation "A" => (ρ) (AddMonoidAlgebra.coeff (P₂) 2)
local notation "B" => (ρ) (AddMonoidAlgebra.coeff (P₃) 3)
local notation "C₀" => (ρ) (AddMonoidAlgebra.coeff (P₃) 2 + 3 * AddMonoidAlgebra.coeff (P₃) 3)

/-- The original outgoing coordinate is extracted with a fifth power of the unchanged unit. -/
theorem completePointFirstPoleNumerators_extract_left :
    (ρ) ((λ) ^ 2) * (N₃ i - (B) * ((x) - 1) ^ 3) -
      (C₀) * ((x) - 1) * (N₂ i - (A) * ((x) - 1) ^ 2) = (ρ) ((λ) ^ 5) * (x) := by
  let e : ChartRing (t) := if twoCycle then (ρ) (t) else 0
  have ht : ((ρ) (t)) ^ 2 = 0 := by rw [← map_pow, parameter_pow K 1, map_zero]
  have he : e * (x) * (y) = 0 := correction_mixed (x) (y) ((ρ) (t))
    (coordinate_relation (t)) ht twoCycle
  have h₂ : N₂ i = (A) * ((x) - 1) ^ 2 + (ρ) ((λ) ^ 2) * (x) +
      (ρ) ((λ) ^ 2) * e * (y) := by
    conv_lhs => rw [completePointFirstPoleTwo_node_marking_form K n h i]
    dsimp only [e]
    split_ifs <;> simp only [map_mul, map_zero, mul_zero, zero_mul]
    ring
  have h₃ : N₃ i = (B) * ((x) - 1) ^ 3 + (C₀) * (x) * ((x) - 1) +
      (ρ) ((λ) ^ 3) * (x) - (C₀) * e * (y) := by
    conv_lhs => rw [completePointFirstPoleThree_node_marking_form K n h i]
    dsimp only [e]
    split_ifs <;> simp only [map_mul, map_neg, map_zero, mul_zero, zero_mul] <;> ring
  have hh := extract_numerators (x) (y) e ((ρ) ((λ) ^ 2)) ((ρ) ((λ) ^ 3))
    (C₀) (A) (B) (N₂ i) (N₃ i) he h₂ h₃
  simp only [← map_mul, ← pow_add] at hh
  exact hh

/-- The predecessor incoming coordinate is extracted with the same unit and opposite sign. -/
theorem completePointFirstPoleNumerators_extract_preceding_right :
    (ρ) ((λ) ^ 2) * (N₃ (p) - (B) * ((y) - 1) ^ 3) -
      ((C₀) - (ρ) ((λ) ^ 3)) * ((y) - 1) *
        (N₂ (p) - (A) * ((y) - 1) ^ 2) = -((ρ) ((λ) ^ 5)) * (y) := by
  let e : ChartRing (t) := if twoCycle then (ρ) (t) else 0
  have ht : ((ρ) (t)) ^ 2 = 0 := by rw [← map_pow, parameter_pow K 1, map_zero]
  have he : e * (y) * (x) = 0 := correction_mixed (y) (x) ((ρ) (t))
    (by rw [mul_comm, coordinate_relation]) ht twoCycle
  have h₂ : N₂ (p) = (A) * ((y) - 1) ^ 2 + (ρ) ((λ) ^ 2) * (y) +
      (ρ) ((λ) ^ 2) * e * (x) := by
    conv_lhs => rw [completePointFirstPoleTwo_preceding_node_marking_form K n h i]
    dsimp only [e]
    split_ifs <;> simp only [map_mul, map_zero, mul_zero, zero_mul]
    ring
  have h₃ : N₃ (p) = (B) * ((y) - 1) ^ 3 +
      ((C₀) - (ρ) ((λ) ^ 3)) * (y) * ((y) - 1) +
      (-((ρ) ((λ) ^ 3))) * (y) - ((C₀) - (ρ) ((λ) ^ 3)) * e * (x) := by
    conv_lhs => rw [completePointFirstPoleThree_preceding_node_marking_form K n h i]
    dsimp only [e]
    split_ifs <;> simp only [map_sub, map_mul, map_zero, mul_zero, zero_mul] <;> ring
  have hh := extract_numerators (y) (x) e ((ρ) ((λ) ^ 2)) (-((ρ) ((λ) ^ 3)))
    ((C₀) - (ρ) ((λ) ^ 3)) (A) (B) (N₂ (p)) (N₃ (p)) he h₂ h₃
  rw [hh]
  simp only [map_pow]
  ring

end FLT.Mazur.PolygonInfinitesimalStages
