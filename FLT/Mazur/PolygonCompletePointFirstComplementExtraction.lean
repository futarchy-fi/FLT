/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstNodeCoordinateNumerators
public import FLT.Mazur.PolygonCompletePointNodeComplementNumerators

/-!
# Outgoing coordinate extraction on the entire original marking complement

The retained pole functions recover the original outgoing coordinate under
any chart map into the marking complement. No incoming marking denominator
is inverted; the actual fifth marking unit is the only coefficient cancelled.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj FCurve.ModuleSheafTensor.tensor FCurve.divisorLineBundle
  completePointStageNodeOpen completePointStageCommonMarkingUnit
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "t" => parameter K 1
local notation "ρ" => algebraMap (Ring K 1) (ChartRing (t))
variable {D : Type} [CommRing D] (σ : ChartRing (parameter K 1) →+* D)
variable (v : Spec (.of D) ⟶ (completePointStageNodeOpen K n h 1 i i).toScheme)
variable (hv : v ≫ (completePointStageNodeOpen K n h 1 i i).ι =
  Spec.map (CommRingCat.ofHom σ))
local notation "ψ" => completePointNodeComplementFunctions K n h 1 i i v
local notation "x" => (σ) (leftCoordinate (t))
local notation "y" => (σ) (rightCoordinate (t))
local notation "p" => Equiv.symm (finRotate n) i
local notation "P₂" => leftLaurentMap (t)
  (completePointStagePoleTwoChartNumerator K n h 1 i i)
local notation "P₃" => leftLaurentMap (t)
  (completePointStagePoleThreeChartNumerator K n h 1 i i)
local notation "u" => completePointStageCommonMarkingUnit K n h 1 i
local notation "λ" => (u : Ring K 1)
local notation "A" => (σ) ((ρ) (AddMonoidAlgebra.coeff (P₂) 2))
local notation "B" => (σ) ((ρ) (AddMonoidAlgebra.coeff (P₃) 3))
local notation "C₀" => (σ) ((ρ) (AddMonoidAlgebra.coeff (P₃) 2 + 3 * AddMonoidAlgebra.coeff (P₃) 3))
local notation "a" => (σ) ((ρ) ((λ) ^ 2))
local notation "b" => (σ) ((ρ) ((λ) ^ 3))
local notation "f₂" => (ψ) (completePointStageNodePoleTwo K n h 1 i i)
local notation "f₃" => (ψ) (completePointStageNodePoleThree K n h 1 i i)

include hv

/-- The original quadratic and cubic extract the outgoing node coordinate exactly. -/
theorem completePointFirstComplementPoles_extract_left :
    ((x) - 1) ^ 3 * ((a) * ((f₃) - (B)) - (C₀) * ((f₂) - (A))) =
      (σ) ((ρ) ((λ) ^ 5)) * (x) := by
  have he := congrArg (σ) (completePointFirstPoleNumerators_extract_left K n h i)
  simp only [σ.map_mul, σ.map_sub, σ.map_pow, σ.map_one] at he
  have h₂ : ((x) - 1) ^ 2 * (f₂) = (σ)
      (completePointStagePoleTwoChartNumerator K n h 1 i i) := by
    simpa only [PolygonInfinitesimal.chartMarkingEquation, ite_true,
      Units.val_one, (ρ).map_one, σ.map_one, σ.map_sub] using
      completePointNodeComplementPoleTwo_bounded K n h 1 i i σ v hv
  have h₃ : ((x) - 1) ^ 3 * (f₃) = (σ)
      (completePointStagePoleThreeChartNumerator K n h 1 i i) := by
    simpa only [PolygonInfinitesimal.chartMarkingEquation, ite_true,
      Units.val_one, (ρ).map_one, σ.map_one, σ.map_sub] using
      completePointNodeComplementPoleThree_bounded K n h 1 i i σ v hv
  rw [← h₂, ← h₃] at he
  convert he using 1
  ring

omit hv in
/-- The inverse fifth marking unit cancels its coefficient in the unchanged receiving ring. -/
theorem completePointFirstComplementMarkingUnit_inv_fifth :
    (σ) ((ρ) (((u)⁻¹ : (Ring K 1)ˣ) ^ 5)) * (σ) ((ρ) ((λ) ^ 5)) = 1 := by
  rw [← σ.map_mul, ← (ρ).map_mul]
  simp only [← mul_pow, Units.inv_mul, one_pow, map_one]

/-- The outgoing coordinate is an explicit expression in the unchanged original pole functions. -/
theorem completePointFirstComplementPoles_recover_left :
    (x) = (σ) ((ρ) (((u)⁻¹ : (Ring K 1)ˣ) ^ 5)) * ((x) - 1) ^ 3 *
      ((a) * ((f₃) - (B)) - (C₀) * ((f₂) - (A))) := by
  rw [mul_assoc, completePointFirstComplementPoles_extract_left K n h i σ v hv,
    ← mul_assoc, completePointFirstComplementMarkingUnit_inv_fifth, one_mul]

end FLT.Mazur.PolygonInfinitesimalStages
