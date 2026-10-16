/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstComplementExtraction
public import FLT.Mazur.PolygonCompletePointNodeComplementNumerators

/-!
# Incoming coordinate extraction on the predecessor marking complement

The adjacent marking's actual pole functions recover the incoming
coordinate on the original predecessor chart. Only the fifth marking
unit is cancelled, leaving arbitrary receiving-ring nilpotents intact.
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
variable (v : Spec (.of D) ⟶
  (completePointStageNodeOpen K n h 1 i (Equiv.symm (finRotate n) i)).toScheme)
variable (hv : v ≫ (completePointStageNodeOpen K n h 1 i (Equiv.symm (finRotate n) i)).ι =
  Spec.map (CommRingCat.ofHom σ))
local notation "ψ" => completePointNodeComplementFunctions K n h 1 i (Equiv.symm (finRotate n) i) v
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
local notation "f₂" => (ψ) (completePointStageNodePoleTwo K n h 1 i (p))
local notation "f₃" => (ψ) (completePointStageNodePoleThree K n h 1 i (p))

include hv

/-- The original quadratic and cubic extract the incoming node coordinate exactly. -/
theorem completePointFirstComplementPoles_extract_preceding_right :
    ((y) - 1) ^ 3 * ((a) * ((f₃) - (B)) - ((C₀) - (b)) * ((f₂) - (A))) =
      -(σ) ((ρ) ((λ) ^ 5)) * (y) := by
  have he := congrArg (σ) (completePointFirstPoleNumerators_extract_preceding_right K n h i)
  simp only [σ.map_mul, σ.map_sub, σ.map_pow, σ.map_one, σ.map_neg] at he
  have h₂ : ((y) - 1) ^ 2 * (f₂) = (σ)
      (completePointStagePoleTwoChartNumerator K n h 1 i (p)) := by
    simpa only [PolygonInfinitesimal.chartMarkingEquation,
      PolygonCyclicAtlas.prev_ne h i, ite_false, ite_true, inv_one,
      Units.val_one, (ρ).map_one, σ.map_one, σ.map_sub] using
      completePointNodeComplementPoleTwo_bounded K n h 1 i (p) σ v hv
  have h₃ : ((y) - 1) ^ 3 * (f₃) = (σ)
      (completePointStagePoleThreeChartNumerator K n h 1 i (p)) := by
    simpa only [PolygonInfinitesimal.chartMarkingEquation,
      PolygonCyclicAtlas.prev_ne h i, ite_false, ite_true, inv_one,
      Units.val_one, (ρ).map_one, σ.map_one, σ.map_sub] using
      completePointNodeComplementPoleThree_bounded K n h 1 i (p) σ v hv
  rw [← h₂, ← h₃] at he
  convert he using 1
  ring

/-- The incoming coordinate is an explicit expression in the unchanged original pole functions. -/
theorem completePointFirstComplementPoles_recover_preceding_right :
    (y) = -(σ) ((ρ) (((u)⁻¹ : (Ring K 1)ˣ) ^ 5)) * ((y) - 1) ^ 3 *
      ((a) * ((f₃) - (B)) - ((C₀) - (b)) * ((f₂) - (A))) := by
  rw [mul_assoc, completePointFirstComplementPoles_extract_preceding_right K n h i σ v hv,
    ← mul_assoc, neg_mul_neg, completePointFirstComplementMarkingUnit_inv_fifth, one_mul]

end FLT.Mazur.PolygonInfinitesimalStages
