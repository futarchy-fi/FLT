/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstLocalizedCoordinateExtraction
public import FLT.Mazur.PolygonCompletePointFirstIncomingComplementExtraction

/-!
# Node-coordinate comparison using the entire marking complement

Equal retained poles and original coefficient maps force the incoming
target coordinate to vanish whenever the source coordinate vanishes.
Only the original fifth marking unit is cancelled.
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
local notation "x" => (σ) (rightCoordinate (t))
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
local notation "f₂" => (ψ) (completePointStageNodePoleTwo K n h 1 i (Equiv.symm (finRotate n) i))
local notation "f₃" => (ψ) (completePointStageNodePoleThree K n h 1 i (Equiv.symm (finRotate n) i))

variable (β : StageNodeLocalization K 1 →+* D)
local notation "η" => algebraMap (ChartRing (t)) (StageNodeLocalization K 1)
local notation "z" => β ((η) (rightCoordinate (t)))
local notation "r₂" => completePointNodeLocalizedPoleTwo K n h 1 i (Equiv.symm (finRotate n) i)
local notation "r₃" => completePointNodeLocalizedPoleThree K n h 1 i (Equiv.symm (finRotate n) i)
variable (hc : ∀ c : Ring K 1,
  σ (algebraMap (Ring K 1) (ChartRing (parameter K 1)) c) =
    β (algebraMap (ChartRing (parameter K 1)) (StageNodeLocalization K 1)
      (algebraMap (Ring K 1) (ChartRing (parameter K 1)) c)))
variable (h₂ : completePointNodeComplementFunctions K n h 1 i (Equiv.symm (finRotate n) i) v
  (completePointStageNodePoleTwo K n h 1 i (Equiv.symm (finRotate n) i)) =
    β (completePointNodeLocalizedPoleTwo K n h 1 i (Equiv.symm (finRotate n) i)))
variable (h₃ : completePointNodeComplementFunctions K n h 1 i (Equiv.symm (finRotate n) i) v
  (completePointStageNodePoleThree K n h 1 i (Equiv.symm (finRotate n) i)) =
    β (completePointNodeLocalizedPoleThree K n h 1 i (Equiv.symm (finRotate n) i)))

include hc h₂ h₃

/-- The source extraction uses exactly the target coefficients and complement poles. -/
theorem completePointFirstIncomingComplementPoles_source_extract :
    ((z) - 1) ^ 3 * ((a) * ((f₃) - (B)) - ((C₀) - (b)) * ((f₂) - (A))) =
      -σ ((ρ) ((λ) ^ 5)) * (z) := by
  simp only [h₂, h₃, hc]
  simpa only [β.map_mul, β.map_sub, β.map_pow, β.map_one, β.map_neg] using
    congrArg β (completePointFirstNodePoles_extract_preceding_right K n h i)

include hv

/-- The actual incoming target vanishes in every full source-node receiving ring. -/
theorem completePointFirstIncomingComplementPoles_target_zero (hz : (z) = 0) : (x) = 0 := by
  have hs := completePointFirstIncomingComplementPoles_source_extract K n h i σ v β hc h₂ h₃
  have hu : (a) * ((f₃) - (B)) - ((C₀) - (b)) * ((f₂) - (A)) = 0 := by
    simpa only [hz, zero_sub, show (-1 : D) ^ 3 = -1 by ring,
      neg_mul, one_mul, mul_zero, neg_eq_zero] using hs
  rw [completePointFirstComplementPoles_recover_preceding_right K n h i σ v hv, hu, mul_zero]

end FLT.Mazur.PolygonInfinitesimalStages
