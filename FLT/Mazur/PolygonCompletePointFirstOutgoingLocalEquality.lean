/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstComplementNodeExtraction
public import FLT.Mazur.NodePoleLocalSecant

/-!
# Exact outgoing coordinate equality in local source-node rings

Equal retained poles determine the actual coordinate whenever the source
coordinate belongs to the maximal ideal. All local-ring nilpotents remain.
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

variable (β : StageNodeLocalization K 1 →+* D)
local notation "η" => algebraMap (ChartRing (t)) (StageNodeLocalization K 1)
local notation "z" => β ((η) (leftCoordinate (t)))
local notation "r₂" => completePointNodeLocalizedPoleTwo K n h 1 i i
local notation "r₃" => completePointNodeLocalizedPoleThree K n h 1 i i
variable (hc : ∀ c : Ring K 1,
  σ (algebraMap (Ring K 1) (ChartRing (parameter K 1)) c) =
    β (algebraMap (ChartRing (parameter K 1)) (StageNodeLocalization K 1)
      (algebraMap (Ring K 1) (ChartRing (parameter K 1)) c)))
variable (h₂ : completePointNodeComplementFunctions K n h 1 i i v
  (completePointStageNodePoleTwo K n h 1 i i) =
    β (completePointNodeLocalizedPoleTwo K n h 1 i i))
variable (h₃ : completePointNodeComplementFunctions K n h 1 i i v
  (completePointStageNodePoleThree K n h 1 i i) =
    β (completePointNodeLocalizedPoleThree K n h 1 i i))

variable [IsLocalRing D]
include hv hc h₂ h₃

/-- The original retained poles force coordinate equality in the full local receiving ring. -/
theorem completePointFirstComplementPoles_eq_of_source_mem
    (hz : β (algebraMap (ChartRing (parameter K 1)) (StageNodeLocalization K 1)
      (leftCoordinate (parameter K 1))) ∈ IsLocalRing.maximalIdeal D) :
    (x) = (z) := by
  have ht := completePointFirstComplementPoles_extract_left K n h i σ v hv
  have hs := completePointFirstComplementPoles_source_extract K n h i σ v β hc h₂ h₃
  have hu : IsUnit ((σ) ((ρ) ((λ) ^ 5))) := by
    exact ((((u).isUnit.pow 5).map (ρ)).map σ)
  exact NodePoleSecant.eq_of_source_mem _ _ _ _ _ ht hs hu hz rfl

end FLT.Mazur.PolygonInfinitesimalStages
