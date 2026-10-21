/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentFiniteSubgroup
public import FLT.Mazur.OneGonAdicIndependentStageRefinement

/-!
# Independence of smooth witnesses under actual stage refinement

Two supplied smooth factorizations become the same finite subgroup at every
shared coefficient refinement. No choice of a preferred factor or functorial
choice of smooth stages is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open Approximation OneGonSmoothing WeierstrassIntegralChart OneGonAdicCharacterTower
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s : Set R)
  {i k : (CoefficientStage (base I t ht n s))ᵒᵖ} (α : k ⟶ i)
  (b : (coefficientModelDiagram (base I t ht n s) (carrier I t ht n s).hom).obj i ⟶
    (integralSmoothOpen (equation (parameter I t ht n s))).toScheme)
  (hb : b ≫ (integralSmoothOpen (equation (parameter I t ht n s))).ι =
    (coefficientModelToInitial (base I t ht n s) (carrier I t ht n s).hom).app i ≫
      embedding I t ht n s)

variable (hi : complementaryInverse I t ht ∈ s)
  (hφ : Function.Surjective (OneGonFiniteCoefficientCoordinates.modelCoordinates t 1
    (canonicalCoordinates I t ht n) s))

/-- Refining a supplied factor gives the finite subgroup of the actual new stage. -/
def refinedFiniteSubgroup :=
  stageFiniteSubgroup I t ht n s k (refinedFactor I t ht n s α b)
    (refinedFactor_inclusion I t ht n s α b hb) hi hφ

/-- Every shared refinement identifies the entire subgroups of two supplied smooth witnesses. -/
theorem refinedFiniteSubgroup_unique
    {j : (CoefficientStage (base I t ht n s))ᵒᵖ} (β : k ⟶ j)
    (c : (coefficientModelDiagram (base I t ht n s) (carrier I t ht n s).hom).obj j ⟶
      (integralSmoothOpen (equation (parameter I t ht n s))).toScheme)
    (hc : c ≫ (integralSmoothOpen (equation (parameter I t ht n s))).ι =
      (coefficientModelToInitial (base I t ht n s) (carrier I t ht n s).hom).app j ≫
        embedding I t ht n s) :
    refinedFiniteSubgroup I t ht n s α b hb hi hφ =
      refinedFiniteSubgroup I t ht n s β c hc hi hφ := by
  unfold refinedFiniteSubgroup
  congr 1
  exact refinedFactor_unique I t ht n s α b hb β c hc

/-- Direct and successive refinements have exactly the same whole finite subgroup. -/
theorem refinedFiniteSubgroup_comp
    {l : (CoefficientStage (base I t ht n s))ᵒᵖ} (β : l ⟶ k) :
    refinedFiniteSubgroup I t ht n s (β ≫ α) b hb hi hφ =
      refinedFiniteSubgroup I t ht n s β (refinedFactor I t ht n s α b)
        (refinedFactor_inclusion I t ht n s α b hb) hi hφ := by
  apply refinedFiniteSubgroup_unique

end FLT.Mazur.OneGonAdicIndependentModel
