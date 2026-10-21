/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientModelCommonRefinement
public import FLT.Mazur.OneGonAdicFiniteSmoothStage

/-!
# Independent descents of the canonical smooth factor have a common refinement

A second finite-stage descent of the actual canonical map agrees with the
chosen descent after enlarging both stages. The refinement retains the full
whole-cubic embedding, not merely its support or geometric points.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicCharacterTower
open OneGonSmoothing WeierstrassIntegralChart Approximation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]
local notation "B" => algebraicBase I t ht n

/-- Any independent descent of the actual smooth map agrees with the chosen descent. -/
theorem exists_algebraicSmoothFactor_common_refinement
    (i : (CoefficientStage (B))ᵒᵖ)
    (a : (coefficientModelDiagram (B) (algebraicCarrier I t ht n).hom).obj i ⟶
      (integralSmoothOpen (equation (algebraicParameter I t ht n))).toScheme)
    (ha : a ≫ integralSmoothStructure (equation (algebraicParameter I t ht n)) =
      (coefficientModelToInitial (B) (algebraicCarrier I t ht n).hom).app i ≫
      (algebraicCarrier I t ht n).hom)
    (hr : (coefficientModelCone (B) (algebraicCarrier I t ht n).hom).π.app i ≫
      a = recoveredSmoothFactor I t ht n) :
    ∃ (k : (CoefficientStage (B))ᵒᵖ) (α : k ⟶ i)
      (β : k ⟶ algebraicSmoothStage I t ht n),
      (coefficientModelDiagram (B) (algebraicCarrier I t ht n).hom).map α ≫
      a = (coefficientModelDiagram (B) (algebraicCarrier I t ht n).hom).map β ≫
        algebraicSmoothFactor I t ht n ∧
      ((coefficientModelDiagram (B) (algebraicCarrier I t ht n).hom).map α ≫
      a) ≫ (integralSmoothOpen (equation (algebraicParameter I t ht n))).ι =
        (coefficientModelToInitial (B) (algebraicCarrier I t ht n).hom).app k ≫
      algebraicEmbedding I t ht n := by
  let _ := (algebraicCarrier_degree I t ht n).1
  obtain ⟨k, α, β, hk⟩ := exists_coefficient_model_common_hom_eq (B) (algebraicCarrier I t ht n).hom
    (integralSmoothStructure (equation (algebraicParameter I t ht n)))
    a (algebraicSmoothFactor I t ht n) ha (algebraicSmoothFactor_structure I t ht n)
    (hr.trans (algebraicSmoothFactor_recovery I t ht n).symm)
  refine ⟨k, α, β, hk, ?_⟩
  rw [hk, Category.assoc, algebraicSmoothFactor_inclusion, ← Category.assoc]
  simp

end FLT.Mazur.OneGonAdicCharacterTower
