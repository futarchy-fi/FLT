/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceBaseCompatibility
public import FLT.Mazur.PrincipalOccurrenceGluedTransitions

/-!
# Structure maps from glued finite stages to the original affine base

The chart structure maps agree across the full common unions, hence glue.
Their actual affine formulas prove compatibility with every refinement.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))

variable [Small.{u} ι]

/-- The actual glued finite stage retains its structure map to the original base. -/
def principalOccurrenceGluedStructure (x : PrincipalOccurrenceGluingStage e) :
    (principalOccurrenceStageGlueData e x).glued ⟶ Spec (.of R) :=
  Multicoequalizer.desc (principalOccurrenceStageGlueData e x).toGlueData.diagram (Spec (.of R))
    (fun i ↦ principalOccurrenceChartStructure e x.val ((equivShrink.{u} ι).symm i)) (by
      rintro ⟨i, t⟩
      exact (principalOccurrenceCommonUnionIso_over e x.val
        (principalOccurrenceGluingBijective e x) (principalOccurrenceGluingEquations e x)
        ((equivShrink.{u} ι).symm i) ((equivShrink.{u} ι).symm t)).trans
          (Category.assoc _ _ _).symm)

/-- Every stage chart has its original affine algebra structure map. -/
@[reassoc] theorem principalOccurrenceGluedStructure_chart
    (x : PrincipalOccurrenceGluingStage e) (i : Shrink.{u} ι) :
    (principalOccurrenceStageGlueData e x).ι i ≫ principalOccurrenceGluedStructure e x =
      principalOccurrenceChartStructure e x.val ((equivShrink.{u} ι).symm i) :=
  Multicoequalizer.π_desc (principalOccurrenceStageGlueData e x).toGlueData.diagram (Spec (.of R))
    (fun j ↦ principalOccurrenceChartStructure e x.val ((equivShrink.{u} ι).symm j)) _ i

/-- Chart transitions retain the original affine base. -/
@[reassoc] theorem principalOccurrenceGluingChartMap_over
    (x y : PrincipalOccurrenceGluingStage e) (hxy : x ≤ y) (i : Shrink.{u} ι) :
    principalOccurrenceGluingChartMap e x y hxy i ≫
        principalOccurrenceChartStructure e x.val ((equivShrink.{u} ι).symm i) =
      principalOccurrenceChartStructure e y.val ((equivShrink.{u} ι).symm i) := by
  unfold principalOccurrenceGluingChartMap principalOccurrenceAmbientTransition
  exact FiniteRelationModel.stageStructure_transition _ _ _

/-- Every global refinement is a morphism over the same original affine base. -/
@[reassoc] theorem principalOccurrenceGluedTransition_over
    (x y : PrincipalOccurrenceGluingStage e) (hxy : x ≤ y) :
    principalOccurrenceGluedTransition e x y hxy ≫ principalOccurrenceGluedStructure e x =
      principalOccurrenceGluedStructure e y := by
  apply schemeGlueData_hom_ext (principalOccurrenceStageGlueData e y)
  intro i
  change Shrink.{u} ι at i
  rw [principalOccurrenceGluedTransition_chart_assoc, principalOccurrenceGluedStructure_chart,
    principalOccurrenceGluedStructure_chart, principalOccurrenceGluingChartMap_over]

/-- The inverse diagram carries compatible maps to the original affine base. -/
def principalOccurrenceGluedToBase :
    principalOccurrenceGluedDiagram e ⟶
      (Functor.const (PrincipalOccurrenceGluingStage e)ᵒᵖ).obj (Spec (.of R)) where
  app x := principalOccurrenceGluedStructure e x.unop
  naturality x y g :=
    (principalOccurrenceGluedTransition_over e y.unop x.unop (leOfHom g.unop)).trans
      (Category.comp_id _).symm

end FLT.Mazur.FiniteTypeRelationModel
