/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceGluingChartMaps
public import FLT.Mazur.SchemeGlueDataMap
/-!
# Compatible global transitions of glued occurrence stages

The constructed ambient transitions and full common-union naturality
glue to global morphisms. Chartwise identity and composition prove the
inverse-system laws without a compatibility assumption on stage choices.
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
  (x y : PrincipalOccurrenceGluingStage e) (hxy : x ≤ y)

/-- The actual chart maps satisfy the gluing relation. -/
theorem principalOccurrenceGluedTransition_compatible (i t : Shrink.{u} ι) :
    (principalOccurrenceStageGlueData e y).f i t ≫
        principalOccurrenceGluingChartMap e x y hxy i ≫
          (principalOccurrenceStageGlueData e x).ι i =
      (principalOccurrenceStageGlueData e y).t i t ≫
        (principalOccurrenceStageGlueData e y).f t i ≫
          principalOccurrenceGluingChartMap e x y hxy t ≫
            (principalOccurrenceStageGlueData e x).ι t :=
  by
  let D := principalOccurrenceStageGlueData e x
  let E := principalOccurrenceStageGlueData e y
  let f := principalOccurrenceGluingChartMap e x y hxy
  let g := principalOccurrenceGluingOverlapMap e x y hxy
  have hf := principalOccurrenceGluingOverlapMap_fac e x y hxy
  have ht := principalOccurrenceGluingOverlapMap_comparison e x y hxy
  change E.f i t ≫ f i ≫ D.ι i = E.t i t ≫ E.f t i ≫ f t ≫ D.ι t
  calc
    _ = g i t ≫ D.f i t ≫ D.ι i := by
      rw [← Category.assoc, ← hf, Category.assoc]
    _ = g i t ≫ D.t i t ≫ D.f t i ≫ D.ι t :=
      congrArg (fun k ↦ g i t ≫ k) (D.glue_condition i t).symm
    _ = E.t i t ≫ g t i ≫ D.f t i ≫ D.ι t := by
      rw [← Category.assoc (g i t), ht, Category.assoc]
    _ = _ := by rw [← Category.assoc (g t i), hf, Category.assoc]

/-- The actual global transition between any two comparable gluable stages. -/
def principalOccurrenceGluedTransition :
    (principalOccurrenceStageGlueData e y).glued ⟶
      (principalOccurrenceStageGlueData e x).glued :=
  Multicoequalizer.desc (principalOccurrenceStageGlueData e y).toGlueData.diagram
    (principalOccurrenceStageGlueData e x).glued
    (fun i ↦ principalOccurrenceGluingChartMap e x y hxy i ≫
      (principalOccurrenceStageGlueData e x).ι i) (by
        rintro ⟨i, t⟩
        change (principalOccurrenceStageGlueData e y).f i t ≫
            principalOccurrenceGluingChartMap e x y hxy i ≫
              (principalOccurrenceStageGlueData e x).ι i =
          ((principalOccurrenceStageGlueData e y).t i t ≫
            (principalOccurrenceStageGlueData e y).f t i) ≫
              principalOccurrenceGluingChartMap e x y hxy t ≫
                (principalOccurrenceStageGlueData e x).ι t
        simpa only [Category.assoc] using
          principalOccurrenceGluedTransition_compatible e x y hxy i t)

/-- Every shrunk chart retains the prescribed affine ambient transition. -/
@[reassoc] theorem principalOccurrenceGluedTransition_chart (i : Shrink.{u} ι) :
    (principalOccurrenceStageGlueData e y).ι i ≫ principalOccurrenceGluedTransition e x y hxy =
      principalOccurrenceGluingChartMap e x y hxy i ≫
        (principalOccurrenceStageGlueData e x).ι i :=
  Multicoequalizer.π_desc (principalOccurrenceStageGlueData e y).toGlueData.diagram
    (principalOccurrenceStageGlueData e x).glued
    (fun j ↦ principalOccurrenceGluingChartMap e x y hxy j ≫
      (principalOccurrenceStageGlueData e x).ι j) _ i

/-- The global transition for a reflexive refinement is the identity. -/
theorem principalOccurrenceGluedTransition_id :
    principalOccurrenceGluedTransition e x x le_rfl = 𝟙 _ := by
  apply schemeGlueData_hom_ext (principalOccurrenceStageGlueData e x)
  intro i
  change Shrink.{u} ι at i
  rw [principalOccurrenceGluedTransition_chart,
    principalOccurrenceGluingChartMap_id, Category.id_comp, Category.comp_id]

/-- Global transitions compose exactly, not merely up to chartwise comparison. -/
@[reassoc] theorem principalOccurrenceGluedTransition_comp
    (z : PrincipalOccurrenceGluingStage e) (hyz : y ≤ z) :
    principalOccurrenceGluedTransition e y z hyz ≫ principalOccurrenceGluedTransition e x y hxy =
      principalOccurrenceGluedTransition e x z (hxy.trans hyz) := by
  apply schemeGlueData_hom_ext (principalOccurrenceStageGlueData e z)
  intro i
  change Shrink.{u} ι at i
  rw [principalOccurrenceGluedTransition_chart_assoc, principalOccurrenceGluedTransition_chart,
    principalOccurrenceGluedTransition_chart, ← Category.assoc,
    principalOccurrenceGluingChartMap_comp]

/-- The nonaffine inverse diagram over all gluable occurrence stages. -/
def principalOccurrenceGluedDiagram : (PrincipalOccurrenceGluingStage e)ᵒᵖ ⥤ Scheme.{u} where
  obj x := (principalOccurrenceStageGlueData e x.unop).glued
  map h := principalOccurrenceGluedTransition e _ _ (leOfHom h.unop)
  map_id x := principalOccurrenceGluedTransition_id e x.unop
  map_comp _f _g := (principalOccurrenceGluedTransition_comp e _ _ _ _ _).symm

end FLT.Mazur.FiniteTypeRelationModel
