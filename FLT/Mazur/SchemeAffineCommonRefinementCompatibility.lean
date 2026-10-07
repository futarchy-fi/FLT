/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineChartComparisonComposition
public import FLT.Mazur.SchemeAffineCommonRefinement

/-!
# Common transitions are preserved by further geometric refinement

Pulling back a transition on a common chart gives the transition on any further
common refinement, through the actual base pullback composition charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → Chart p) (T T' : Chart p) (ρ : ∀ i, (C i).Refinement T)
variable (σ : T.Refinement T') {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
variable [((pullback T.cover).obj M).IsQuasicoherent]
variable [((pullback T'.cover).obj M).IsQuasicoherent]

/-- Common transitions commute with pullback to a further common affine refinement. -/
theorem commonTransition_refinement (i j : ι) :
    (pullback (Spec.map σ.base)).map (commonTransition C T ρ D i j).hom ≫
        ((C j).compositionPullback T T' D (ρ j) σ).hom =
      ((C i).compositionPullback T T' D (ρ i) σ).hom ≫
        (commonTransition C T' (fun k ↦ (ρ k).comp σ) D i j).hom := by
  apply (cancel_mono ((C j).comparison T' D ((ρ j).comp σ)).hom).mp
  rw [Category.assoc, ← (C j).comparison_composition T T' D (ρ j) σ]
  simp only [commonTransition, Iso.trans_hom, Iso.symm_hom, Functor.map_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Functor.map_comp_assoc (pullback (Spec.map σ.base))
    ((C j).comparison T D (ρ j)).inv ((C j).comparison T D (ρ j)).hom,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  exact (C i).comparison_composition T T' D (ρ i) σ

/-- Transporting the pulled-back transition gives exactly the further common transition. -/
theorem commonTransition_refinement_eq (i j : ι) :
    (commonTransition C T' (fun k ↦ (ρ k).comp σ) D i j).hom =
      ((C i).compositionPullback T T' D (ρ i) σ).inv ≫
        (pullback (Spec.map σ.base)).map (commonTransition C T ρ D i j).hom ≫
          ((C j).compositionPullback T T' D (ρ j) σ).hom := by
  rw [commonTransition_refinement C T T' ρ σ D i j, Iso.inv_hom_id_assoc]

end FLT.Mazur.SchemeAffineDescent
