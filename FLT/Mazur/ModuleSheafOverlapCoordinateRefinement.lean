/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOverlapImageTransition

/-!
# Refinement of coordinates for ambient chart sheaves

The identification of a pulled-back chart pushforward with its chart
coordinate pullback is compatible with further geometric refinement.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.ModuleSheafOverlapImageTransition
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Z W Y X : Scheme.{u}}

/-- The chart-pushforward coordinate identification respects refinement. -/
theorem coordinateIso_refine (t : Z ⟶ W) (p : W ⟶ Y) (i : Y ⟶ X)
    [IsOpenImmersion i] (r : W ⟶ X) (h : p ≫ i = r)
    (p' : Z ⟶ Y) (hp : t ≫ p = p') (r' : Z ⟶ X) (hr : t ≫ r = r')
    (h' : p' ≫ i = r') (M : Y.Modules) :
    (pullback t).map (coordinateIso p i r h M).hom ≫
        (comparison t p p' hp).hom.app M =
      (comparison t r r' hr).hom.app ((pushforward i).obj M) ≫
        (coordinateIso p' i r' h' M).hom := by
  apply (cancel_epi ((pullback t).map
    ((comparison p i r h).hom.app ((pushforward i).obj M)))).mp
  simp only [coordinateIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]
  rw [comparison_assoc_assoc t p i p' r r' hp h hr h']
  simp only [Iso.hom_inv_id_app_assoc]
  exact (comparison t p p' hp).hom.naturality (openCounitIso i M).hom

end FLT.Mazur.ModuleSheafOverlapImageTransition
