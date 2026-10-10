/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FreeSheafRestrictionCoherence
public import FLT.Mazur.ModulePullbackRestrictionPasting

/-!
# Free coordinates across geometric restriction squares

The canonical free-sheaf coordinates commute with the actual comparison in
an arbitrary commuting restriction-pullback square. This supplies the free
ambient coherence needed when refining geometric projective base-change charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.ModuleGlobalEvaluationPullback
open FCurve
variable {X Y Z W : Scheme.{u}}

/-- Canonical free pullback coordinates respect equality of the geometric morphism. -/
lemma freeIso_congr {f g : X ⟶ Y} (h : f = g) (ι : Type u) :
    (pullbackCongr h).hom.app (SheafOfModules.free ι) ≫ (freeIso g ι).hom =
      (freeIso f ι).hom := by
  subst g
  simp [pullbackCongr]

/-- Free coordinates preserve the actual restriction-pullback square. -/
lemma freeIso_restriction_square (f : X ⟶ Y) (g : Z ⟶ W)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j]
    (h : i ≫ f = g ≫ j) (ι : Type u) :
    (modulePullbackRestrictIso f g i j h (SheafOfModules.free ι)).hom ≫
        (pullback g).map (freeRestrictIso j ι).hom ≫ (freeIso g ι).hom =
      (restrictFunctor i).map (freeIso f ι).hom ≫ (freeRestrictIso i ι).hom := by
  dsimp only [modulePullbackRestrictIso, freeRestrictIso, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [freeIso_comp, freeIso_congr]
  rw [← freeIso_comp i f]
  simp only [Iso.hom_inv_id_app_assoc]
  have hn := (restrictFunctorIsoPullback i).hom.naturality (freeIso f ι).hom
  exact ((reassoc_of% hn) (freeIso i ι).hom).symm

end FLT.Mazur.ModuleGlobalEvaluationPullback
