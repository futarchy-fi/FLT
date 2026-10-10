/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOpenImageRecovery

/-!
# Chart recovery from ambient projections

Recovery transported from an image open is the restriction adjoint of its
ambient projection. The same formula holds for actual module pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.ModuleSheafOpenImageChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]
variable (M : Y.Modules) (G : X.Modules)
private lemma restrict_map_app {A B : X.Modules} (f : A ⟶ B) (U : Y.Opens) :
    ((restrictFunctor i).map f).app U = f.app (i ''ᵁ U) := rfl

private lemma counit_app (U : Y.Opens) :
    ((restrictFunctorAdjCounitIso i).hom.app M).app U =
      M.presheaf.map (eqToHom (i.preimage_image_eq U).symm).op := rfl

variable (q : G ⟶ (pushforward i.opensRange.ι).obj (imageModule i M))

/-- The image-open recovery composite is the adjoint of the ambient projection. -/
lemma restrictionRecovery_projection
    (e : G.restrict i.opensRange.ι ≅ imageModule i M)
    (he : e.hom = (restrictFunctor i.opensRange.ι).map q ≫
      (restrictFunctorAdjCounitIso i.opensRange.ι).hom.app (imageModule i M)) :
    (restrictionRecovery i M G e).hom =
      (restrictFunctor i).map (q ≫ (imagePushforwardIso i M).hom) ≫
        (restrictFunctorAdjCounitIso i).hom.app M := by
  simp only [restrictionRecovery, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, he, Functor.map_comp, Category.assoc]
  apply Scheme.Modules.hom_ext
  intro U
  simp only [Hom.comp_app, restrictFunctorComp_hom_app_app,
    restrictFunctorCongr_inv_app_app, imageRestrictionIso, imagePushforwardIso,
    Iso.trans_hom, Iso.app_hom, restrict_map_app, counit_app,
    pushforwardComp_hom_app_app, pushforwardCongr_hom_app_app,
    Category.assoc]
  simp only [imageModule, pushforward_obj_presheaf_map]
  change G.presheaf.map _ ≫ G.presheaf.map _ ≫ q.app _ ≫
    M.presheaf.map _ ≫ M.presheaf.map _ =
    q.app _ ≫ (𝟙 _) ≫ M.presheaf.map _ ≫ M.presheaf.map _
  simp only [← Category.assoc, ← G.presheaf.map_comp]
  have hn {V W : X.Opens} (f : Opposite.op V ⟶ Opposite.op W) :
      G.presheaf.map f ≫ q.app W = q.app V ≫
        ((pushforward i.opensRange.ι).obj (imageModule i M)).presheaf.map f :=
    q.mapPresheaf.naturality f
  rw [hn]
  simp only [Category.assoc, Category.id_comp,
    ← Functor.map_comp]
  congr 2
  rw [Functor.map_comp]
  simp only [pushforward_obj_presheaf_map, imageModule, Category.assoc,
    ← Functor.map_comp]
  congr 1

/-- Pullback recovery is the pulled ambient projection followed by the open counit. -/
lemma pullbackRecovery_projection
    (e : G.restrict i.opensRange.ι ≅ imageModule i M)
    (he : e.hom = (restrictFunctor i.opensRange.ι).map q ≫
      (restrictFunctorAdjCounitIso i.opensRange.ι).hom.app (imageModule i M)) :
    (pullbackRecovery i M G e).hom =
      (pullback i).map (q ≫ (imagePushforwardIso i M).hom) ≫
        (ModuleSheafOverlapImageTransition.openCounitIso i M).hom := by
  simp only [pullbackRecovery, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    restrictionRecovery_projection i M G q e he]
  rw [← (restrictFunctorIsoPullback i).inv.naturality_assoc]
  rfl

end FLT.Mazur.ModuleSheafOpenImageChart
