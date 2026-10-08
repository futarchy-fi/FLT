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
ambient projection. The chosen image isomorphism is retained throughout the calculation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.ModuleSheafImageIsoProjectionRecovery
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

variable (U : X.Opens) (eI : Y ≅ U.toScheme) (hI : eI.hom ≫ U.ι = i)
variable (q : G ⟶ (pushforward U.ι).obj ((pushforward eI.hom).obj M))

/-- Recovery through any specified image isomorphism is adjoint to its ambient projection. -/
lemma recovery_projection
    (e : G.restrict U.ι ≅ (pushforward eI.hom).obj M)
    (he : e.hom = (restrictFunctor U.ι).map q ≫
      (restrictFunctorAdjCounitIso U.ι).hom.app ((pushforward eI.hom).obj M)) :
    ((restrictFunctorCongr hI).inv.app G ≫
      (restrictFunctorComp eI.hom U.ι).hom.app G ≫
      (restrictFunctor eI.hom).map e.hom ≫
      (restrictFunctorAdjCounitIso eI.hom).hom.app M) =
        (restrictFunctor i).map (q ≫ (pushforwardComp eI.hom U.ι).hom.app M ≫
          (pushforwardCongr hI).hom.app M) ≫
            (restrictFunctorAdjCounitIso i).hom.app M := by
  simp only [he, Functor.map_comp, Category.assoc]
  apply Scheme.Modules.hom_ext
  intro W
  simp only [Hom.comp_app, restrictFunctorComp_hom_app_app,
    restrictFunctorCongr_inv_app_app, restrict_map_app, counit_app,
    pushforwardComp_hom_app_app, pushforwardCongr_hom_app_app]
  simp only [pushforward_obj_presheaf_map]
  change G.presheaf.map _ ≫ G.presheaf.map _ ≫ q.app _ ≫
    M.presheaf.map _ ≫ M.presheaf.map _ =
    q.app _ ≫ (𝟙 _) ≫ M.presheaf.map _ ≫ M.presheaf.map _
  simp only [← Category.assoc, ← G.presheaf.map_comp]
  have hn {V W : X.Opens} (f : Opposite.op V ⟶ Opposite.op W) :
      G.presheaf.map f ≫ q.app W = q.app V ≫
        ((pushforward U.ι).obj ((pushforward eI.hom).obj M)).presheaf.map f :=
    q.mapPresheaf.naturality f
  rw [hn]
  simp only [Category.assoc, Category.id_comp,
    ← Functor.map_comp]
  congr 2
  rw [Functor.map_comp]
  simp only [pushforward_obj_presheaf_map, Category.assoc,
    ← Functor.map_comp]
  congr 1

end FLT.Mazur.ModuleSheafImageIsoProjectionRecovery
