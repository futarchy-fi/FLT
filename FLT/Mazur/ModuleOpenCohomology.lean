/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleCohomology
public import FLT.Mazur.OpenSheafCohomology

/-!
# Module cohomology on opens

Forgetting the scalar structure commutes with restriction to an open subscheme.
Consequently ambient cohomology on an open is the actual module cohomology of
the restriction, naturally in the coefficient module.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FLT.Mazur.ModuleOpenCohomology

variable {X : Scheme.{u}} (W : X.Opens)

/-- The identity on sections identifies the two additive sheaves. -/
def restrictionIso (M : X.Modules) :
    (OpenSheafRestriction.restriction W).obj (FCurve.moduleAbelianSheaf M) ≅
      FCurve.moduleAbelianSheaf (M.restrict W.ι) where
  hom.hom :=
    { app := fun _ ↦ AddCommGrpCat.ofHom
        { toFun := fun x ↦ x
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      naturality := by intros; ext x; rfl }
  inv.hom :=
    { app := fun _ ↦ AddCommGrpCat.ofHom
        { toFun := fun x ↦ x
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      naturality := by intros; ext x; rfl }
  hom_inv_id := by
    apply Sheaf.hom_ext
    ext V x
    rfl
  inv_hom_id := by
    apply Sheaf.hom_ext
    ext V x
    rfl

/-- The sectionwise comparison is natural in the coefficient module. -/
lemma restrictionIso_naturality {M N : X.Modules} (g : M ⟶ N) :
    (OpenSheafRestriction.restriction W).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map g) ≫ (restrictionIso W N).hom =
      (restrictionIso W M).hom ≫
        (SheafOfModules.toSheaf W.toScheme.ringCatSheaf).map
          ((Scheme.Modules.restrictFunctor W.ι).map g) := by
  apply Sheaf.hom_ext
  ext V x
  rfl

end FLT.Mazur.ModuleOpenCohomology

namespace FLT.Mazur.FCurve

set_option maxSynthPendingDepth 1

local instance moduleOpenHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

variable {X : Scheme.{u}} (W : X.Opens)

/-- Cohomology on an ambient open equals module cohomology on the open subscheme. -/
def moduleOpenHEquiv (M : X.Modules) (n : ℕ) :
    Sheaf.H'.{u + 1} (moduleAbelianSheaf M) n W ≃+ ModuleH (M.restrict W.ι) n :=
  @OpenSheafCohomology.openHEquiv.{u, u + 1} X.toTopCat W
    (moduleOpenHasExt X) (HasExt.standard _) (moduleAbelianSheaf M) n

end FLT.Mazur.FCurve
