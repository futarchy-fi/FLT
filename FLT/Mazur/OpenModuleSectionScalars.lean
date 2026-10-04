/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePullbackSectionCoherence
public import FLT.Mazur.AffineCartesianSectionScalars

/-!
# Base scalars on sections of open subschemes

Ambient sections and global sections of an open restriction agree over the
original base ring. The comparison retains the actual section restriction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
namespace FLT.Mazur.OpenModuleSectionScalars
open ModulePullbackSectionCoherence AffineCartesianSectionScalars
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) (U : X.Opens)

/-- Sections over an open with their actual structural base scalars. -/
abbrev openSections : ModuleCat Γ(S, ⊤) :=
  (ModuleCat.restrictScalars
    ((X.presheaf.map U.leTop.op).hom.comp f.appTop.hom)).obj (M.val.obj (op U))

/-- Chart restriction is bijective on the underlying section groups. -/
lemma chartSection_bijective : Function.Bijective (chartSection M U) := by
  exact ConcreteCategory.bijective_of_isIso (M.presheaf.map (eqToHom U.ι_image_top).op)

/-- The open-to-chart comparison is linear over the original base ring. -/
def chartIso : openSections f M U ≅ baseSections (U.ι ≫ f) (M.restrict U.ι) :=
  (LinearEquiv.ofBijective
    ({ toFun := chartSection M U
       map_add' := map_add (M.presheaf.map (eqToHom U.ι_image_top).op).hom
       map_smul' := fun r m ↦ by
         change M.presheaf.map _ ((X.presheaf.map U.leTop.op (f.appTop r)) • m) =
           (U.ι ≫ f).appTop r • chartSection M U m
         erw [M.map_smul]
         congr 1
         change X.presheaf.map _ (X.presheaf.map _ (f.appTop r)) =
           (U.ι.appIso ⊤).inv ((U.ι ≫ f).appTop r)
         rw [Scheme.Opens.ι_appIso]
         change X.presheaf.map _ (X.presheaf.map _ (f.appTop r)) =
           X.presheaf.map _ (f.appTop r)
         rw [← Functor.map_comp_apply]
         rfl } : openSections f M U →ₗ[Γ(S, ⊤)] baseSections (U.ι ≫ f) (M.restrict U.ι))
    (chartSection_bijective M U)).toModuleIso

/-- The chart isomorphism sends a section to its actual restriction. -/
lemma chartIso_hom (m : Γ(M, U)) : (chartIso f M U).hom m = chartSection M U m := rfl

end FLT.Mazur.OpenModuleSectionScalars
