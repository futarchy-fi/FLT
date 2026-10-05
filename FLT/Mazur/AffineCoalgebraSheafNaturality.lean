/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineLineCoalgebraDescent

/-!
# Naturality of the descended affine sheaf reconstruction

The coefficient reconstruction square lifts to the actual pullback sheaves
using naturality of the scalar-extension/tilde comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineModuleCoalgebraDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.FaithfullyFlat)

/-- The pullback reconstruction intertwines every descended coalgebra morphism. -/
@[reassoc]
theorem pullbackDescentIso_naturality {D E : Data φ} (f : D ⟶ E) :
    (pullback (Spec.map φ)).map (descendedSheafMap φ hφ f) ≫
        (pullbackDescentIso φ hφ E).hom =
      (pullbackDescentIso φ hφ D).hom ≫ (tilde.functor S).map f.f := by
  have hn := (AffineModulePullbackSections.tildePullbackIso φ).inv.naturality
    (descendedModuleMap φ hφ f)
  change (pullback (Spec.map φ)).map ((tilde.functor R).map (descendedModuleMap φ hφ f)) ≫
      (AffineModulePullbackSections.tildePullbackIso φ).inv.app _ =
    (AffineModulePullbackSections.tildePullbackIso φ).inv.app _ ≫
      (tilde.functor S).map ((ModuleCat.extendScalars φ.hom).map
        (descendedModuleMap φ hφ f)) at hn
  dsimp only [pullbackDescentIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    descendedSheafMap, Iso.app_inv]
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
    coefficientIso_naturality, Functor.map_comp, Category.assoc]

end FLT.Mazur.AffineModuleCoalgebraDescent
