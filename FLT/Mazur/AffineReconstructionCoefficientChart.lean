/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePullbackCoefficientRecognition

/-!
# Coefficients of a reconstruction lifted from an affine module

Lifting a coefficient isomorphism through tilde and the affine counit gives
an actual sheaf reconstruction. Its section chart is the original coefficient
map precomposed with the inverse of the tilde unit.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffinePullbackCoefficientRecognition
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable (P : ModuleCat.{u} R) {M : (Spec S).Modules} [M.IsQuasicoherent]
variable (e : (ModuleCat.extendScalars φ.hom).obj P ≅ moduleSpecΓFunctor.obj M)

/-- The lifted reconstruction has the original coefficient map after unit normalization. -/
theorem chart_reconstructed :
    (chart φ (tilde P) (((AffineModulePullbackSections.tildePullbackIso φ).app P).symm ≪≫
      (tilde.functor S).mapIso e ≪≫ asIso M.fromTildeΓ)).hom =
    (ModuleCat.extendScalars φ.hom).map (tilde.toTildeΓNatIso.app P).inv ≫ e.hom := by
  apply (tilde.functor S).map_injective
  apply (cancel_mono M.fromTildeΓ).mp
  rw [chart_counit, Functor.map_comp]
  have hu : (tilde.functor R).map (tilde.toTildeΓNatIso.app P).inv =
      (tilde P).fromTildeΓ := by
    apply (cancel_epi ((tilde.functor R).map (tilde.toTildeΓNatIso.app P).hom)).mp
    rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
    exact (tilde.adjunction.left_triangle_components P).symm
  have hn := (AffineModulePullbackSections.tildePullbackIso φ).hom.naturality
    (tilde.toTildeΓNatIso.app P).inv
  dsimp only [Functor.comp_map] at hn
  rw [hu] at hn
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom, Iso.app_hom, Iso.app_inv]
  erw [← Category.assoc, ← hn]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]
  rfl
end FLT.Mazur.AffinePullbackCoefficientRecognition
