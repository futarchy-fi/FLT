/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeFrameRestrictionSquare

/-!
# Pasting actual pulled finite free frames

Two successive restriction squares preserve the pulled frame, including the
comparisons between direct and iterated restrictions on both sides.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FiniteFreePullbackFrame
open FCurve ModuleGlobalEvaluationPullback
variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Scheme.{u}}

/-- Pasting two restriction squares preserves the actual pulled finite free frame. -/
lemma frame_pasting
    (f₀ : X₀ ⟶ Y₀) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (i₁ : X₁ ⟶ X₀) (i₂ : X₂ ⟶ X₁) (j₁ : Y₁ ⟶ Y₀) (j₂ : Y₂ ⟶ Y₁)
    [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h₁ : i₁ ≫ f₀ = f₁ ≫ j₁) (h₂ : i₂ ≫ f₁ = f₂ ≫ j₂)
    (M : Y₀.Modules) {ι : Type u} (e : M.restrict j₁ ≅ SheafOfModules.free ι) :
    modulePullbackRestrictIso f₀ f₂ (i₂ ≫ i₁) (j₂ ≫ j₁)
        (by rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc]) M ≪≫
      frame f₂ ((restrictFunctorComp j₂ j₁).app M ≪≫ restrictFrame j₂ e) =
    (restrictFunctorComp i₂ i₁).app ((pullback f₀).obj M) ≪≫
      restrictFrame i₂ (modulePullbackRestrictIso f₀ f₁ i₁ j₁ h₁ M ≪≫ frame f₁ e) := by
  rw [modulePullbackRestrictIso_pasting f₀ f₁ f₂ i₁ i₂ j₁ j₂ h₁ h₂ M]
  apply Iso.ext
  dsimp only [frame, restrictFrame, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← modulePullbackRestrictIso_naturality_assoc f₁ f₂ i₂ j₂ h₂ e.hom,
    freeIso_restriction_square]

end FLT.Mazur.FiniteFreePullbackFrame
