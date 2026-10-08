/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOpenImageMap
public import FLT.Mazur.ModuleSheafOpenImageRecovery

/-!
# Naturality of recovery from an image open

A map whose image-open restriction recovers an original chart morphism also
recovers that morphism after restriction or pullback to the original chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.ModuleSheafOpenImageChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]
variable {M N : Y.Modules} {G H : X.Modules}
variable (e : G.restrict i.opensRange.ι ≅ imageModule i M)
variable (e' : H.restrict i.opensRange.ι ≅ imageModule i N)
variable (f : M ⟶ N) (g : G ⟶ H)
variable (h : (restrictFunctor i.opensRange.ι).map g ≫ e'.hom = e.hom ≫ imageMap i f)

include h

/-- Image-open recovery of a morphism implies recovery on the original open chart. -/
@[reassoc]
lemma restrictionRecovery_naturality :
    (restrictFunctor i).map g ≫ (restrictionRecovery i N H e').hom =
      (restrictionRecovery i M G e).hom ≫ f := by
  have hc := ((restrictFunctorCongr (imageIso_hom_ι i)).symm ≪≫
    restrictFunctorComp (imageIso i).hom i.opensRange.ι).hom.naturality g
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.comp_map] at hc
  simp only [restrictionRecovery, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc]
  simp only [← Category.assoc] at hc ⊢
  rw [hc]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, h, Functor.map_comp, Category.assoc,
    imageRestrictionIso_naturality]

/-- Actual pullback recovery also retains the original chart morphism. -/
@[reassoc]
lemma pullbackRecovery_naturality :
    (pullback i).map g ≫ (pullbackRecovery i N H e').hom =
      (pullbackRecovery i M G e).hom ≫ f := by
  simp only [pullbackRecovery, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Category.assoc]
  rw [(restrictFunctorIsoPullback i).inv.naturality_assoc,
    restrictionRecovery_naturality i e e' f g h]

end FLT.Mazur.ModuleSheafOpenImageChart
