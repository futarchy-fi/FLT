/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFreeSheafCoordinates
public import FLT.Mazur.FreeSheafSectionCoordinates

/-!
# Affine free coordinates are actual section coordinates

The affine tilde adjunction identifies the recovered module coordinates with
actual free sheaf sections, normalized by the canonical free generators.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineFreeSheafCoordinates
open AffineModuleGlobalSections FreeSheafSectionCoordinates FCurve

/-- The tilde/free comparison preserves the canonical inclusions. -/
lemma tildeFinsupp_generator (R : CommRingCat.{u}) {ι : Type u} (i : ι) :
    tilde.map (ModuleCat.ofHom (Finsupp.lsingle i : R →ₗ[R] (ι →₀ R))) ≫
      (tildeFinsupp ι).hom = SheafOfModules.ιFree i := by
  have h := (IsColimit.comp_coconePointUniqueUpToIso_hom
      ((IsColimit.precomposeHomEquiv
        (Discrete.natIso (fun _ : Discrete ι ↦ (tildeSelf (R := R)))).symm _).symm
          (isColimitOfPreserves (tilde.functor R)
            (ModuleCat.finsuppCoconeIsColimit R R ι)))
      (coproductIsCoproduct (fun _ : ι ↦ SheafOfModules.unit (Spec R).ringCatSheaf))
      (Discrete.mk i))
  simp only [Cocone.precompose_obj_ι, NatTrans.comp_app,
    Functor.mapCocone_ι_app, tildeSelf] at h
  exact h

/-- The tilde unit of the coefficient ring preserves one. -/
lemma tilde_toOpen_one (R : CommRingCat.{u}) :
    tilde.toOpen (ModuleCat.of R R) ⊤ (1 : R) = (1 : Γ(Spec R, ⊤)) := by
  change algebraMap R Γ(Spec R, ⊤) 1 = 1
  exact map_one _

/-- The tilde/free unit sends each basis vector to the actual free generator. -/
lemma tildeFinsupp_single_one (R : CommRingCat.{u}) {ι : Type u} (i : ι) :
    (tildeFinsupp (R := R) ι).hom.app ⊤
      (tilde.toOpen _ ⊤ (Finsupp.single i (1 : R))) =
        (show structureModule (Spec R) ⟶ SheafOfModules.free ι from
          SheafOfModules.ιFree i).app ⊤ (1 : Γ(Spec R, ⊤)) := by
  have hn := ConcreteCategory.congr_hom
    (tilde.toOpen_map_app (ModuleCat.ofHom (Finsupp.lsingle i : R →ₗ[R] (ι →₀ R))) ⊤)
    (1 : R)
  change (tilde.map (ModuleCat.ofHom (Finsupp.lsingle i))).app ⊤
    (tilde.toOpen (ModuleCat.of R R) ⊤ (1 : R)) =
      tilde.toOpen _ ⊤ (Finsupp.single i (1 : R)) at hn
  rw [← hn, tilde_toOpen_one]
  exact congrArg (fun k ↦ k.app ⊤ (1 : Γ(Spec R, ⊤))) (tildeFinsupp_generator R i)

variable (S : Scheme.{u}) [IsAffine S]

/-- The adjunction identifies finite-support vectors with actual global sections. -/
def sectionIso (ι : Type u) :
    ModuleCat.of Γ(S, ⊤) (ι →₀ Γ(S, ⊤)) ≅
      (sections S).obj (SheafOfModules.free ι) :=
  asIso ((affineAdjunction S).unit.app _) ≪≫ (sections S).mapIso (freeIso S ι)

/-- Section coordinates are the pullback of the affine tilde unit. -/
lemma sectionIso_apply {ι : Type u} (v : ι →₀ Γ(S, ⊤)) :
    (sectionIso S ι).hom v = (freeIso S ι).hom.app ⊤
      (pullGlobal S.isoSpec.hom _ (tilde.toOpen _ ⊤ v)) := rfl

/-- Coordinate recovery intertwines the actual map on global sections. -/
lemma sectionIso_coordinates_hom {ι κ : Type u}
    (e : (SheafOfModules.free ι : S.Modules) ≅ SheafOfModules.free κ) :
    (coordinatesIso S e).hom ≫ (sectionIso S κ).hom =
      (sectionIso S ι).hom ≫ (sections S).map e.hom := by
  have hn := (affineAdjunction S).unit.naturality (coordinatesIso S e).hom
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  have hr := congrArg Iso.hom (coordinatesIso_reconstruct S e)
  dsimp only [Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom] at hr
  dsimp only [sectionIso, Iso.trans_hom, asIso_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp, hr]
  simp

end FLT.Mazur.AffineFreeSheafCoordinates
