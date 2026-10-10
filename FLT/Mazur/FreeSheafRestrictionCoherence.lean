/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleGlobalEvaluationPullback
public import FLT.Mazur.ModulePullbackUnitCoherence

/-!
# Coherent free sheaf comparisons

The canonical free sheaf comparison respects composition of pullbacks.
For open immersions it gives the corresponding coherent restriction comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits hiding pullback
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.ModuleGlobalEvaluationPullback
open FCurve
variable {X Y Z : Scheme.{u}}

/-- Free coordinates commute with two successive pullbacks. -/
lemma freeIso_comp (f : X ⟶ Y) (g : Y ⟶ Z) (ι : Type u) :
    (pullbackComp f g).inv.app (SheafOfModules.free ι) ≫
      (pullback f).map (freeIso g ι).hom ≫ (freeIso f ι).hom =
        (freeIso (f ≫ g) ι).hom := by
  apply Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit (pullback (f ≫ g)) _ _
      (SheafOfModules.isColimitFreeCofan ι))
  intro i
  change (pullback (f ≫ g)).map (SheafOfModules.ιFree i) ≫ _ =
    (pullback (f ≫ g)).map (SheafOfModules.ιFree i) ≫ _
  rw [(pullbackComp f g).inv.naturality_assoc]
  change (pullbackComp f g).inv.app _ ≫
    (pullback f).map ((pullback g).map (SheafOfModules.ιFree i)) ≫ _ = _
  rw [← Functor.map_comp_assoc, freeIso_generator, Functor.map_comp]
  simp only [Category.assoc]
  rw [freeIso_generator, freeIso_generator]
  simpa only [structureModule, Category.assoc] using
    congrArg (fun k ↦ k ≫ SheafOfModules.ιFree i) (modulePullbackUnitIso_comp f g)

/-- Canonical free coordinates for ordinary open restriction. -/
def freeRestrictIso (f : X ⟶ Y) [IsOpenImmersion f] (ι : Type u) :
    (restrictFunctor f).obj (SheafOfModules.free ι) ≅ SheafOfModules.free ι :=
  (restrictFunctorIsoPullback f).app _ ≪≫ freeIso f ι

/-- Restriction of each free generator agrees with restriction of the structure module. -/
@[reassoc]
lemma freeRestrictIso_generator (f : X ⟶ Y) [IsOpenImmersion f]
    {ι : Type u} (i : ι) :
    (restrictFunctor f).map (SheafOfModules.ιFree i) ≫ (freeRestrictIso f ι).hom =
      (restrictUnitIso f).hom ≫ SheafOfModules.ιFree i := by
  dsimp only [freeRestrictIso, Iso.trans_hom, Iso.app_hom]
  rw [(restrictFunctorIsoPullback f).hom.naturality_assoc,
    freeIso_generator]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun k ↦ k ≫ SheafOfModules.ιFree i) (restrictPullbackUnitIso f))

/-- Free coordinates commute with two successive open restrictions. -/
lemma freeRestrictIso_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (ι : Type u) :
    (restrictFunctorComp f g).hom.app (SheafOfModules.free ι) ≫
      (restrictFunctor f).map (freeRestrictIso g ι).hom ≫ (freeRestrictIso f ι).hom =
        (freeRestrictIso (f ≫ g) ι).hom := by
  have h := NatTrans.congr_app (restrictFunctorIsoPullback_comp f g)
    (SheafOfModules.free ι)
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  dsimp only [freeRestrictIso, Iso.trans_hom, Iso.app_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [(restrictFunctorIsoPullback f).hom.naturality_assoc]
  change (restrictFunctorComp f g).hom.app _ ≫
    (restrictFunctor f).map ((restrictFunctorIsoPullback g).hom.app _) ≫
    (restrictFunctorIsoPullback f).hom.app _ ≫ _ = _
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [Category.assoc]
  rw [freeIso_comp]

end FLT.Mazur.ModuleGlobalEvaluationPullback
