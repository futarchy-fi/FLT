/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLinePushforwardTilde
public import FLT.Mazur.CoherentFreeSheaf
public import FLT.Mazur.ModuleGlobalSectionExt
public import FLT.Mazur.ArtinianProperStructureSheaf

/-!
# A proper affinization identifies the actual structure sheaves

On an affine target, quasi-coherent reconstruction promotes bijectivity of
global functions to bijectivity on every open. The map is the original pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
namespace FLT.Mazur.AffineProperFunctionSheaf
open FCurve AffineModuleGlobalSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X S : Scheme.{0}} (f : X ⟶ S)

/-- The module map underlying pullback of regular functions. -/
def structureModuleMap : structureModule S ⟶ (pushforward f).obj (structureModule X) :=
  globalSectionHom _ (1 : Γ(X, ⊤))

/-- The module comparison is exactly the original pullback on every open. -/
theorem structureModuleMap_app (U : S.Opens) (r : Γ(S, U)) :
    (structureModuleMap f).app U r = f.app U r := by
  change f.app U r * X.presheaf.map _ 1 = _
  rw [map_one, mul_one]

variable [IsAffine S] [IsProper f]

/-- Affine reconstruction detects invertibility of the original module map. -/
theorem structureModuleMap_isIso (hf : Function.Bijective f.appTop) :
    IsIso (structureModuleMap f) := by
  let _ := (structureModule_locallyFreeRankOne (X := X)).isFinitePresentation
  let _ := (structureModule_locallyFreeRankOne (X := S)).isFinitePresentation
  let _ := LineSectionBaseChange.properPushforward_isQuasicoherent f (structureModule X)
  let a := structureModuleMap f
  have ha : IsIso ((sections S).map a) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun r : Γ(S, ⊤) ↦ (structureModuleMap f).app ⊤ r)
    simp only [structureModuleMap_app]
    exact hf
  have hn := (affineAdjunction S).counit.naturality a
  have he : a = inv ((affineAdjunction S).counit.app (structureModule S)) ≫
      (affineTilde S).map ((sections S).map a) ≫
        (affineAdjunction S).counit.app ((pushforward f).obj (structureModule X)) := by
    change (affineTilde S).map ((sections S).map a) ≫ _ =
      (affineAdjunction S).counit.app (structureModule S) ≫ a at hn
    rw [hn, IsIso.inv_hom_id_assoc]
  rw [show structureModuleMap f = a from rfl, he]
  infer_instance

/-- Every open has the original ring of inverse-image functions. -/
theorem app_isIso (hf : Function.Bijective f.appTop) (U : S.Opens) :
    IsIso (f.app U) := by
  let _ := structureModuleMap_isIso f hf
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have h := ConcreteCategory.bijective_of_isIso ((structureModuleMap f).app U)
  change Function.Bijective (fun r : Γ(S, U) ↦ (structureModuleMap f).app U r) at h
  simpa only [structureModuleMap_app] using h

/-- The original structure-sheaf map is invertible, including on non-affine opens. -/
theorem structureMap_isIso (hf : Function.Bijective f.appTop) :
    IsIso (ArtinianProperStructureSheaf.structureMap (q := f)) := by
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  intro U
  exact app_isIso f hf U.unop

end FLT.Mazur.AffineProperFunctionSheaf
