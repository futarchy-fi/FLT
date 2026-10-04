/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleGlobalUnitGenerator
public import FLT.Mazur.IdealModulePullbackRestrict

/-!
# Transporting generating section morphisms

Composition, sheaf comparisons, and open images preserve the actual section
isomorphism. These identities connect chart calculations to open-cover generation.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y Z : Scheme.{u}}

/-- Successive pullbacks of a generating section give a generator for the composite. -/
lemma globalSectionHom_isIso_comp_pullGlobal (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (s : Γ(M, ⊤))
    [hh : IsIso (globalSectionHom _ (pullGlobal f _ (pullGlobal g M s)))] :
    IsIso (globalSectionHom _ (pullGlobal (f ≫ g) M s)) := by
  rw [← pullGlobal_comp_hom f g M s]
  have ht : IsIso (globalSectionHom ((pullback g ⋙ pullback f).obj M)
    (pullGlobal f _ (pullGlobal g M s))) := hh
  exact globalSectionHom_isIso_transport _ ((pullbackComp f g).app M) _

/-- A comparison of sheaves detects generation after pullback without unfolding it. -/
lemma globalSectionHom_isIso_pullback_transport (f : X ⟶ Y) {M N : Y.Modules}
    (e : M ≅ N) (s : Γ(M, ⊤))
    [IsIso (globalSectionHom _ (pullGlobal f N (e.hom.app ⊤ s)))] :
    IsIso (globalSectionHom _ (pullGlobal f M s)) := by
  have hc : IsIso (globalSectionHom _ (pullGlobal f M s) ≫ (pullback f).map e.hom) := by
    rw [globalSectionHom_naturality, pullGlobal_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((pullback f).map e.hom)

/-- A pulled-back generator is invertible precisely when its pulled-back morphism is. -/
lemma globalSectionHom_pullGlobal_isIso_iff (f : X ⟶ Y) (M : Y.Modules) (s : Γ(M, ⊤)) :
    IsIso (globalSectionHom _ (pullGlobal f M s)) ↔
      IsIso ((pullback f).map (globalSectionHom M s)) := by
  rw [globalSectionHom_pullGlobal]
  constructor
  · intro h
    exact IsIso.of_isIso_comp_left (modulePullbackUnitIso f).inv _
  · intro h
    infer_instance

/-- Open restriction of a global section is its associated local section morphism. -/
lemma sectionHom_restrict_global (M : X.Modules) (U : X.Opens) (s : Γ(M, ⊤)) :
    sectionHom M U (M.presheaf.map (homOfLE le_top).op s) =
      (restrictUnitIso U.ι).inv ≫ (restrictFunctor U.ι).map (globalSectionHom M s) := by
  apply Scheme.Modules.hom_ext
  intro V
  ext r
  simp only [sectionHom_app, Hom.comp_app, AddCommGrpCat.comp_apply]
  erw [M.smul_restrictAppIso_hom_apply U.ι V r]
  change (U.ι.appIso V).inv r •
    M.presheaf.map (homOfLE (U.ι_image_le V)).op
      (M.presheaf.map (homOfLE le_top).op s) =
    (U.ι.appIso V).inv r • M.presheaf.map (homOfLE le_top).op s
  rw [← Functor.map_comp_apply]
  rfl

/-- A generator on an open immersion gives a generator on its actual image open. -/
lemma sectionHom_isIso_on_image (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (s : Γ(M, ⊤))
    [IsIso (globalSectionHom _ (pullGlobal f M s))] :
    IsIso (sectionHom M f.opensRange (M.presheaf.map (homOfLE le_top).op s)) := by
  have := (globalSectionHom_pullGlobal_isIso_iff f M s).mp inferInstance
  have hr : IsIso ((restrictFunctor f).map (globalSectionHom M s)) := by
    have hn := ((restrictFunctorIsoPullback f).hom.naturality (globalSectionHom M s))
    have : IsIso ((restrictFunctor f).map (globalSectionHom M s) ≫
        (restrictFunctorIsoPullback f).hom.app M) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((restrictFunctorIsoPullback f).hom.app M)
  have := moduleHom_isIso_restrict_opensRange (globalSectionHom M s) f
  rw [sectionHom_restrict_global]
  infer_instance

end FLT.Mazur.FCurve
