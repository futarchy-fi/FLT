/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleGlobalGeneration
public import FLT.Mazur.ModuleGlobalUnitGenerator

/-!
# Pullback of global evaluation

Evaluation at a family of global sections commutes with sheaf pullback, under
the canonical comparison between the pullback of a free sheaf and a free sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Limits hiding pullback
open Scheme.Modules
universe u
namespace FLT.Mazur.ModuleGlobalEvaluationPullback
open FCurve ProjectiveSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private instance opensMap_final : (TopologicalSpace.Opens.map f.base).Final := by
  let F := TopologicalSpace.Opens.map f.base
  let : (Functor.fromPUnit.{0} (⊤ : Y.Opens)).Final :=
    Functor.final_fromPUnit_of_isTerminal isTerminalTop
  let : (Functor.fromPUnit.{0} (⊤ : X.Opens)).Final :=
    Functor.final_fromPUnit_of_isTerminal isTerminalTop
  let : (Functor.fromPUnit.{0} (⊤ : Y.Opens) ⋙ F).Final :=
    Functor.final_of_natIso (F := Functor.fromPUnit.{0} (⊤ : X.Opens))
      (Discrete.natIso (fun _ ↦ eqToIso (by ext; simp [F])))
  exact Functor.final_of_final_comp (Functor.fromPUnit.{0} (⊤ : Y.Opens)) F

/-- Canonical preservation of a free module sheaf by scheme pullback. -/
def freeIso (κ : Type u) :
    (pullback f).obj (SheafOfModules.free κ) ≅ SheafOfModules.free κ :=
  SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom κ

/-- The free comparison identifies each structural inclusion. -/
@[reassoc]
lemma freeIso_generator {κ : Type u} (i : κ) :
    (pullback f).map (SheafOfModules.ιFree i) ≫ (freeIso f κ).hom =
      (modulePullbackUnitIso f).hom ≫ SheafOfModules.ιFree i :=
  SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom f.toRingCatSheafHom i

/-- Each generator of global evaluation is the actual section morphism. -/
lemma evaluation_generator (M : Y.Modules) {κ : Type u} (s : κ → Γ(M, ⊤)) (i : κ) :
    SheafOfModules.ιFree i ≫ globalEvaluation M s = globalSectionHom M (s i) := by
  rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply,
    globalEvaluation, Equiv.apply_symm_apply]
  rfl

/-- Pullback commutes with evaluation at any family of global sections. -/
lemma evaluation_pullback (M : Y.Modules) {κ : Type u} (s : κ → Γ(M, ⊤)) :
    (pullback f).map (globalEvaluation M s) =
      (freeIso f κ).hom ≫ globalEvaluation ((pullback f).obj M) (fun i ↦ pullGlobal f M (s i)) := by
  apply Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit (pullback f) _ _
      (SheafOfModules.isColimitFreeCofan κ))
  intro i
  change (pullback f).map (SheafOfModules.ιFree i) ≫ _ =
    (pullback f).map (SheafOfModules.ιFree i) ≫ _
  rw [← Functor.map_comp, evaluation_generator, freeIso_generator_assoc,
    evaluation_generator, globalSectionHom_pullGlobal]
  simp only [Iso.hom_inv_id_assoc]

/-- Epimorphic evaluation is preserved by pullback. -/
lemma evaluation_epi (M : Y.Modules) {κ : Type u} (s : κ → Γ(M, ⊤))
    [Epi (globalEvaluation M s)] :
    Epi (globalEvaluation ((pullback f).obj M) (fun i ↦ pullGlobal f M (s i))) := by
  have he : Epi ((freeIso f κ).hom ≫
      globalEvaluation ((pullback f).obj M) (fun i ↦ pullGlobal f M (s i))) := by
    rw [← evaluation_pullback]
    infer_instance
  exact epi_of_epi (freeIso f κ).hom _

end FLT.Mazur.ModuleGlobalEvaluationPullback
