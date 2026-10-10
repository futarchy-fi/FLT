/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineTensorSectionEquiv

/-!
# Tensor-dual sections commute with geometric pullback

The intrinsic evaluation compatibility identifies the pulled dual-line map
with the map of the geometrically pulled tensor section. All comparisons
are the original tensor, structure-module, and dual pullback isomorphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.FCurve
open ModuleSheafTensor
attribute [local irreducible] ModuleSheafTensor.tensor
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {B : Y.Modules}
  (hB : LocallyFreeRankOne B)

/-- Inverse evaluation commutes with the canonical tensor and dual pullback maps. -/
lemma lineDualCoevaluation_pullback :
    (modulePullbackUnitIso f).inv ≫
        (pullback f).map (lineSheafDualEvaluationIso hB).inv ≫
        (ModuleLineBundleTensorPullback.tensorIso f (moduleSheafDual B) B).hom =
      (lineSheafDualEvaluationIso (hB.pullback f)).inv ≫
        map (moduleSheafDualPullbackIso f hB).inv (𝟙 _) := by
  have he := moduleSheafDualPullbackHom_evaluation f B
  change map (moduleSheafDualPullbackIso f hB).hom (𝟙 _) ≫
      (lineSheafDualEvaluationIso (hB.pullback f)).hom =
    (ModuleLineBundleTensorPullback.tensorIso f (moduleSheafDual B) B).inv ≫
      (pullback f).map (lineSheafDualEvaluationIso hB).hom ≫
      (modulePullbackUnitIso f).hom at he
  have hi : congr (moduleSheafDualPullbackIso f hB) (Iso.refl _) ≪≫
      lineSheafDualEvaluationIso (hB.pullback f) =
    (ModuleLineBundleTensorPullback.tensorIso f (moduleSheafDual B) B).symm ≪≫
      (pullback f).mapIso (lineSheafDualEvaluationIso hB) ≪≫ modulePullbackUnitIso f :=
    Iso.ext he
  exact (congrArg Iso.inv hi).symm

/-- Geometrically pulling the tensor section pulls its dual-line morphism. -/
lemma lineHomSectionEquiv_pullback (L : Y.Modules) (a : moduleSheafDual B ⟶ L) :
    lineHomSectionEquiv ((pullback f).obj L) (hB.pullback f)
        ((moduleSheafDualPullbackIso f hB).inv ≫ (pullback f).map a) =
      (ModuleLineBundleTensorPullback.tensorIso f L B).hom.app ⊤
        (pullGlobal f (tensor L B) (lineHomSectionEquiv L hB a)) := by
  apply (globalSectionHomEquiv _).injective
  change globalSectionHom _ _ = globalSectionHom _ _
  rw [lineHomSectionEquiv_hom, ← globalSectionHom_naturality,
    globalSectionHom_pullGlobal, lineHomSectionEquiv_hom, Functor.map_comp]
  rw [Category.assoc, Category.assoc,
    ModuleLineBundleTensorPullback.tensorIso_naturality]
  rw [← Category.assoc, ← Category.assoc]
  rw [Category.assoc (modulePullbackUnitIso f).inv, lineDualCoevaluation_pullback]
  simp only [Category.assoc, ← ModuleSheafTensor.map_comp, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- Recovering a map from the pulled tensor section gives the actual pulled original map. -/
lemma lineHomSectionEquiv_symm_pullback (L : Y.Modules) (s : Γ(tensor L B, ⊤)) :
    (lineHomSectionEquiv ((pullback f).obj L) (hB.pullback f)).symm
        ((ModuleLineBundleTensorPullback.tensorIso f L B).hom.app ⊤
          (pullGlobal f (tensor L B) s)) =
      (moduleSheafDualPullbackIso f hB).inv ≫
        (pullback f).map ((lineHomSectionEquiv L hB).symm s) := by
  apply (lineHomSectionEquiv ((pullback f).obj L) (hB.pullback f)).injective
  rw [Equiv.apply_symm_apply, lineHomSectionEquiv_pullback, Equiv.apply_symm_apply]

end FLT.Mazur.FCurve
