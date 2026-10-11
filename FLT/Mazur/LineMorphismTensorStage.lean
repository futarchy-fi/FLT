/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineMorphismTensorSection
public import FLT.Mazur.ModulePullbackStageDual
public import FLT.Mazur.ModulePullbackStageTensor

/-!
# Tensor-dual morphism lines retain original stage coherence

The tensor and dual stage squares combine into the stage square for the
line representing morphisms. All comparisons are the canonical ones.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
universe u
namespace FLT.Mazur.FCurve
open ModuleSheafTensor ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensor tensorIso moduleSheafDualPullbackIso
variable {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (r : X ⟶ Y)
  (h : r ≫ q = p) {L : S.Modules} (hL : LocallyFreeRankOne L) (M : S.Modules)

/-- The canonical tensor-dual comparisons commute with the actual original stage square. -/
theorem lineMorphismTensorPullbackIso_stage :
    (pullback r).map (lineMorphismTensorPullbackIso hL M q).hom ≫
        (lineMorphismTensorPullbackIso (hL.pullback q) ((pullback q).obj M) r).hom ≫
          map (pullbackStageIso p q r h M).hom
            (moduleSheafDualIso _ (pullbackStageIso p q r h L)).inv =
      (pullbackStageIso p q r h (tensor M (moduleSheafDual L))).hom ≫
        (lineMorphismTensorPullbackIso hL M p).hom := by
  simp only [lineMorphismTensorPullbackIso, Iso.trans_hom, ModuleSheafTensor.congr, Iso.refl_hom,
    Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((pullback r).map (map (𝟙 _) _)), tensorIso_naturality]
  simp only [CategoryTheory.Functor.map_id, Category.assoc, ← map_comp, Category.id_comp]
  have hd := pullbackStageIso_dual p q r h hL
  have ht := pullbackStageIso_tensor p q r h M (moduleSheafDual L)
  rw [← reassoc_of% ht]
  simp only [← map_comp, Category.comp_id]
  rw [← hd]

end FLT.Mazur.FCurve
