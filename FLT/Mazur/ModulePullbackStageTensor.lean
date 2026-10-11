/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePullbackStageIso
public import FLT.Mazur.ModuleTensorPullbackRestriction

/-!
# Tensor and unit coherence for the sealed stage comparison

The original stage comparison respects the tensor pullback and structure-module
comparisons, including the given equality of the composite scheme map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.FCurve

open ModuleLineBundleTensorPullback

universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] ModuleSheafTensor.tensor tensorIso

variable {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (r : X ⟶ Y)
  (h : r ≫ q = p)

/-- The sealed stage comparison respects the actual structure-module comparisons. -/
theorem pullbackStageIso_unit :
    (pullback r).map (modulePullbackUnitIso q).hom ≫ (modulePullbackUnitIso r).hom =
      (pullbackStageIso p q r h (structureModule S)).hom ≫
        (modulePullbackUnitIso p).hom := by
  subst p
  rw [pullbackStageIso_hom]
  simpa only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id] using modulePullbackUnitIso_comp_hom r q

/-- The sealed stage comparison respects the actual tensor pullback comparison. -/
theorem pullbackStageIso_tensor (M N : S.Modules) :
    (pullback r).map (tensorIso q M N).hom ≫
        (tensorIso r ((pullback q).obj M) ((pullback q).obj N)).hom ≫
        ModuleSheafTensor.map (pullbackStageIso p q r h M).hom
          (pullbackStageIso p q r h N).hom =
      (pullbackStageIso p q r h (ModuleSheafTensor.tensor M N)).hom ≫
        (tensorIso p M N).hom := by
  subst p
  simp only [pullbackStageIso_hom, pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id]
  exact (tensorIso_comp_hom r q M N).symm

end FLT.Mazur.FCurve
