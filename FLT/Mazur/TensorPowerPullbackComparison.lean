/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePullbackStageTensor
public import FLT.Mazur.RelativeVeryAmpleLineBundle

/-!
# Tensor powers of coherent pullback comparisons

A commuting square of original line comparisons induces commuting squares on
all tensor powers. The proof uses only tensor functoriality and pullback coherence.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.FCurve

open ModuleLineBundleTensorPullback

universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] ModuleSheafTensor.tensor tensorIso

/-- Tensor powers of a specified comparison with an actual pullback. -/
def tensorPowerPullbackComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    {L : Y.Modules} {M : X.Modules} (e : (pullback f).obj L ≅ M) (d : ℕ) :
    (pullback f).obj (tensorPower L d) ≅ tensorPower M d :=
  tensorPowerIso f L d ≪≫ tensorPowerCongr e d

/-- The successor comparison is the tensor of the line and preceding-power comparisons. -/
theorem tensorPowerPullbackComparison_succ {X Y : Scheme.{u}} (f : X ⟶ Y)
    {L : Y.Modules} {M : X.Modules} (e : (pullback f).obj L ≅ M) (d : ℕ) :
    (tensorPowerPullbackComparison f e (d + 1)).hom =
      (tensorIso f L (tensorPower L d)).hom ≫
        ModuleSheafTensor.map e.hom (tensorPowerPullbackComparison f e d).hom := by
  simp only [tensorPowerPullbackComparison, tensorPowerIso_succ, tensorPowerCongr,
    Iso.trans_hom, Iso.refl_hom, ModuleSheafTensor.congr, Category.assoc,
    ← ModuleSheafTensor.map_comp,
    Category.id_comp]

/-- Coherence of the line comparisons induces coherence of every actual tensor power. -/
theorem tensorPowerPullbackComparison_stage
    {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (r : X ⟶ Y) (h : r ≫ q = p)
    {L : S.Modules} {M : Y.Modules} {N : X.Modules}
    (e : (pullback q).obj L ≅ M) (v : (pullback r).obj M ≅ N)
    (w : (pullback p).obj L ≅ N)
    (he : (pullback r).map e.hom ≫ v.hom = (pullbackStageIso p q r h L).hom ≫ w.hom)
    (d : ℕ) :
    (pullback r).map (tensorPowerPullbackComparison q e d).hom ≫
        (tensorPowerPullbackComparison r v d).hom =
      (pullbackStageIso p q r h (tensorPower L d)).hom ≫
        (tensorPowerPullbackComparison p w d).hom := by
  induction d with
  | zero =>
    simpa only [tensorPowerPullbackComparison, tensorPowerIso_zero, tensorPowerCongr,
      Iso.trans_hom, Iso.refl_hom, Category.comp_id, tensorPower] using
      pullbackStageIso_unit p q r h
  | succ d ih =>
    simp only [tensorPowerPullbackComparison_succ, Functor.map_comp, Category.assoc]
    rw [reassoc_of% tensorIso_naturality]
    rw [← ModuleSheafTensor.map_comp, he, ih, ModuleSheafTensor.map_comp]
    simpa only [tensorPower, Category.assoc] using
      congrArg (fun k ↦ k ≫ ModuleSheafTensor.map w.hom
        (tensorPowerPullbackComparison p w d).hom)
        (pullbackStageIso_tensor p q r h L (tensorPower L d))

end FLT.Mazur.FCurve
