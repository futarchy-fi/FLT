/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasBaseChangeRefinement
public import FLT.Mazur.FiniteFreeFramePasting
public import FLT.Mazur.ModulePullbackTrivializationCoherence

/-!
# Refining the actual pulled ambient chart frames

The chosen restriction-pullback comparisons preserve refinement of target
frames along simultaneous original source and target chart refinements.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasBaseChangeCharts
open FCurve AffineFiniteFreeAtlas FiniteFreePullbackFrame FiniteFreeChartTransitions
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)

/-- Pulling an original target frame commutes with simultaneous chart refinement. -/
lemma pulledFrame_refinement (c d : Chart f M)
    (hi : c.source ≤ d.source) (hj : c.target ≤ d.target)
    {ι : Type u} (e : M.restrict d.target.val.ι ≅ SheafOfModules.free ι) :
    comparison f M c.source c.target c.le_preimage ≪≫
        frame (baseMap f M c.source c.target c.le_preimage) (refineChart M hj e) =
      refineChart ((pullback f).obj M) hi
        (comparison f M d.source d.target d.le_preimage ≪≫
          frame (baseMap f M d.source d.target d.le_preimage) e) := by
  let fc := baseMap f M c.source c.target c.le_preimage
  let fd := baseMap f M d.source d.target d.le_preimage
  have h₁ := (baseMap_ι f M d.source d.target d.le_preimage).symm
  have h₂ := baseMap_refinement f M c d hi hj
  have ht : (X.homOfLE hi ≫ d.source.val.ι) ≫ f =
      fc ≫ (Y.homOfLE hj ≫ d.target.val.ι) := by
    rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc]
  have hp := congrArg Iso.hom (frame_pasting f fd fc d.source.val.ι (X.homOfLE hi)
    d.target.val.ι (Y.homOfLE hj) h₁ h₂ M e)
  have hc := congrArg Iso.hom (modulePullbackRestrictIso_congr f fc
    c.source.val.ι (X.homOfLE hi ≫ d.source.val.ι)
    c.target.val.ι (Y.homOfLE hj ≫ d.target.val.ι)
    (X.homOfLE_ι hi).symm (Y.homOfLE_ι hj).symm
    (baseMap_ι f M c.source c.target c.le_preimage).symm ht M)
  apply Iso.ext
  dsimp only [refineChart, comparison, frame, restrictFrame, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, ModuleGlobalEvaluationPullback.freeRestrictIso]
    at hp ⊢
  simp only [Functor.map_comp, Category.assoc] at hp ⊢
  rw [← hp]
  dsimp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at hc
  rw [← Category.assoc, ← hc]
  simp only [Category.assoc]
  rfl

end FLT.Mazur.DualAtlasBaseChangeCharts
