/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasIteratedCharts
public import FLT.Mazur.FiniteFreeFrameHorizontal

/-!
# Composition of actual geometric chart frames

The coordinate changes for consecutive base changes retain the genuine
ambient pullback-composition comparison and the original chart frames.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] FLT.Mazur.FCurve.modulePullbackRestrictIso
namespace FLT.Mazur.DualAtlasIteratedCharts
open FCurve AffineFiniteFreeAtlas DualAtlasBaseChangeCharts FiniteFreePullbackFrame
open AffineFreeSheafCoordinates
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
variable (c : Chart f g M)

/-- Original pulled chart frames compose through the actual ambient comparison. -/
lemma pulledFrame_comp :
    (restrictFunctor c.source.val.ι).mapIso ((pullbackComp f g).app M) ≪≫
        comparison (f ≫ g) M (c.composite f g M).source c.target
          (c.composite f g M).le_preimage ≪≫
        frame (baseMap (f ≫ g) M (c.composite f g M).source c.target
          (c.composite f g M).le_preimage) (chart M c.target) =
      comparison f ((pullback g).obj M) c.source c.middle c.first_le ≪≫
        frame (baseMap f ((pullback g).obj M) c.source c.middle c.first_le)
          (comparison g M c.middle c.target c.second_le ≪≫
            frame (baseMap g M c.middle c.target c.second_le) (chart M c.target)) := by
  let f' := baseMap f ((pullback g).obj M) c.source c.middle c.first_le
  let g' := baseMap g M c.middle c.target c.second_le
  have hf := (baseMap_ι f ((pullback g).obj M) c.source c.middle c.first_le).symm
  have hg := (baseMap_ι g M c.middle c.target c.second_le).symm
  have normalize (q : c.source.val.toScheme ⟶ c.target.val.toScheme)
      (w : f' ≫ g' = q) (hq : c.source.val.ι ≫ f ≫ g = q ≫ c.target.val.ι) :
      (restrictFunctor c.source.val.ι).mapIso ((pullbackComp f g).app M) ≪≫
          modulePullbackRestrictIso (f ≫ g) q c.source.val.ι c.target.val.ι hq M ≪≫
          frame q (chart M c.target) =
        modulePullbackRestrictIso f f' c.source.val.ι c.middle.val.ι hf
            ((pullback g).obj M) ≪≫
          frame f' (modulePullbackRestrictIso g g' c.middle.val.ι c.target.val.ι hg M ≪≫
            frame g' (chart M c.target)) := by
    subst q
    exact frame_horizontal f g f' g' c.source.val.ι c.middle.val.ι c.target.val.ι
      hf hg M (chart M c.target)
  exact normalize _ (baseMap_comp f g M c)
    (baseMap_ι (f ≫ g) M (c.composite f g M).source c.target
      (c.composite f g M).le_preimage).symm

/-- Actual coordinate changes compose after normalization of the original ambient sheaf. -/
lemma chartChange_comp :
    DualAtlasAmbient.change ((pullbackComp f g).app M) c.source ≪≫
        chartChange (f ≫ g) M (c.composite f g M) =
      chartChange f ((pullback g).obj M) (c.first f g M) ≪≫
        pullbackFreeIso (baseMap f ((pullback g).obj M) c.source c.middle c.first_le)
          (chartChange g M (c.second f g M)) := by
  have hp := congrArg Iso.hom (pulledFrame_comp f g M c)
  have hc := change_frame
    (baseMap f ((pullback g).obj M) c.source c.middle c.first_le)
    (chart ((pullback g).obj M) c.middle)
    (comparison g M c.middle c.target c.second_le ≪≫
      frame (baseMap g M c.middle c.target c.second_le) (chart M c.target))
  dsimp only [chartChange, Chart.second] at hc ⊢
  rw [← hc]
  apply Iso.ext
  dsimp only [DualAtlasAmbient.change, FiniteFreeChartTransitions.ambientChange,
    Chart.first, Chart.composite, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  dsimp only [Iso.trans_hom] at hp
  simpa only [Category.assoc, Chart.composite, Functor.comp_obj] using
    congrArg (fun t ↦ (chart ((pullback f).obj ((pullback g).obj M)) c.source).inv ≫ t) hp

end FLT.Mazur.DualAtlasIteratedCharts
