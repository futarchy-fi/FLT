/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasPulledFrameRefinement
public import FLT.Mazur.FiniteFreeRefinementPullback

/-!
# Geometric compatibility of original base-change chart maps

The actual scheme morphisms commute with simultaneous source and target
refinement. The proof uses sheaf coordinate changes and coefficient morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasBaseChangeCharts
open FCurve AffineFiniteFreeAtlas FiniteFreePullbackFrame FiniteFreeChartTransitions
open ProjectiveSpace DualFreeSheafCoordinates AffineFreeSheafCoordinates
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)

/-- The free coordinate change defining the original geometric chart map. -/
def chartChange (c : Chart f M) :
    (SheafOfModules.free (AffineFiniteFreeAtlas.coordinates ((pullback f).obj M) c.source) :
      c.source.val.toScheme.Modules) ≅
        SheafOfModules.free (AffineFiniteFreeAtlas.coordinates M c.target) :=
  (chart ((pullback f).obj M) c.source).symm ≪≫
    comparison f M c.source c.target c.le_preimage ≪≫
      frame (baseMap f M c.source c.target c.le_preimage) (chart M c.target)

/-- The original scheme map is its genuine dual coordinate change and coefficient map. -/
lemma chartMap_eq (c : Chart f M) :
    chartMap f M c.source c.target c.le_preimage =
      (projectiveIso (chartChange f M c)).hom ≫
        coefficientMap (baseMap f M c.source c.target c.le_preimage).appTop.hom
          (AffineFiniteFreeAtlas.coordinates M c.target) := rfl

/-- The actual source and target coordinate changes agree under simultaneous refinement. -/
lemma chartChange_refinement (c d : Chart f M)
    (hi : c.source ≤ d.source) (hj : c.target ≤ d.target) :
    transition ((pullback f).obj M) le_rfl hi
        (chart ((pullback f).obj M) c.source) (chart ((pullback f).obj M) d.source) ≪≫
      pullbackFreeIso (X.homOfLE hi) (chartChange f M d) =
    chartChange f M c ≪≫
      pullbackFreeIso (baseMap f M c.source c.target c.le_preimage)
        (transition M le_rfl hj (chart M c.target) (chart M d.target)) := by
  rw [transition, transition, refineChart_self, refineChart_self]
  rw [chartChange, chartChange]
  have hr := pulledFrame_refinement f M c d hi hj (chart M d.target)
  have hs := refineChart_change ((pullback f).obj M) hi
    (chart ((pullback f).obj M) d.source)
    (comparison f M d.source d.target d.le_preimage ≪≫
      frame (baseMap f M d.source d.target d.le_preimage) (chart M d.target))
  rw [← hs, ← hr, ← change_frame]
  apply Iso.ext
  simp

/-- Original geometric chart maps commute as scheme morphisms with refinement. -/
lemma chartMap_refinement (c d : Chart f M)
    (hi : c.source ≤ d.source) (hj : c.target ≤ d.target) :
    dualChartInclusion ((pullback f).obj M) hi
        (chart ((pullback f).obj M) c.source) (chart ((pullback f).obj M) d.source) ≫
      chartMap f M d.source d.target d.le_preimage =
    chartMap f M c.source c.target c.le_preimage ≫
      dualChartInclusion M hj (chart M c.target) (chart M d.target) := by
  rw [chartMap_eq, chartMap_eq]
  change ((projectiveIso (transition _ le_rfl hi _ _)).hom ≫ _) ≫ _ =
    _ ≫ (projectiveIso (transition _ le_rfl hj _ _)).hom ≫ _
  simp only [Category.assoc]
  rw [projectiveIso_pullback_assoc, projectiveIso_pullback_assoc]
  rw [← Category.assoc (projectiveIso (transition _ le_rfl hi _ _)).hom,
    ← Iso.trans_hom, ← projectiveIso_trans, chartChange_refinement f M c d hi hj]
  rw [projectiveIso_trans, Iso.trans_hom]
  simp only [Category.assoc]
  rw [coefficientMap_appTop_comp, coefficientMap_appTop_comp, baseMap_refinement]

end FLT.Mazur.DualAtlasBaseChangeCharts
