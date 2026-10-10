/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallySplitLineAtlasSection
public import FLT.Mazur.DualAtlasSectionLineCover

/-!
# Original chart points of the reverse atlas section

The atlas chart open immersions recover the original reverse point.
Consequently every normalized neighborhood chosen by the forward construction
retains that point in its actual inherited ambient frame.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] FLT.Mazur.LocallySplitLineAmbientChart.point
  FLT.Mazur.LocallySplitLineAtlasSection.morphism
namespace FLT.Mazur.LocallySplitLineAtlasSection
open FCurve SplitLineAffineNeighborhood DualAtlasSectionLineCover
variable {X : Scheme.{u}} {L M : X.Modules} (s : L ⟶ M)
variable (hL : LocallyFreeRankOne L) (hs : LocallySplit s) (hM : LocallyFiniteFree M)

/-- Restricting the actual reverse section recovers its original ambient-chart point. -/
lemma section_chartPoint (i : AffineFiniteFreeAtlas.Index M) :
    DualAtlasSectionChartPoints.point M hM (morphism s hL hs hM)
        (morphism_projection s hL hs hM) i =
      LocallySplitLineAmbientChart.point s hL hs i.val (AffineFiniteFreeAtlas.chart M i) := by
  apply (cancel_mono (LocallyFreeDualProjectiveAtlas.chartMap M hM i)).mp
  rw [DualAtlasSectionChartPoints.point_chartMap, ι_morphism]
  rfl

/-- Each forward neighborhood of the reverse section recovers the original inclusion's point. -/
lemma neighborhood_point (n : Neighborhood M hM (morphism s hL hs hM)
    (morphism_projection s hL hs hM)) :
    LocallySplitLineAmbientChart.point s hL hs n.opens (frame n) =
      ProjectiveSpace.affineSectionLinePoint (.id _) n.coordinate n.line := by
  have hp := n.point_eq
  rw [section_chartPoint, LocallySplitLineAmbientChart.point_refinement] at hp
  apply (cancel_mono (ProjectiveSpace.coefficientMap
    (X.homOfLE n.le_parent).appTop.hom (coordinateType n))).mp
  rw [ProjectiveSpace.affineSectionLinePoint_coefficientMap, RingHom.id_comp]
  exact hp

end FLT.Mazur.LocallySplitLineAtlasSection
