/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasGeometricBaseChange
public import FLT.Mazur.DualAtlasBaseChangeReverse

/-!
# The global reverse-section square for geometric base change

The independently descended atlas morphism preserves the reverse section of
the genuinely pulled line inclusion, including nontrivial source line bundles.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasBaseChangeCharts
open SplitLineAffineNeighborhood FCurve AffineFiniteFreeAtlas LocallySplitLineAmbientChart
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {L M : Y.Modules}
variable (s : L ⟶ M) (hL : LocallyFreeRankOne L) (hs : LocallySplit s)
variable (hM : LocallyFiniteFree M)

/-- Genuine pullback of a line inclusion commutes with the global reverse-section map. -/
@[reassoc]
lemma reverse_square :
    LocallySplitLineAtlasSection.morphism ((pullback f).map s)
        (hL.pullback f) (hs.pullback s f) (hM.pullback f) ≫ map f M hM =
      f ≫ LocallySplitLineAtlasSection.morphism s hL hs hM := by
  apply (baseCover f M hM).hom_ext
  intro c
  change c.source.val.ι ≫ _ = c.source.val.ι ≫ _
  rw [LocallySplitLineAtlasSection.ι_morphism_assoc]
  change (point _ _ _ _ _ ≫
    LocallyFreeDualProjectiveAtlas.chartMap _ _ c.source) ≫ _ = _
  rw [Category.assoc, chart_map, point_toAtlas]

end FLT.Mazur.DualAtlasBaseChangeCharts
