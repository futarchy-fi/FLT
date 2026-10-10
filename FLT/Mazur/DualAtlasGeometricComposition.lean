/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasIteratedChartMaps
public import FLT.Mazur.SheafPullbackPathComparison

/-!
# Composition of the actual geometric dual atlas morphisms

The chartwise composition equation descends over the original chart-triple
cover. It retains the genuine ambient pullback comparison as a scheme map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasBaseChangeCharts
open FCurve AffineFiniteFreeAtlas
attribute [local irreducible] map chartMap DualAtlasAmbient.map DualAtlasAmbient.chartIso
attribute [local irreducible] LocallyFreeDualProjectiveAtlas.space
attribute [local irreducible] LocallyFreeDualProjectiveAtlas.chartMap
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable (M : Z.Modules) (hM : LocallyFiniteFree M)

/-- Successive actual atlas maps compose through the genuine ambient comparison. -/
lemma map_comp :
    map f ((pullback g).obj M) (hM.pullback g) ≫ map g M hM =
      DualAtlasAmbient.map ((pullbackComp f g).app M) ((hM.pullback g).pullback f)
        (hM.pullback (f ≫ g)) ≫ map (f ≫ g) M hM := by
  apply (DualAtlasIteratedCharts.projectiveCover f g M hM).hom_ext
  intro c
  change DualAtlasIteratedCharts.Chart f g M at c
  change LocallyFreeDualProjectiveAtlas.chartMap _ _ c.source ≫ _ =
    LocallyFreeDualProjectiveAtlas.chartMap _ _ c.source ≫ _
  have hf := chart_map f ((pullback g).obj M) (hM.pullback g) (c.first f g M)
  have hg := chart_map g M hM (c.second f g M)
  have hk := chart_map (f ≫ g) M hM (c.composite f g M)
  have ha := DualAtlasAmbient.chart_map ((pullbackComp f g).app M)
    ((hM.pullback g).pullback f) (hM.pullback (f ≫ g)) c.source
  dsimp only [DualAtlasIteratedCharts.Chart.first, DualAtlasIteratedCharts.Chart.second,
    DualAtlasIteratedCharts.Chart.composite, toAtlas, DualAtlasAmbient.toAtlas] at hf hg hk ha
  rw [reassoc_of% hf]
  rw [hg, reassoc_of% ha]
  rw [hk]
  simpa only [Category.assoc, DualAtlasIteratedCharts.Chart.composite] using
    congrArg (fun t ↦ t ≫ LocallyFreeDualProjectiveAtlas.chartMap M hM c.target)
      (DualAtlasIteratedCharts.chartMap_comp f g M c)

/-- Normalizing the composite base morphism retains its actual path comparison. -/
lemma map_path (k : X ⟶ Z) (w : f ≫ g = k) :
    map f ((pullback g).obj M) (hM.pullback g) ≫ map g M hM =
      DualAtlasAmbient.map ((SheafPullbackPathComparison.comparison f g k w).app M)
        ((hM.pullback g).pullback f) (hM.pullback k) ≫ map k M hM := by
  subst k
  simpa only [SheafPullbackPathComparison.comparison, pullbackCongr, eqToIso_refl,
    Iso.trans_refl] using map_comp f g M hM

end FLT.Mazur.DualAtlasBaseChangeCharts
