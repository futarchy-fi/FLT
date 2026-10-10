/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasBaseChangeDirectedCover
public import FLT.Mazur.DualAtlasBaseChangeOverlapMaps

/-!
# Descent of the actual geometric dual atlas base change

Compatible original projective chart morphisms descend to a morphism of the
actual glued atlases. Its original chart laws and projection square are retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasBaseChangeCharts
open FCurve AffineFiniteFreeAtlas FiniteFreeChartTransitions
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (hM : LocallyFiniteFree M)

/-- The original chart morphisms to the target atlas agree on simultaneous refinements. -/
lemma toAtlas_refinement (c d : Chart f M)
    (hi : c.source ≤ d.source) (hj : c.target ≤ d.target) :
    dualChartInclusion ((pullback f).obj M) hi
        (chart ((pullback f).obj M) c.source) (chart ((pullback f).obj M) d.source) ≫
      toAtlas f M d.source d.target d.le_preimage hM =
        toAtlas f M c.source c.target c.le_preimage hM := by
  rw [toAtlas, ← Category.assoc, chartMap_refinement f M c d hi hj,
    Category.assoc, LocallyFreeDualProjectiveAtlas.chart_refinement]
  rfl

/-- The geometric morphism descended from the actual original projective chart maps. -/
def map : LocallyFreeDualProjectiveAtlas.space ((pullback f).obj M) (hM.pullback f) ⟶
    LocallyFreeDualProjectiveAtlas.space M hM :=
  (projectiveCover f M hM).glueMorphismsOfLocallyDirected
    (fun c ↦ toAtlas f M c.source c.target c.le_preimage hM)
    (fun {c d} h ↦ toAtlas_refinement f M hM c d h.le.1 h.le.2)

/-- The descended morphism retains every supported original chart map. -/
@[reassoc]
lemma chart_map (c : Chart f M) :
    LocallyFreeDualProjectiveAtlas.chartMap ((pullback f).obj M) (hM.pullback f) c.source ≫
      map f M hM = toAtlas f M c.source c.target c.le_preimage hM :=
  (projectiveCover f M hM).map_glueMorphismsOfLocallyDirected _
    (fun {c d} h ↦ toAtlas_refinement f M hM c d h.le.1 h.le.2) c

/-- The actual descended atlas morphism lies over the original base morphism. -/
@[reassoc]
lemma map_projection :
    map f M hM ≫ LocallyFreeDualProjectiveAtlas.projection M hM =
      LocallyFreeDualProjectiveAtlas.projection ((pullback f).obj M) (hM.pullback f) ≫ f := by
  apply hom_ext f M hM
  intro c
  rw [chart_map_assoc, toAtlas_projection]

/-- The original chart laws uniquely determine the descended geometric morphism. -/
lemma map_unique
    (g : LocallyFreeDualProjectiveAtlas.space ((pullback f).obj M) (hM.pullback f) ⟶
      LocallyFreeDualProjectiveAtlas.space M hM)
    (hg : ∀ c : Chart f M,
      LocallyFreeDualProjectiveAtlas.chartMap ((pullback f).obj M) (hM.pullback f) c.source ≫ g =
        toAtlas f M c.source c.target c.le_preimage hM) : g = map f M hM := by
  apply hom_ext f M hM
  intro c
  rw [hg, chart_map]

end FLT.Mazur.DualAtlasBaseChangeCharts
