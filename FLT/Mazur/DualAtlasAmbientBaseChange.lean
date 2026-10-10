/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasAmbientIso
public import FLT.Mazur.DualAtlasAmbientBaseChangeCharts

/-!
# Naturality of the actual ambient atlas isomorphism

The chartwise geometric square descends to the original glued atlases. Ambient
transport and geometric base change therefore commute as actual scheme maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasAmbient
open FCurve AffineFiniteFreeAtlas
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : Y.Modules} (a : M ≅ N)
variable (hM : LocallyFiniteFree M) (hN : LocallyFiniteFree N)

/-- The independently defined ambient and base-change maps commute on the actual atlases. -/
@[reassoc]
lemma baseChange_square :
    map ((pullback f).mapIso a) (hM.pullback f) (hN.pullback f) ≫
        DualAtlasBaseChangeCharts.map f N hN =
      DualAtlasBaseChangeCharts.map f M hM ≫ map a hM hN := by
  apply DualAtlasBaseChangeCharts.hom_ext f M hM
  intro c
  have hc := DualAtlasBaseChangeCharts.chart_map f N hN (baseChangeChart f a c)
  have hs := baseChange_chart_square f a c
  dsimp only [baseChangeChart] at hc hs
  rw [chart_map_assoc, toAtlas, Category.assoc, hc]
  rw [DualAtlasBaseChangeCharts.toAtlas, ← Category.assoc, hs,
    Category.assoc]
  rw [DualAtlasBaseChangeCharts.chart_map_assoc f M hM c,
    DualAtlasBaseChangeCharts.toAtlas,
    Category.assoc, chart_map]
  rfl

end FLT.Mazur.DualAtlasAmbient
