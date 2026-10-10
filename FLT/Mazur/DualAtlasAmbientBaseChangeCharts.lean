/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasAmbientCharts
public import FLT.Mazur.DualAtlasBaseChangeOverlapMaps

/-!
# Ambient transport commutes with original geometric base-change charts

Naturality of the actual restriction-pullback comparison gives the coordinate
square, and the dual coordinate functor gives the square of scheme morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] FLT.Mazur.FCurve.modulePullbackRestrictIso
namespace FLT.Mazur.DualAtlasAmbient
open FCurve AffineFiniteFreeAtlas DualFreeSheafCoordinates AffineFreeSheafCoordinates
open DualAtlasBaseChangeCharts FiniteFreePullbackFrame
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : Y.Modules} (a : M ≅ N)

/-- Transport a supported pair of original base-change charts along the ambient isomorphism. -/
def baseChangeChart (c : Chart f M) : Chart f N where
  source := index ((pullback f).mapIso a) c.source
  target := index a c.target
  le_preimage := c.le_preimage

private lemma frame_ambient {U V : Scheme.{u}} (g : U ⟶ V) {A B : V.Modules}
    (b : A ≅ B) {ι κ : Type u} (e : A ≅ SheafOfModules.free ι)
    (d : B ≅ SheafOfModules.free κ) :
    frame g e ≪≫ pullbackFreeIso g (e.symm ≪≫ b ≪≫ d) =
      (pullback g).mapIso b ≪≫ frame g d := by
  rw [← change_frame]
  apply Iso.ext
  simp [frame]

attribute [local irreducible] frame pullbackFreeIso

/-- The original restriction-pullback square is natural in the ambient isomorphism. -/
lemma baseChange_comparison_square (c : Chart f M) :
    (restrictFunctor c.source.val.ι).mapIso ((pullback f).mapIso a) ≪≫
        comparison f N (baseChangeChart f a c).source (baseChangeChart f a c).target
          (baseChangeChart f a c).le_preimage =
      comparison f M c.source c.target c.le_preimage ≪≫
        (pullback (baseMap f M c.source c.target c.le_preimage)).mapIso
          ((restrictFunctor c.target.val.ι).mapIso a) := by
  apply Iso.ext
  dsimp only [comparison, baseChangeChart, baseMap, index, Iso.trans_hom,
    Functor.mapIso_hom]
  exact modulePullbackRestrictIso_naturality f
    (baseMap f M c.source c.target c.le_preimage) c.source.val.ι c.target.val.ι
    (baseMap_ι f M c.source c.target c.le_preimage).symm a.hom

/-- The actual coordinate changes commute with the geometric restriction-pullback square. -/
lemma baseChange_coordinate_square (c : Chart f M) :
    change ((pullback f).mapIso a) c.source ≪≫ chartChange f N (baseChangeChart f a c) =
      chartChange f M c ≪≫
        pullbackFreeIso (baseMap f M c.source c.target c.le_preimage) (change a c.target) := by
  have hn := congrArg Iso.hom (baseChange_comparison_square f a c)
  have hf := congrArg Iso.hom (frame_ambient
    (baseMap f M c.source c.target c.le_preimage)
    ((restrictFunctor c.target.val.ι).mapIso a)
    (chart M c.target) (chart N (index a c.target)))
  dsimp only [Iso.trans_hom, baseChangeChart] at hn hf
  apply Iso.ext
  dsimp only [change, FiniteFreeChartTransitions.ambientChange, chartChange,
    Iso.trans_hom, Iso.symm_hom, baseChangeChart]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hn, hf]
  rfl

/-- Original projective chart morphisms commute with ambient transport and base change. -/
lemma baseChange_chart_square (c : Chart f M) :
    (chartIso ((pullback f).mapIso a) c.source).hom ≫
        DualAtlasBaseChangeCharts.chartMap f N (baseChangeChart f a c).source
          (baseChangeChart f a c).target (baseChangeChart f a c).le_preimage =
      DualAtlasBaseChangeCharts.chartMap f M c.source c.target c.le_preimage ≫
        (chartIso a c.target).hom := by
  rw [chartMap_eq, chartMap_eq]
  change (projectiveIso (change ((pullback f).mapIso a) c.source)).hom ≫ _ =
    _ ≫ (projectiveIso (change a c.target)).hom
  rw [Category.assoc, projectiveIso_pullback, ← Category.assoc,
    ← Iso.trans_hom, ← projectiveIso_trans, ← Category.assoc,
    ← Iso.trans_hom, ← projectiveIso_trans, baseChange_coordinate_square]
  rfl

end FLT.Mazur.DualAtlasAmbient
