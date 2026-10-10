/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FramedDualProjectivePullback
public import FLT.Mazur.LocallyFreeDualProjectiveAtlas

/-!
# Base-change maps on original dual atlas charts

For an original pulled ambient chart contained in the inverse image of an
original target chart, construct the actual projective morphism between them.
Its frame comparison is the geometric restriction-pullback comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasBaseChangeCharts
open FCurve AffineFiniteFreeAtlas ProjectiveSpace
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
variable (i : Index ((pullback f).obj M)) (j : Index M) (h : i.val ≤ f ⁻¹ᵁ j.val)

/-- The actual morphism from a source affine chart into the original target chart. -/
def baseMap : i.val.toScheme ⟶ j.val.toScheme := X.homOfLE h ≫ f ∣_ j.val

/-- The chart map recovers the original base morphism on its source open. -/
@[reassoc]
lemma baseMap_ι : baseMap f M i j h ≫ j.val.ι = i.val.ι ≫ f := by
  simp only [baseMap, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]

/-- The genuine comparison between restricted pullback and pullback of restriction. -/
def comparison : ((pullback f).obj M).restrict i.val.ι ≅
    (pullback (baseMap f M i j h)).obj (M.restrict j.val.ι) :=
  modulePullbackRestrictIso f (baseMap f M i j h) i.val.ι j.val.ι
    (baseMap_ι f M i j h).symm M

/-- Express the original source chart as a frame of the genuinely pulled target sheaf. -/
def sourceFrame : (pullback (baseMap f M i j h)).obj (M.restrict j.val.ι) ≅
    SheafOfModules.free (coordinates ((pullback f).obj M) i) :=
  (comparison f M i j h).symm ≪≫ chart ((pullback f).obj M) i

/-- The actual geometric map between the original finite projective atlas charts. -/
def chartMap : space Γ(i.val.toScheme, ⊤) (coordinates ((pullback f).obj M) i) ⟶
    space Γ(j.val.toScheme, ⊤) (coordinates M j) :=
  FramedDualProjectivePullback.map (baseMap f M i j h) (chart M j) (sourceFrame f M i j h)

/-- The original chart projections commute with the constructed morphism. -/
@[reassoc]
lemma chartMap_projection :
    chartMap f M i j h ≫ affineProjection j.val.toScheme (coordinates M j) =
      affineProjection i.val.toScheme (coordinates ((pullback f).obj M) i) ≫
        baseMap f M i j h :=
  FramedDualProjectivePullback.map_projection _ _ _

/-- This is a cartesian square of original projective charts. -/
lemma chartMap_isPullback :
    IsPullback (chartMap f M i j h)
      (affineProjection i.val.toScheme (coordinates ((pullback f).obj M) i))
      (affineProjection j.val.toScheme (coordinates M j)) (baseMap f M i j h) :=
  FramedDualProjectivePullback.map_isPullback _ _ _

variable (hM : LocallyFiniteFree M)

/-- The constructed original chart morphism takes values in the genuine glued target atlas. -/
def toAtlas : space Γ(i.val.toScheme, ⊤) (coordinates ((pullback f).obj M) i) ⟶
    LocallyFreeDualProjectiveAtlas.space M hM :=
  chartMap f M i j h ≫ LocallyFreeDualProjectiveAtlas.chartMap M hM j

/-- The chartwise base-change morphism has the original global projection square. -/
lemma toAtlas_projection :
    toAtlas f M i j h hM ≫ LocallyFreeDualProjectiveAtlas.projection M hM =
      LocallyFreeDualProjectiveAtlas.chartMap ((pullback f).obj M) (hM.pullback f) i ≫
        LocallyFreeDualProjectiveAtlas.projection ((pullback f).obj M) (hM.pullback f) ≫ f := by
  rw [toAtlas, Category.assoc, LocallyFreeDualProjectiveAtlas.chart_projection,
    chartMap_projection_assoc, baseMap_ι,
    LocallyFreeDualProjectiveAtlas.chart_projection_assoc]

end FLT.Mazur.DualAtlasBaseChangeCharts
