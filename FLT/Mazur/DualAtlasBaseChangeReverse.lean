/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasBaseChangeCharts
public import FLT.Mazur.FramedDualProjectiveReverse
public import FLT.Mazur.ModulePullbackRestrictionPasting
public import FLT.Mazur.LocallySplitLineAtlasSection

/-!
# Reverse-section square on original dual atlas charts

The constructed chartwise geometric base-change map transports the reverse
point of the genuinely pulled line to the original line's reverse point.
Both ambient and source comparisons come from the same geometric square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasBaseChangeCharts
open FCurve AffineFiniteFreeAtlas LocallySplitLineAmbientChart
open SplitLineAffineNeighborhood SplitLineAffinePresentation
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {L M : Y.Modules}
variable (s : L ⟶ M) (hL : LocallyFreeRankOne L) (hs : LocallySplit s)
variable (i : Index ((pullback f).obj M)) (j : Index M) (h : i.val ≤ f ⁻¹ᵁ j.val)

/-- The original chart reverse points commute with the genuine geometric chart map. -/
lemma point_square :
    baseMap f M i j h ≫ point s hL hs j.val (chart M j) =
      point ((pullback f).map s) (hL.pullback f) (hs.pullback s f)
        i.val (chart ((pullback f).obj M) i) ≫ chartMap f M i j h := by
  let g := baseMap f M i j h
  let a := modulePullbackRestrictIso f g i.val.ι j.val.ι (baseMap_ι f M i j h).symm L
  let t := (pullback g).map ((restrictFunctor j.val.ι).map s) ≫
    (sourceFrame f M i j h).hom
  have ht : LocallySplit t :=
    ((hs.restriction s j.val.ι).pullback _ g).postcompose _ (sourceFrame f M i j h)
  have ha : a.hom ≫ t =
      inclusion ((pullback f).map s) i.val (chart ((pullback f).obj M) i) := by
    dsimp only [a, t, sourceFrame, Iso.trans_hom, Iso.symm_hom, inclusion]
    rw [← Category.assoc, ← modulePullbackRestrictIso_naturality]
    change (_ ≫ (comparison f M i j h).hom) ≫
      (comparison f M i j h).inv ≫ _ = _
    rw [Category.assoc, Iso.hom_inv_id_assoc]
  have hp := FramedDualProjectivePullback.reverse_square g
    ((restrictFunctor j.val.ι).map s) (hL.restrict j.val.ι)
    (hs.restriction s j.val.ι) (chart M j) (sourceFrame f M i j h)
  change g ≫ point s hL hs j.val (chart M j) = morphism t _ ht ≫ _ at hp
  rw [hp]
  apply congrArg (· ≫ chartMap f M i j h)
  exact (morphism_sourceIso a _ t ha ((hL.pullback f).restrict i.val.ι)
    ((hL.restrict j.val.ι).pullback g)
    (inclusion_locallySplit _ (hs.pullback s f) i.val (chart ((pullback f).obj M) i)) ht).symm

variable (hM : LocallyFiniteFree M)

/-- The local maps into the genuine target atlas preserve the original reverse section. -/
lemma point_toAtlas :
    point ((pullback f).map s) (hL.pullback f) (hs.pullback s f)
        i.val (chart ((pullback f).obj M) i) ≫ toAtlas f M i j h hM =
      i.val.ι ≫ f ≫ LocallySplitLineAtlasSection.morphism s hL hs hM := by
  rw [toAtlas, ← Category.assoc, ← point_square,
    Category.assoc, ← atlasPoint, ← LocallySplitLineAtlasSection.ι_morphism,
    ← Category.assoc, baseMap_ι, Category.assoc]

end FLT.Mazur.DualAtlasBaseChangeCharts
