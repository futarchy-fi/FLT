/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasGeometricBaseChange

/-!
# Cartesian geometric base change of the actual dual atlas

The descended map realizes the fiber product with the original base morphism.
Cartesian squares on the supported original charts descend along the base cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits hiding pullback
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasBaseChangeCharts
open FCurve AffineFiniteFreeAtlas
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (hM : LocallyFiniteFree M)

/-- The descended atlas morphism is the actual cartesian geometric base change. -/
lemma map_isPullback :
    IsPullback (map f M hM)
      (LocallyFreeDualProjectiveAtlas.projection ((pullback f).obj M) (hM.pullback f))
      (LocallyFreeDualProjectiveAtlas.projection M hM) f := by
  apply IsPullback.flip
  apply Scheme.isPullback_of_openCover _ _ _ _ (baseCover f M hM)
  intro c
  have hs := (LocallyFreeDualProjectiveAtlas.chart_isPullback
    ((pullback f).obj M) (hM.pullback f) c.source).flip
  have ht := (chartMap_isPullback f M c.source c.target c.le_preimage).paste_horiz
    (LocallyFreeDualProjectiveAtlas.chart_isPullback M hM c.target).flip
  have ha : IsPullback
      (ProjectiveSpace.affineProjection c.source.val.toScheme
        (coordinates ((pullback f).obj M) c.source))
      (LocallyFreeDualProjectiveAtlas.chartMap ((pullback f).obj M)
        (hM.pullback f) c.source ≫ map f M hM)
      (c.source.val.ι ≫ f) (LocallyFreeDualProjectiveAtlas.projection M hM) := by
    rw [chart_map]
    simpa only [toAtlas, baseMap_ι] using ht.flip
  refine ha.of_iso hs.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl) (by simp)
  · change _ ≫ 𝟙 _ = hs.isoPullback.hom ≫ Limits.pullback.snd _ _
    rw [Category.comp_id, hs.isoPullback_hom_snd]
  · change (_ ≫ map f M hM) ≫ 𝟙 _ =
      hs.isoPullback.hom ≫ Limits.pullback.fst _ _ ≫ map f M hM
    rw [Category.comp_id, ← Category.assoc, hs.isoPullback_hom_fst]

/-- The original pulled atlas is canonically isomorphic to the actual fiber product. -/
def pullbackIso :
    LocallyFreeDualProjectiveAtlas.space ((pullback f).obj M) (hM.pullback f) ≅
      Limits.pullback (LocallyFreeDualProjectiveAtlas.projection M hM) f :=
  (map_isPullback f M hM).isoPullback

/-- The fiber-product comparison retains the independently constructed atlas morphism. -/
@[reassoc]
lemma pullbackIso_fst :
    (pullbackIso f M hM).hom ≫ Limits.pullback.fst _ _ = map f M hM :=
  (map_isPullback f M hM).isoPullback_hom_fst

/-- The fiber-product comparison retains the original pulled atlas projection. -/
@[reassoc]
lemma pullbackIso_snd :
    (pullbackIso f M hM).hom ≫ Limits.pullback.snd _ _ =
      LocallyFreeDualProjectiveAtlas.projection ((pullback f).obj M) (hM.pullback f) :=
  (map_isPullback f M hM).isoPullback_hom_snd

end FLT.Mazur.DualAtlasBaseChangeCharts
