/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasGeometricCartesian
public import FLT.Mazur.DualAtlasGeometricReverseSquare

/-!
# Geometric pullback of arbitrary dual atlas sections

Sections pull back by the actual cartesian atlas square. This construction
uses the fiber-product universal property, independently of line recovery.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasBaseChangeCharts
open SplitLineAffineNeighborhood FCurve
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (hM : LocallyFiniteFree M)
variable (s : Y ⟶ LocallyFreeDualProjectiveAtlas.space M hM)
variable (hs : s ≫ LocallyFreeDualProjectiveAtlas.projection M hM = 𝟙 Y)

/-- Pull back an arbitrary section by the actual geometric cartesian square. -/
def sectionPullback : X ⟶
    LocallyFreeDualProjectiveAtlas.space ((pullback f).obj M) (hM.pullback f) :=
  (map_isPullback f M hM).lift (f ≫ s) (𝟙 X) (by simp [Category.assoc, hs])

/-- The constructed geometric section lies over the identity of the new base. -/
lemma sectionPullback_projection :
    sectionPullback f M hM s hs ≫
      LocallyFreeDualProjectiveAtlas.projection ((pullback f).obj M) (hM.pullback f) = 𝟙 X :=
  (map_isPullback f M hM).lift_snd _ _ _

/-- The geometric pullback section has its original cartesian compatibility square. -/
@[reassoc]
lemma sectionPullback_map : sectionPullback f M hM s hs ≫ map f M hM = f ≫ s :=
  (map_isPullback f M hM).lift_fst _ _ _

/-- The two cartesian projection laws uniquely characterize the geometric section. -/
lemma sectionPullback_unique
    (t : X ⟶ LocallyFreeDualProjectiveAtlas.space ((pullback f).obj M) (hM.pullback f))
    (ht : t ≫ LocallyFreeDualProjectiveAtlas.projection ((pullback f).obj M)
      (hM.pullback f) = 𝟙 X) (hm : t ≫ map f M hM = f ≫ s) :
    t = sectionPullback f M hM s hs := by
  apply (map_isPullback f M hM).hom_ext
  · rw [hm, sectionPullback_map]
  · rw [ht, sectionPullback_projection]

/-- The reverse section of the actual pulled line is its geometric section pullback. -/
lemma sectionPullback_reverse {L : Y.Modules} (a : L ⟶ M)
    (hL : LocallyFreeRankOne L) (ha : LocallySplit a) :
    LocallySplitLineAtlasSection.morphism ((pullback f).map a)
        (hL.pullback f) (ha.pullback a f) (hM.pullback f) =
      sectionPullback f M hM (LocallySplitLineAtlasSection.morphism a hL ha hM)
        (LocallySplitLineAtlasSection.morphism_projection a hL ha hM) := by
  apply sectionPullback_unique
  · exact LocallySplitLineAtlasSection.morphism_projection _ _ _ _
  · exact reverse_square f a hL ha hM

end FLT.Mazur.DualAtlasBaseChangeCharts
