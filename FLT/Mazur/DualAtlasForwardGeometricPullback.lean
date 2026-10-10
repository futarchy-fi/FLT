/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasGeometricSectionPullback
public import FLT.Mazur.DualAtlasSectionReverseForward
public import FLT.Mazur.LineRecoveryPullback

/-!
# Forward-line naturality for arbitrary geometric atlas sections

The forward line of an arbitrary geometrically pulled section is canonically
isomorphic to the actual pulled original line. The comparison preserves its
inclusion in the pulled ambient sheaf and is uniquely determined by it.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] FLT.Mazur.CoherentSubmoduleGluing.data
  FLT.Mazur.LocallySplitLineAtlasSection.morphism
namespace FLT.Mazur.DualAtlasSectionForwardLine
open FCurve
variable {Y : Scheme.{u}} (M : Y.Modules) (hM : LocallyFiniteFree M)

/-- Equality of original sections induces equality transport of their actual forward lines. -/
def lineCongrIso {s t : Y ⟶ LocallyFreeDualProjectiveAtlas.space M hM}
    (hs : s ≫ LocallyFreeDualProjectiveAtlas.projection M hM = 𝟙 Y)
    (ht : t ≫ LocallyFreeDualProjectiveAtlas.projection M hM = 𝟙 Y) (h : s = t) :
    line M hM s hs ≅ line M hM t ht := by
  subst t
  exact Iso.refl _

/-- Section equality transport retains the original ambient inclusion. -/
lemma lineCongrIso_inclusion {s t : Y ⟶ LocallyFreeDualProjectiveAtlas.space M hM}
    (hs : s ≫ LocallyFreeDualProjectiveAtlas.projection M hM = 𝟙 Y)
    (ht : t ≫ LocallyFreeDualProjectiveAtlas.projection M hM = 𝟙 Y) (h : s = t) :
    (lineCongrIso M hM hs ht h).hom ≫ inclusion M hM t ht = inclusion M hM s hs := by
  subst t
  simp [lineCongrIso]

variable {X : Scheme.{u}} (f : X ⟶ Y)
variable (s : Y ⟶ LocallyFreeDualProjectiveAtlas.space M hM)
variable (hs : s ≫ LocallyFreeDualProjectiveAtlas.projection M hM = 𝟙 Y)
open DualAtlasBaseChangeCharts LocallySplitLineAtlasSection

/-- The actual pulled forward inclusion reverses to the independent geometric section pullback. -/
lemma pullback_reverse_forward :
    morphism ((pullback f).map (inclusion M hM s hs))
        ((rankOne M hM s hs).pullback f)
        ((locallySplit M hM s hs).pullback _ f) (hM.pullback f) =
      sectionPullback f M hM s hs := by
  apply sectionPullback_unique
  · exact morphism_projection _ _ _ _
  · rw [reverse_square f (inclusion M hM s hs) (rankOne M hM s hs)
      (locallySplit M hM s hs) hM, reverse_forward]

/-- Forward recovery of a geometric section pullback is the actual pulled original source line. -/
def geometricPullbackIso :
    line ((pullback f).obj M) (hM.pullback f) (sectionPullback f M hM s hs)
        (sectionPullback_projection f M hM s hs) ≅ (pullback f).obj (line M hM s hs) := by
  let _ := pullback_mono M hM s hs f
  exact lineCongrIso _ _ _ _ (pullback_reverse_forward M hM f s hs).symm ≪≫
    forwardReverseIso ((pullback f).map (inclusion M hM s hs))
      ((rankOne M hM s hs).pullback f)
      ((locallySplit M hM s hs).pullback _ f) (hM.pullback f)

/-- The geometric forward comparison preserves the inclusion into the actual pulled ambient. -/
lemma geometricPullbackIso_inclusion :
    (geometricPullbackIso M hM f s hs).hom ≫ (pullback f).map (inclusion M hM s hs) =
      inclusion ((pullback f).obj M) (hM.pullback f) (sectionPullback f M hM s hs)
        (sectionPullback_projection f M hM s hs) := by
  let _ := pullback_mono M hM s hs f
  dsimp only [geometricPullbackIso, Iso.trans_hom]
  rw [Category.assoc, forwardReverseIso_inclusion]
  exact lineCongrIso_inclusion _ _ _ _ _

/-- The actual ambient inclusion uniquely characterizes the forward pullback comparison. -/
lemma geometricPullbackIso_unique
    (a : line ((pullback f).obj M) (hM.pullback f) (sectionPullback f M hM s hs)
        (sectionPullback_projection f M hM s hs) ⟶ (pullback f).obj (line M hM s hs))
    (ha : a ≫ (pullback f).map (inclusion M hM s hs) =
      inclusion ((pullback f).obj M) (hM.pullback f) (sectionPullback f M hM s hs)
        (sectionPullback_projection f M hM s hs)) :
    a = (geometricPullbackIso M hM f s hs).hom := by
  let _ := pullback_mono M hM s hs f
  apply (cancel_mono ((pullback f).map (inclusion M hM s hs))).mp
  rw [ha, geometricPullbackIso_inclusion]

end FLT.Mazur.DualAtlasSectionForwardLine
