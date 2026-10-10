/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasSectionLocalSubobjects
public import FLT.Mazur.CoherentSubmoduleLocalEquality
public import FLT.Mazur.AffineSectionLineGluing
public import FLT.Mazur.SplitLineAffineNeighborhood

/-!
# The actual forward line of a global dual atlas section

Normalized local lines of the given section have proved overlap compatibility.
They therefore construct a global rank-one sheaf inside the original ambient
module, with local splittings and monicity after every test-base pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] FLT.Mazur.FiniteFreeChartTransitions.chartSectionLineInclusion
  FLT.Mazur.DualAtlasSectionLineCover.frame
  FLT.Mazur.CoherentSubmoduleGluing.data

namespace FLT.Mazur.DualAtlasSectionForwardLine
open FCurve DualAtlasSectionLineCover SplitLineAffineNeighborhood
variable {X : Scheme.{u}} (M : X.Modules) (hM : LocallyFiniteFree M)
variable (s : X ⟶ LocallyFreeDualProjectiveAtlas.space M hM)
variable (hs : s ≫ LocallyFreeDualProjectiveAtlas.projection M hM = 𝟙 X)

/-- Compatibility of the actual normalized lines is derived from the original global section. -/
lemma compatible : AffineSectionLineGluing.Compatible
    (fun n : Neighborhood M hM s hs ↦ n.opens) M coordinateType frame
    Neighborhood.coordinate Neighborhood.line := by
  intro n m
  apply CoherentSubmoduleGluing.subobject_eq_of_local M _ _ inf_le_left inf_le_right
  intro x hx
  obtain ⟨T, _, hU, hV, hxT, he⟩ := exists_local_subobject_eq n m x hx
  exact ⟨T, hU, hV, hxT, he⟩

/-- The actual global line sheaf recovered from the section. -/
abbrev line : X.Modules := AffineSectionLineGluing.line (compatible M hM s hs)

/-- Its actual inclusion in the original ambient sheaf. -/
abbrev inclusion : line M hM s hs ⟶ M :=
  AffineSectionLineGluing.inclusion (compatible M hM s hs) (iSup_opens M hM s hs)

/-- The constructed forward sheaf is locally free of rank one. -/
lemma rankOne : LocallyFreeRankOne (line M hM s hs) :=
  AffineSectionLineGluing.rankOne (compatible M hM s hs) (iSup_opens M hM s hs)

/-- The original normalized line sheaf is recovered on each constructed affine neighborhood. -/
def chartIso (n : Neighborhood M hM s hs) :
    (line M hM s hs).restrict n.opens.ι ≅
      AffineFreeSheafCoordinates.sectionLineSheaf n.opens.toScheme n.coordinate n.line :=
  AffineSectionLineGluing.chartIso (compatible M hM s hs) n

/-- Recovery preserves the original local ambient inclusion. -/
lemma chartIso_inclusion (n : Neighborhood M hM s hs) :
    (chartIso M hM s hs n).hom ≫
        FiniteFreeChartTransitions.chartSectionLineInclusion M le_rfl (frame n)
          n.coordinate n.line = (restrictFunctor n.opens.ι).map (inclusion M hM s hs) :=
  AffineSectionLineGluing.chartIso_inclusion (compatible M hM s hs) (iSup_opens M hM s hs) n

/-- The original normalized coordinate retractions give local splitting of the global inclusion. -/
lemma locallySplit : LocallySplit (inclusion M hM s hs) := by
  apply locallySplit_of_restrict
  intro x
  obtain ⟨n, hx⟩ := exists_mem M hM s hs x
  exact ⟨n.opens, hx, inferInstance⟩

/-- Every test-base pullback of the forward inclusion remains monic. -/
lemma pullback_mono {T : Scheme.{u}} (f : T ⟶ X) :
    Mono ((pullback f).map (inclusion M hM s hs)) :=
  AffineSectionLineGluing.pullback_mono (compatible M hM s hs) (iSup_opens M hM s hs) f

/-- Every test-base pullback of the forward line retains rank one. -/
lemma pullback_rankOne {T : Scheme.{u}} (f : T ⟶ X) :
    LocallyFreeRankOne ((pullback f).obj (line M hM s hs)) := (rankOne M hM s hs).pullback f

end FLT.Mazur.DualAtlasSectionForwardLine
