/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasSectionForwardLine
public import FLT.Mazur.LocallySplitLineNormalizedChart
public import FLT.Mazur.LocallySplitLineAtlasSection

/-!
# Reverse after forward for actual dual atlas sections

The line constructed from a section recovers its normalized point on every
constructed neighborhood. These neighborhoods cover the original base, so
the actual global reverse morphism is the original section.
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
  FLT.Mazur.LocallySplitLineAmbientChart.point
  FLT.Mazur.LocallySplitLineAtlasSection.morphism
  FLT.Mazur.FiniteFreeChartTransitions.refineChart
namespace FLT.Mazur.DualAtlasSectionForwardLine
open FCurve DualAtlasSectionLineCover
variable {X : Scheme.{u}} (M : X.Modules) (hM : LocallyFiniteFree M)
variable (s : X ⟶ LocallyFreeDualProjectiveAtlas.space M hM)
variable (hs : s ≫ LocallyFreeDualProjectiveAtlas.projection M hM = 𝟙 X)

/-- The actual reverse point in each inherited frame recovers the original normalized line. -/
lemma point_eq (n : Neighborhood M hM s hs) :
    LocallySplitLineAmbientChart.point (inclusion M hM s hs) (rankOne M hM s hs)
        (locallySplit M hM s hs) n.opens (frame n) =
      ProjectiveSpace.affineSectionLinePoint (.id _) n.coordinate n.line :=
  LocallySplitLineAmbientChart.point_sectionLine _ _ _ _ _ _ _
    (chartIso M hM s hs n) (chartIso_inclusion M hM s hs n)

/-- The reverse section agrees with the given section on every constructed base neighborhood. -/
lemma ι_reverse (n : Neighborhood M hM s hs) :
    n.opens.ι ≫ LocallySplitLineAtlasSection.morphism (inclusion M hM s hs)
        (rankOne M hM s hs) (locallySplit M hM s hs) hM = n.opens.ι ≫ s := by
  rw [← X.homOfLE_ι n.le_parent, Category.assoc,
    LocallySplitLineAtlasSection.ι_morphism]
  change X.homOfLE n.le_parent ≫
    (LocallySplitLineAmbientChart.point _ _ _ _ _ ≫ _) = _
  rw [← Category.assoc, LocallySplitLineAmbientChart.point_refinement]
  have hp := point_eq M hM s hs n
  unfold DualAtlasSectionLineCover.frame at hp
  rw [hp, ProjectiveSpace.affineSectionLinePoint_coefficientMap, RingHom.id_comp]
  rw [X.homOfLE_ι]
  exact point_chartMap n

/-- The reverse morphism of the constructed global line is the original atlas section. -/
theorem reverse_forward :
    LocallySplitLineAtlasSection.morphism (inclusion M hM s hs)
      (rankOne M hM s hs) (locallySplit M hM s hs) hM = s := by
  apply (X.openCoverOfIsOpenCover (fun n : Neighborhood M hM s hs ↦ n.opens)
    (iSup_opens M hM s hs)).hom_ext
  intro n
  exact ι_reverse M hM s hs n

end FLT.Mazur.DualAtlasSectionForwardLine
