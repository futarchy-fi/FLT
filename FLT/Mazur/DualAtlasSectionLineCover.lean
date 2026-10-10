/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasSectionBaseNeighborhood

/-!
# The actual normalized affine cover of an atlas section

The cover retains each parent atlas chart, its inherited ambient frame,
and the normalized line whose projective point is the original section.
Covering is proved from local recovery, without an overlap compatibility input.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasSectionLineCover
open FCurve AffineFiniteFreeAtlas LocallyFreeDualProjectiveAtlas NormalizedSectionLine
open DualAtlasSectionChartPoints
variable {X : Scheme.{u}} (M : X.Modules) (hM : LocallyFiniteFree M)
variable (s : X ⟶ space M hM) (hs : s ≫ projection M hM = 𝟙 X)

/-- A recovered normalized line chart of the original atlas section. -/
structure Neighborhood where
  /-- The original affine free atlas chart. -/
  parent : Index M
  /-- The actual affine neighborhood in the base. -/
  opens : X.Opens
  affine : IsAffine opens.toScheme
  le_parent : opens ≤ parent.val
  /-- The selected normalized coordinate in the parent frame. -/
  coordinate : coordinates M parent
  /-- The recovered normalized section submodule. -/
  line : Chart Γ(opens.toScheme, ⊤) (coordinates M parent) coordinate
  point_eq : let _ := affine
    X.homOfLE le_parent ≫ point M hM s hs parent =
      ProjectiveSpace.affineSectionLinePoint (X.homOfLE le_parent).appTop.hom coordinate line

attribute [instance] Neighborhood.affine

/-- Every point of the original base belongs to a recovered normalized line neighborhood. -/
lemma exists_mem (x : X) : ∃ n : Neighborhood M hM s hs, x ∈ n.opens := by
  obtain ⟨i, U, hU, h, hx, k, L, hp⟩ := exists_base_local_line M hM s hs x
  exact ⟨⟨i, U, hU, h, k, L, hp⟩, hx⟩

/-- The actual normalized line neighborhoods cover the original base. -/
lemma iSup_opens : ⨆ n : Neighborhood M hM s hs, n.opens = ⊤ := by
  apply top_le_iff.mp
  intro x _
  exact Opens.mem_iSup.mpr (exists_mem M hM s hs x)

variable {M hM s hs}

/-- The finite coordinate type is inherited from the original ambient atlas frame. -/
abbrev coordinateType (n : Neighborhood M hM s hs) := coordinates M n.parent

/-- The inherited frame is an actual restriction of the original ambient sheaf chart. -/
def frame (n : Neighborhood M hM s hs) :
    M.restrict n.opens.ι ≅ SheafOfModules.free (coordinateType n) :=
  FiniteFreeChartTransitions.refineChart M n.le_parent (chart M n.parent)

/-- The recovered local point still maps to the original global atlas section. -/
lemma point_chartMap (n : Neighborhood M hM s hs) :
    ProjectiveSpace.affineSectionLinePoint (X.homOfLE n.le_parent).appTop.hom
        n.coordinate n.line ≫ chartMap M hM n.parent = n.opens.ι ≫ s := by
  rw [← n.point_eq, Category.assoc, DualAtlasSectionChartPoints.point_chartMap,
    ← Category.assoc, X.homOfLE_ι]

end FLT.Mazur.DualAtlasSectionLineCover
