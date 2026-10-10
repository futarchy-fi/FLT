/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasSectionLineOverlap
public import FLT.Mazur.FiniteFreeChartUnitRefinement
public import FLT.Mazur.AffineSectionLinePointRestriction

/-!
# Constructed local equality of the actual line-cover subobjects

Every point of a line-cover overlap has an affine neighborhood on which
the original restricted line inclusions define equal subobjects. Both the
point square and the unit coordinate are derived from the original section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasSectionLineCover
open FCurve AffineFiniteFreeAtlas LocallyFreeDualProjectiveAtlas NormalizedSectionLine
open FiniteFreeChartTransitions ModuleSheafMorphismGluing CoherentSubmoduleGluing
variable {X : Scheme.{u}} {M : X.Modules} {hM : LocallyFiniteFree M}
variable {s : X ⟶ LocallyFreeDualProjectiveAtlas.space M hM}
variable {hs : s ≫ projection M hM = 𝟙 X}

/-- Original local line inclusions agree near every point of the actual overlap. -/
lemma exists_local_subobject_eq (n m : Neighborhood M hM s hs) (x : X)
    (hx : x ∈ n.opens ⊓ m.opens) :
    ∃ (T : X.Opens) (_ : IsAffine T.toScheme) (hU : T ≤ n.opens) (hV : T ≤ m.opens),
      x ∈ T ∧
      Subobject.mk (restrictionEquiv T
        (inclusionOn M (chartSectionLineInclusion M le_rfl (frame n) n.coordinate n.line) hU)) =
      Subobject.mk (restrictionEquiv T
        (inclusionOn M (chartSectionLineInclusion M le_rfl (frame m) m.coordinate m.line) hV)) := by
  obtain ⟨W, hW, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset hx
  let _ : IsAffine W.toScheme := hW
  let hU : W ≤ n.opens := hWle.trans inf_le_left
  let hV : W ≤ m.opens := hWle.trans inf_le_right
  obtain ⟨T, hT, h, hxT, j, a, ha⟩ := exists_unit_refinement M hU hV (frame n) (frame m)
    n.coordinate (baseChange (X.homOfLE hU).appTop.hom n.coordinate n.line) ⟨x, hxW⟩
  let _ := hT
  have hL : baseChange (X.homOfLE h).appTop.hom n.coordinate
      (baseChange (X.homOfLE hU).appTop.hom n.coordinate n.line) =
      baseChange (X.homOfLE (h.trans hU)).appTop.hom n.coordinate n.line := by
    rw [baseChange_comp]
    congr 1
    change (X.homOfLE h ≫ X.homOfLE hU).appTop.hom = _
    rw [X.homOfLE_homOfLE]
  rw [hL] at ha
  exact ⟨T, hT, h.trans hU, h.trans hV, hxT,
    sectionLine_pointRestriction_subobject M (h.trans hU) (h.trans hV)
      (frame n) (frame m) n.coordinate j m.coordinate n.line m.line a ha
      (point_overlap n m (h.trans hU) (h.trans hV))⟩

end FLT.Mazur.DualAtlasSectionLineCover
