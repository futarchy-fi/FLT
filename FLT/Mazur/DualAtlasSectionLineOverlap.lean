/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasSectionLineCover
public import FLT.Mazur.DualAtlasSectionCommonPoint
public import FLT.Mazur.FiniteFreeInheritedChartTransitions

/-!
# Actual dual point compatibility on the constructed line cover

The normalized line cover inherits genuine point squares on every common
affine refinement. These squares use precisely the ambient frames needed
by affine section-line gluing.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasSectionLineCover
open FCurve AffineFiniteFreeAtlas LocallyFreeDualProjectiveAtlas NormalizedSectionLine
open FiniteFreeChartTransitions ProjectiveSpace
variable {X : Scheme.{u}} {M : X.Modules} {hM : LocallyFiniteFree M}
variable {s : X ⟶ LocallyFreeDualProjectiveAtlas.space M hM}
variable {hs : s ≫ projection M hM = 𝟙 X}

/-- The recovered normalized line retains its original parent point on every affine refinement. -/
lemma point_restrict (n : Neighborhood M hM s hs) {W : X.Opens} [IsAffine W.toScheme]
    (h : W ≤ n.opens) :
    X.homOfLE (h.trans n.le_parent) ≫ DualAtlasSectionChartPoints.point M hM s hs n.parent =
      affineSectionLinePoint (X.homOfLE (h.trans n.le_parent)).appTop.hom n.coordinate
        (baseChange (X.homOfLE h).appTop.hom n.coordinate n.line) := by
  rw [← X.homOfLE_homOfLE h n.le_parent, Category.assoc, n.point_eq,
    affineSectionLinePoint_pullback]
  rfl

/-- Actual line-cover points satisfy the dual square for their inherited ambient frames. -/
lemma point_overlap (n m : Neighborhood M hM s hs) {W : X.Opens} [IsAffine W.toScheme]
    (hU : W ≤ n.opens) (hV : W ≤ m.opens) :
    sectionLinePoint Γ(W.toScheme, ⊤) (coordinateType n) (.id _) n.coordinate
        (baseChange (X.homOfLE hU).appTop.hom n.coordinate n.line) ≫
          (dualProjectiveTransition M hU hV (frame n) (frame m)).hom =
      sectionLinePoint Γ(W.toScheme, ⊤) (coordinateType m) (.id _) m.coordinate
        (baseChange (X.homOfLE hV).appTop.hom m.coordinate m.line) := by
  rw [frame, frame, dualProjectiveTransition_inherited]
  exact DualAtlasSectionChartPoints.normalized_common_point M hM s hs n.parent m.parent
    (hU.trans n.le_parent) (hV.trans m.le_parent) n.coordinate m.coordinate _ _
    (point_restrict n hU) (point_restrict m hV)

end FLT.Mazur.DualAtlasSectionLineCover
