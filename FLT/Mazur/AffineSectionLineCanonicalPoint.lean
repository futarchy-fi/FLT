/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSectionLineReversePoint
public import FLT.Mazur.LocallySplitLineSourceTransport

/-!
# Canonical reverse points recover normalized affine lines

The canonical construction agrees with the framed construction on an affine
scheme. In particular, it recovers the point of an actual normalized line.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SplitLineAffinePresentation
open FCurve SplitLineAffineNeighborhood AffineSplitLineCoordinates
open AffineFreeSheafCoordinates NormalizedSectionLine
variable {X : Scheme.{u}} [IsAffine X] {ι : Type u} [Finite ι] {L : X.Modules}
variable (s : L ⟶ SheafOfModules.free ι)
variable (hL : LocallyFreeRankOne L) (hs : LocallySplit s)

/-- A global affine frame and splitting recover the canonical reverse construction. -/
lemma morphism_eq_projectivePoint (e : L ≅ structureModule X)
    (r : SheafOfModules.free ι ⟶ L) (hr : s ≫ r = 𝟙 _) :
    morphism s hL hs = projectivePoint e s r hr := by
  have hm := morphism_affine_test s hL hs (𝟙 X)
    (SplitSheafLinePullback.frame (𝟙 X) e)
    (SplitSheafLinePullback.retraction (𝟙 X) r)
    (SplitSheafLinePullback.inclusion_retraction (𝟙 X) s r hr)
  have hp := projectivePoint_pullback (𝟙 X) e s r hr
  exact (Category.id_comp _).symm.trans (hm.trans (hp.symm.trans (Category.id_comp _)))

/-- The canonical reverse map of a normalized section line is its original affine point. -/
lemma morphism_sectionLine (i : ι) (N : Chart Γ(X, ⊤) ι i)
    (hN : LocallyFreeRankOne (sectionLineSheaf X i N))
    (ht : LocallySplit (sectionLineInclusion X i N))
    (r : SheafOfModules.free ι ⟶ sectionLineSheaf X i N)
    (hr : sectionLineInclusion X i N ≫ r = 𝟙 _) :
    morphism (sectionLineInclusion X i N) hN ht =
      ProjectiveSpace.affineSectionLinePoint (.id _) i N := by
  rw [morphism_eq_projectivePoint _ _ _ (sectionLineTrivialization X i N) r hr]
  exact projectivePoint_sectionLineInclusion i N r hr

end FLT.Mazur.SplitLineAffinePresentation
