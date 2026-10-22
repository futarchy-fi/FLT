/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveSmoothMarking
public import FLT.Mazur.GroupSectionBaseChange

/-!
# Base change of the original smooth-marking pole coefficients

The full generalized curve retains its group point and whole-curve section.
The actual section ideal and every pole power commute with arbitrary base
change, including nonflat changes to nilpotent bases.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (E : GeneralizedEllipticCurve S) (g : T ⟶ S)
  (s : 𝟙_ (Over S) ⟶ E.group)

/-- Pulling back the original group point retains its whole-curve marking. -/
theorem pullSection_smoothMarking :
    pullSection g (s ≫ E.inclusion) =
      pullSection g s ≫ (E.baseChange g).inclusion := by
  rw [section_comp, baseChange_inclusion]
  rfl

/-- The whole-curve pole coefficients retain their actual divisor after arbitrary base change. -/
def smoothMarkingPowerBaseChangeIso (m : ℕ) :
    (Scheme.Modules.pullback (pullback.fst E.curve.hom g)).obj (E.smoothMarkingPower s m) ≅
      (E.baseChange g).smoothMarkingPower (pullSection g s) m := by
  let _ : IsProper E.curve.hom := E.family.family.1
  let t := pullSection g s ≫ (E.baseChange g).inclusion
  have ht : t = pullSection g (s ≫ E.inclusion) := (E.pullSection_smoothMarking g s).symm
  exact sectionPointPowerIso (IsPullback.of_hasPullback E.curve.hom g)
    (s ≫ E.inclusion).left t.left (s ≫ E.inclusion).w t.w
    (by rw [ht]; exact section_fst g (s ≫ E.inclusion))
    (E.smoothMarking_relativeCartier s).1
    ((E.baseChange g).smoothMarking_relativeCartier (pullSection g s)).1 m

end FLT.Mazur.GeneralizedEllipticCurve
