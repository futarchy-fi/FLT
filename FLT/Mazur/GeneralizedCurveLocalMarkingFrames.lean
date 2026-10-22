/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingBaseChange
public import FLT.Mazur.LineBundleAffineFrames
public import FLT.Mazur.SectionRestrictedLineBaseChange

/-!
# Local frames at original smooth markings of singular families

The line restricted to the actual marking is trivial on affine base
neighborhoods. Its frame retains the original group point and section after
base change, without requiring the whole family to be smooth.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory Scheme.Modules
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle
variable {S : Scheme} (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)

/-- A base-open frame induces a frame on the actual base-changed smooth marking. -/
def smoothMarkingOpenFrame (U : S.Opens)
    (e : ((pullback (s ≫ E.inclusion).left).obj
      (divisorLineBundle (s ≫ E.inclusion).left.ker
        (E.smoothMarking_relativeCartier s).1)).restrict U.ι ≅ structureModule U.toScheme) :
    (pullback (pullSection U.ι s ≫ (E.baseChange U.ι).inclusion).left).obj
      (divisorLineBundle (pullSection U.ι s ≫ (E.baseChange U.ι).inclusion).left.ker
        ((E.baseChange U.ι).smoothMarking_relativeCartier (pullSection U.ι s)).1) ≅
          structureModule U.toScheme := by
  let _ : IsProper E.curve.hom := E.family.family.1
  let t := pullSection U.ι s ≫ (E.baseChange U.ι).inclusion
  have ht : t = pullSection U.ι (s ≫ E.inclusion) :=
    (E.pullSection_smoothMarking U.ι s).symm
  exact sectionRestrictedLineOpenFrame (IsPullback.of_hasPullback E.curve.hom U.ι)
    (s ≫ E.inclusion).left t.left (s ≫ E.inclusion).w t.w
    (by rw [ht]; exact section_fst U.ι (s ≫ E.inclusion))
    (E.smoothMarking_relativeCartier s).1
    ((E.baseChange U.ι).smoothMarking_relativeCartier (pullSection U.ι s)).1 e

/-- Every prescribed base neighborhood admits an affine frame of the original marked line. -/
theorem exists_smoothMarking_affineFrame {V : S.Opens} {x : S} (hx : x ∈ V) :
    ∃ U : S.affineOpens, x ∈ U.1 ∧ U.1 ≤ V ∧ Nonempty
      ((pullback (pullSection U.1.ι s ≫ (E.baseChange U.1.ι).inclusion).left).obj
        (divisorLineBundle (pullSection U.1.ι s ≫ (E.baseChange U.1.ι).inclusion).left.ker
          ((E.baseChange U.1.ι).smoothMarking_relativeCartier (pullSection U.1.ι s)).1) ≅
            structureModule U.1.toScheme) := by
  obtain ⟨U, hxU, hUV, ⟨e⟩⟩ :=
    (E.smoothMarking_relativeCartier s).1.divisorLineBundle_locallyFreeRankOne.section_affine_frame
      (s ≫ E.inclusion).left hx
  exact ⟨U, hxU, hUV, ⟨E.smoothMarkingOpenFrame s U.1 e⟩⟩

end FLT.Mazur.GeneralizedEllipticCurve
