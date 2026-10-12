/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveRelativePointFrames
public import FLT.Mazur.GroupSectionBaseChange
public import FLT.Mazur.LineBundleAffineFrames
public import FLT.Mazur.SectionRestrictedLineBaseChange

/-!
# Frames of the original point line on affine base neighborhoods

Every point of a smooth generalized curve's base has an affine neighborhood
on which the actual pulled-back marking has a framed restricted divisor line.
No frame of that line is assumed, and the original curve and marking are retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle

variable {S T : Scheme} (E : GeneralizedEllipticCurve S)
  [SmoothOfRelativeDimension 1 E.curve.hom] (s : 𝟙_ (Over S) ⟶ E.curve)

/-- The original relative dimension survives on the actual base-changed curve. -/
instance baseChange_smoothPointDimension (g : T ⟶ S) :
    SmoothOfRelativeDimension 1 (E.baseChange g).curve.hom :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- Restriction of the base line gives the required frame on the actual restricted marking. -/
def smoothPointOpenFrame (U : S.Opens)
    (e : ((pullback s.left).obj
      (divisorLineBundle s.left.ker (smoothPoint_cartier E s))).restrict U.ι ≅
        structureModule U.toScheme) :
    (pullback (pullSection U.ι s).left).obj
      (divisorLineBundle (pullSection U.ι s).left.ker
        (smoothPoint_cartier (E.baseChange U.ι) (pullSection U.ι s))) ≅
      structureModule U.toScheme := by
  let _ : IsProper E.curve.hom := E.family.family.1
  exact sectionRestrictedLineOpenFrame (IsPullback.of_hasPullback E.curve.hom U.ι)
    s.left (pullSection U.ι s).left s.w (pullSection U.ι s).w
    (section_fst U.ι s) (smoothPoint_cartier E s)
    (smoothPoint_cartier (E.baseChange U.ι) (pullSection U.ι s)) e

/-- Every prescribed base neighborhood admits an affine frame for the original new marking. -/
theorem exists_smoothPoint_affineFrame {V : S.Opens} {x : S} (hx : x ∈ V) :
    ∃ U : S.affineOpens, x ∈ U.1 ∧ U.1 ≤ V ∧ Nonempty
      ((pullback (pullSection U.1.ι s).left).obj
        (divisorLineBundle (pullSection U.1.ι s).left.ker
          (smoothPoint_cartier (E.baseChange U.1.ι) (pullSection U.1.ι s))) ≅
        structureModule U.1.toScheme) := by
  obtain ⟨U, hxU, hUV, ⟨e⟩⟩ :=
    (smoothPoint_cartier E s).divisorLineBundle_locallyFreeRankOne.section_affine_frame
      s.left hx
  exact ⟨U, hxU, hUV, ⟨smoothPointOpenFrame E s U.1 e⟩⟩

end FLT.Mazur.GeneralizedEllipticCurve
