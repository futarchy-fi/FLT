/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveGroupRelativeDimension
public import FLT.Mazur.SmoothOpenSectionCartier
public import FLT.Mazur.SectionPointPowerBaseChange
public import FLT.Mazur.AmpleAffinePullback

/-!
# Actual smooth markings on possibly singular generalized curves

A point of the original smooth group defines a relative Cartier divisor on
its whole curve. Its pole powers retain the actual section under arbitrary
base change; smoothness of the whole curve is not required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme} (E : GeneralizedEllipticCurve S)

/-- An original group section cuts out a relative Cartier divisor on the whole curve. -/
theorem smoothMarking_relativeCartier (s : 𝟙_ (Over S) ⟶ E.group) :
    RelativeEffectiveCartier E.curve.hom (s ≫ E.inclusion).left.ker := by
  let _ : IsProper E.curve.hom := E.family.family.1
  have hd : SmoothOfRelativeDimension 1 (E.inclusion.left ≫ E.curve.hom) := by
    rw [E.inclusion.w]
    infer_instance
  exact smoothOpenSectionCartier E.inclusion.left E.curve.hom s.left
    inferInstance hd inferInstance (by rw [E.inclusion.w]; exact s.w)

/-- The positive pole line of an actual smooth marking, with its original ideal. -/
def smoothMarkingPower (s : 𝟙_ (Over S) ⟶ E.group) (m : ℕ) : E.curve.left.Modules :=
  tensorPower (divisorLineBundle (s ≫ E.inclusion).left.ker
    (E.smoothMarking_relativeCartier s).1) m

/-- Every pole coefficient is an actual line bundle, including on singular families. -/
theorem smoothMarkingPower_rankOne (s : 𝟙_ (Over S) ⟶ E.group) (m : ℕ) :
    LocallyFreeRankOne (E.smoothMarkingPower s m) :=
  (E.smoothMarking_relativeCartier s).1.divisorLineBundle_locallyFreeRankOne.tensorPower m

/-- The original identity is relative Cartier without smoothness of the total curve. -/
theorem identity_relativeCartier :
    RelativeEffectiveCartier E.curve.hom E.identitySection.left.ker :=
  E.smoothMarking_relativeCartier (MonObj.one (X := E.group))

end FLT.Mazur.GeneralizedEllipticCurve
