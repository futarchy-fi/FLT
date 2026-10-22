/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPoleComplementBaseChange
public import FLT.Mazur.GeneralizedCurveMarkingTransportedFrame
public import FLT.Mazur.GeneralizedCurveMarkingComplementCoordinates

/-!
# The original curve's complement functions under actual base change

The map is the restriction of the original total-space projection to the
retained marking complements. Its scalar map and both transported pole
coordinates are identified with their original structure-sheaf pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback relativePoleFunction smoothMarkingTransportedLift
variable {S T : Scheme} (E : GeneralizedEllipticCurve S) (g : T ⟶ S)
  (s : 𝟙_ (Over S) ⟶ E.group)

local instance generalizedCurveMarkingComplementPullbackProper :
    IsProper E.curve.hom := E.family.family.1

local notation "t" => s ≫ E.inclusion
local notation "v" => pullSection g s ≫ GeneralizedEllipticCurve.inclusion (E.baseChange g)
local notation "hI" => And.left (smoothMarking_relativeCartier E s)
local notation "hJ" => And.left (smoothMarking_relativeCartier (E.baseChange g) (pullSection g s))
local notation "H" => smoothMarkingBaseChange_cartesian E g
local notation "w" => smoothMarkingBaseChange_sectionSquare E g s

/-- The actual base-change projection on the two original marking complements. -/
def smoothMarkingComplementProjection :
    Scheme.Opens.toScheme (X := (E.baseChange g).curve.left) (v).left.ker.support.compl ⟶
      Scheme.Opens.toScheme (X := E.curve.left) (t).left.ker.support.compl :=
  sectionPointComplementMap (H) (t).left (v).left (t).w (v).w (w)

variable [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]

omit [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsAffine T] [IsNoetherianRing Γ(T, ⊤)] in
/-- Original base scalars agree around the actual complement base-change square. -/
theorem smoothMarkingComplementProjection_scalar (r : Γ(S, ⊤)) :
    (smoothMarkingComplementProjection E g s).appTop (smoothMarkingComplementBaseMap E s r) =
      smoothMarkingComplementBaseMap (E.baseChange g) (pullSection g s) (g.appTop r) := by
  unfold smoothMarkingComplementBaseMap smoothMarkingComplementProjection
  have hh := congrArg Scheme.Hom.appTop
    (sectionPointComplementMap_base (H) (t).left (v).left (t).w (v).w (w))
  simp only [Scheme.Hom.comp_appTop] at hh
  exact ConcreteCategory.congr_hom hh r

variable (a : (pullback (s ≫ E.inclusion).left).obj
    (divisorLineBundle (s ≫ E.inclusion).left.ker
      (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

omit [IsAffine T] [IsNoetherianRing Γ(T, ⊤)] in
/-- Every transported chosen lift represents the actual pullback of its original function. -/
theorem smoothMarkingComplementProjection_lift (m : ℕ) (hm : 0 < m) :
    (smoothMarkingComplementProjection E g s).appTop
        (relativePoleFunction E.curve.hom (t).left (hI) (m + 1)
          (smoothMarkingFramedLift E s a m hm)) =
      relativePoleFunction (E.baseChange g).curve.hom (v).left (hJ) (m + 1)
        (smoothMarkingTransportedLift E g s a m hm) := by
  simpa only [smoothMarkingComplementProjection, smoothMarkingTransportedLift] using
    sectionPointComplementMap_relativeFunction (H) (t).left (v).left
      (t).w (v).w (w) (hI) (hJ) m (smoothMarkingFramedLift E s a m hm)

omit [IsAffine T] [IsNoetherianRing Γ(T, ⊤)] in
/-- The original x function pulls back to the actual transported order-two pole section. -/
theorem smoothMarkingComplementProjection_x :
    (smoothMarkingComplementProjection E g s).appTop (smoothMarkingComplementX E s a) =
      relativePoleFunction (E.baseChange g).curve.hom (v).left (hJ) 2
        (smoothMarkingTransportedLift E g s a 1 (by decide)) :=
  smoothMarkingComplementProjection_lift E g s a 1 (by decide)

omit [IsAffine T] [IsNoetherianRing Γ(T, ⊤)] in
/-- The original y function pulls back to the actual transported order-three pole section. -/
theorem smoothMarkingComplementProjection_y :
    (smoothMarkingComplementProjection E g s).appTop (smoothMarkingComplementY E s a) =
      relativePoleFunction (E.baseChange g).curve.hom (v).left (hJ) 3
        (smoothMarkingTransportedLift E g s a 2 (by decide)) :=
  smoothMarkingComplementProjection_lift E g s a 2 (by decide)

end FLT.Mazur.GeneralizedEllipticCurve
