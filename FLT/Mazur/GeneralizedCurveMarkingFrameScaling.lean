/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPoleFrameChange
public import FLT.Mazur.GeneralizedCurveMarkingComplementCoordinates

/-!
# Exact frame scaling on the original generalized family

Two frames of the same marking line scale the actual normalized lifts and
complement functions by the expected unit powers. The original family may
have higher polygons, nilpotents, and mixed characteristic.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPoleMultiplicativeCoordinates relativePoleFunction
variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

local instance generalizedCurveMarkingFrameScalingProper :
    IsProper E.curve.hom := E.family.family.1

variable (e f : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

/-- The actual transition unit of the original marking line. -/
def smoothMarkingFrameUnit : Γ(S, ⊤)ˣ := frameComparisonUnit e f ⊤

/-- Every positive normalized lift changes by its precise pole-degree power. -/
theorem smoothMarkingFramedLift_frameChange (m : ℕ) (hm : 0 < m) :
    smoothMarkingFramedLift E s f m hm =
      (smoothMarkingFrameUnit E s e f : Γ(S, ⊤)) ^ (m + 1) •
        smoothMarkingFramedLift E s e m hm := by
  let _ : Subsingleton
      (ModuleH (tensorPower (divisorLineBundle (t).left.ker (hI)) m) 1) :=
    smoothMarkingPower_relative_acyclic E s m hm 0
  exact sectionPoleNormalizedLift_frameChange (S := S) (t).left (hI) e f E.curve.hom (t).w m

/-- The actual order-two function has weight two under the marking-frame change. -/
theorem smoothMarkingComplementX_frameChange :
    smoothMarkingComplementX E s f =
      smoothMarkingComplementBaseMap E s
        ((smoothMarkingFrameUnit E s e f : Γ(S, ⊤)) ^ 2) *
          smoothMarkingComplementX E s e := by
  unfold smoothMarkingComplementX
  rw [smoothMarkingFramedLift_frameChange E s e f, relativePoleFunction_smul]
  rfl

/-- The actual order-three function has weight three under the same frame change. -/
theorem smoothMarkingComplementY_frameChange :
    smoothMarkingComplementY E s f =
      smoothMarkingComplementBaseMap E s
        ((smoothMarkingFrameUnit E s e f : Γ(S, ⊤)) ^ 3) *
          smoothMarkingComplementY E s e := by
  unfold smoothMarkingComplementY
  rw [smoothMarkingFramedLift_frameChange E s e f, relativePoleFunction_smul]
  rfl

omit [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] in
/-- Frame transitions on the original family satisfy the triple-frame cocycle. -/
theorem smoothMarkingFrameUnit_cocycle
    (g : (pullback (s ≫ E.inclusion).left).obj
      (divisorLineBundle (s ≫ E.inclusion).left.ker
        (smoothMarking_relativeCartier E s).1) ≅ structureModule S) :
    smoothMarkingFrameUnit E s e f * smoothMarkingFrameUnit E s f g =
      smoothMarkingFrameUnit E s e g := frameComparisonUnit_cocycle e f g ⊤

end FLT.Mazur.GeneralizedEllipticCurve
