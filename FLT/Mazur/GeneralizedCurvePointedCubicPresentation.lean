/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveRelativePointFrames
public import FLT.Mazur.RelativeGenusOnePointedPresentation

/-!
# Complete pointed cubics for original smooth generalized elliptic curves

The original smooth inclusion supplies the group object and the family supplies
the geometric genus. The original marking is Cartier by smoothness. With a
frame of its restricted divisor line, the constructed coefficients give an
elliptic cubic and an actual pointed isomorphism of the entire original curve.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve WeierstrassIntegralChart ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates

variable {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) [SmoothOfRelativeDimension 1 E.curve.hom]
  [GeometricallyIntegral E.curve.hom]

/-- Properness is supplied by the original generalized-curve family. -/
local instance smoothPointPresentationProper : IsProper E.curve.hom := E.family.family.1

/-- The actual smooth inclusion transports the original group to the whole smooth curve. -/
local instance smoothPointPresentationGroup : GrpObj E.curve := by
  let _ : Smooth E.curve.hom := SmoothOfRelativeDimension.smooth 1 E.curve.hom
  exact GrpObj.ofIso (asIso E.inclusion)

variable (s : 𝟙_ (Over S) ⟶ E.curve)
  (e : (pullback s.left).obj (divisorLineBundle s.left.ker (smoothPoint_cartier E s)) ≅
    structureModule S)

/-- The actual coefficient equation constructed from the original smooth curve and marking. -/
def smoothPointCubicEquation : WeierstrassCurve Γ(S, ⊤) :=
  relativePointWeierstrassCurve E.curve E.family.genus s (smoothPoint_cartier E s) e

/-- The original coefficient equation has unit discriminant, over the original base ring. -/
theorem smoothPointCubicEquation_isElliptic : (smoothPointCubicEquation E s e).IsElliptic :=
  relativePointWeierstrass_isElliptic E.curve E.family.genus s (smoothPoint_cartier E s) e

/-- The entire original smooth curve has this actual complete projective presentation. -/
def smoothPointCubicIso : E.curve.left ≅ integralCurve (smoothPointCubicEquation E s e) :=
  relativePointIntegralCubicIso E.curve E.family.genus s (smoothPoint_cartier E s) e

/-- The complete presentation retains the original varying structural map. -/
@[reassoc] theorem smoothPointCubicIso_over :
    (smoothPointCubicIso E s e).hom ≫ integralCurveStructure (smoothPointCubicEquation E s e) =
      E.curve.hom ≫ S.toSpecΓ :=
  relativePointIntegralCubicIso_over E.curve E.family.genus s (smoothPoint_cartier E s) e

/-- The complete presentation takes the specified original marking to the actual infinity point. -/
@[reassoc] theorem smoothPointCubicIso_marking :
    s.left ≫ (smoothPointCubicIso E s e).hom =
      S.toSpecΓ ≫ integralCurveZero (smoothPointCubicEquation E s e) :=
  relativePointIntegralCubicIso_marking E.curve E.family.genus s (smoothPoint_cartier E s) e

end FLT.Mazur.GeneralizedEllipticCurve
