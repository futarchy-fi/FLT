/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingOpenCubic
public import FLT.Mazur.GeneralizedCurveMarkingOverlapCocycle

/-!
# Constructed cubic transitions on intersections of affine frame opens

Two independently framed affine opens restrict to any affine open inside their
intersection. The original marking frames construct the transition and a span
of open immersions into the two original cubics. The base need not be affine
or separated, so the entire intersection is not assumed affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback smoothMarkingWeierstrassCurve smoothMarkingTransportedFrame
variable {S : Scheme} [IsLocallyNoetherian S] (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group) (U V W : S.Opens)
  [IsAffine U.toScheme] [IsAffine V.toScheme] [IsAffine W.toScheme]
  (hU : W ≤ U) (hV : W ≤ V)
  (a : SmoothMarkingFrame (E.baseChange U.ι) (pullSection U.ι s))
  (b : SmoothMarkingFrame (E.baseChange V.ι) (pullSection V.ι s))

local instance affineOverlapNoetherian (X : S.Opens) [IsAffine X.toScheme] :
    IsNoetherianRing Γ(X.toScheme, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

omit [IsLocallyNoetherian S] [IsAffine U.toScheme] [IsAffine V.toScheme]
  [IsAffine W.toScheme] in
/-- The two actual inclusions from a common open give the same original base map. -/
theorem smoothMarkingOpenOverlap_square :
    S.homOfLE hV ≫ V.ι = S.homOfLE hU ≫ U.ι := by
  rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]

local notation "A" => smoothMarkingOpenRestrictionEquation E s U W hU a
local notation "B" => smoothMarkingOpenRestrictionEquation E s V W hV b
local notation "aW" => smoothMarkingOpenRestrictionFrame E s U W hU a
local notation "bW" => smoothMarkingOpenRestrictionFrame E s V W hV b

/-- The two independent chart frames construct a transition on their affine intersection piece. -/
def smoothMarkingAffineOverlapIso : integralCurve A ≅ integralCurve B :=
  smoothMarkingOverlapCubicIso E U.ι V.ι (S.homOfLE hU) (S.homOfLE hV)
    (smoothMarkingOpenOverlap_square U V W hU hV) s aW bW

omit [IsAffine U.toScheme] [IsAffine V.toScheme] in
/-- The affine intersection transition preserves the common base spectrum. -/
@[reassoc] theorem smoothMarkingAffineOverlapIso_over :
    (smoothMarkingAffineOverlapIso E s U V W hU hV a b).hom ≫ integralCurveStructure B =
      integralCurveStructure A := smoothMarkingOverlapCubicIso_over _ _ _ _ _ _ _ _ _

omit [IsAffine U.toScheme] [IsAffine V.toScheme] in
/-- The affine intersection transition preserves the infinity marking. -/
@[reassoc] theorem smoothMarkingAffineOverlapIso_zero :
    integralCurveZero A ≫ (smoothMarkingAffineOverlapIso E s U V W hU hV a b).hom =
      integralCurveZero B := smoothMarkingOverlapCubicIso_zero _ _ _ _ _ _ _ _ _

/-- The common overlap piece maps to the second original cubic chart. -/
def smoothMarkingAffineOverlapRight : integralCurve A ⟶
    integralCurve (smoothMarkingWeierstrassCurve (E.baseChange V.ι) (pullSection V.ι s) b) :=
  (smoothMarkingAffineOverlapIso E s U V W hU hV a b).hom ≫
    smoothMarkingOpenRestrictionProjection E s V W hV b

/-- Both legs of the constructed overlap span are genuine open immersions. -/
instance smoothMarkingAffineOverlapRight_isOpenImmersion :
    IsOpenImmersion (smoothMarkingAffineOverlapRight E s U V W hU hV a b) := by
  unfold smoothMarkingAffineOverlapRight
  infer_instance

end FLT.Mazur.GeneralizedEllipticCurve
