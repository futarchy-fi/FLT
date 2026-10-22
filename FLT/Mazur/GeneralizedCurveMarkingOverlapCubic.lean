/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkedCubicComparison
public import FLT.Mazur.GeneralizedCurveMarkingOverlap

/-!
# Cubic transitions between distinct base-chart restrictions

The two paths through a commuting square carry independent marking frames.
Their actual full-family comparison constructs the pointed cubic transition.
Only the common base is required to be affine Noetherian.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FCurve.divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback smoothMarkingWeierstrassCurve markedCubicComparison
variable {S T U V : Scheme} [IsAffine V] [IsNoetherianRing Γ(V, ⊤)]
  (E : GeneralizedEllipticCurve S) (g : T ⟶ S) (h : U ⟶ S)
  (p : V ⟶ T) (q : V ⟶ U) (w : q ≫ h = p ≫ g)
  (s : 𝟙_ (Over S) ⟶ E.group)
  (a : SmoothMarkingFrame ((E.baseChange g).baseChange p) (pullSection p (pullSection g s)))
  (b : SmoothMarkingFrame ((E.baseChange h).baseChange q) (pullSection q (pullSection h s)))
local notation "L" => GeneralizedEllipticCurve.baseChange (E.baseChange g) p
local notation "R" => GeneralizedEllipticCurve.baseChange (E.baseChange h) q
local notation "sL" => pullSection p (pullSection g s)
local notation "sR" => pullSection q (pullSection h s)
local notation "WL" => smoothMarkingWeierstrassCurve L sL a
local notation "WR" => smoothMarkingWeierstrassCurve R sR b
local notation "e" => Iso.app (baseChangeSquare g h q p w) E

/-- Independent frames on the two restricted families construct an overlap transition. -/
def smoothMarkingOverlapCubicIso : integralCurve WL ≅ integralCurve WR :=
  markedCubicComparison (e) sR sL (smoothMarkingOverlap_group E g h p q w s) b a

/-- The overlap transition preserves the actual common coefficient base. -/
@[reassoc] theorem smoothMarkingOverlapCubicIso_over :
    (smoothMarkingOverlapCubicIso E g h p q w s a b).hom ≫ integralCurveStructure WR =
      integralCurveStructure WL := markedCubicComparison_over _ _ _ _ _ _

/-- The overlap transition carries the original cubic marking to the other marking. -/
@[reassoc] theorem smoothMarkingOverlapCubicIso_zero :
    integralCurveZero WL ≫ (smoothMarkingOverlapCubicIso E g h p q w s a b).hom =
      integralCurveZero WR := markedCubicComparison_zero _ _ _ _ _ _

/-- The overlap transition commutes with the whole original family comparison. -/
@[reassoc] theorem smoothMarkingOverlapCubicIso_whole :
    smoothMarkingToIntegralCubic L sL a ≫
      (smoothMarkingOverlapCubicIso E g h p q w s a b).hom =
        (e).inv.curve.left ≫ smoothMarkingToIntegralCubic R sR b :=
  markedCubicComparison_whole _ _ _ _ _ _

end FLT.Mazur.GeneralizedEllipticCurve
