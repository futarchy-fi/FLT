/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkedCubicInverse
public import FLT.Mazur.GeneralizedCurveMarkingOpenCubic
public import FLT.Mazur.GeneralizedCurveGroupSectionComposition

/-!
# Cubic maps between directly framed affine opens

An inclusion of affine opens constructs an open immersion between their
independently framed cubics. The actual equal-composite family associator
compares the direct and iterated restrictions before the cubic projection.
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
  (s : 𝟙_ (Over S) ⟶ E.group) (U W : S.Opens)
  [IsAffine U.toScheme] [IsAffine W.toScheme] (h : W ≤ U)
  (a : SmoothMarkingFrame (E.baseChange U.ι) (pullSection U.ι s))
  (b : SmoothMarkingFrame (E.baseChange W.ι) (pullSection W.ι s))

local instance directRestrictionNoetherian (X : S.Opens) [IsAffine X.toScheme] :
    IsNoetherianRing Γ(X.toScheme, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

local notation "e" => E.baseChangeCompEqIso U.ι (S.homOfLE h) W.ι
  (Eq.symm (Scheme.homOfLE_ι S h))
local notation "hs" => E.baseChangeCompEqIso_groupSection U.ι (S.homOfLE h) W.ι
  (Eq.symm (Scheme.homOfLE_ι S h)) s
local notation "aW" => smoothMarkingOpenRestrictionFrame E s U W h a
local notation "i" => markedCubicComparison (e) (pullSection W.ι s)
  (pullSection (S.homOfLE h) (pullSection U.ι s)) (hs) b aW
local notation "C" => smoothMarkingWeierstrassCurve (E.baseChange U.ι) (pullSection U.ι s) a
local notation "D" => smoothMarkingWeierstrassCurve (E.baseChange W.ι) (pullSection W.ι s) b

/-- Direct affine charts map by the actual associator and whole cubic projection. -/
def smoothMarkingDirectRestriction : integralCurve D ⟶ integralCurve C :=
  (i).inv ≫ smoothMarkingOpenRestrictionProjection E s U W h a

/-- Inclusions of directly framed opens induce open immersions of their whole cubics. -/
instance smoothMarkingDirectRestriction_isOpenImmersion :
    IsOpenImmersion (smoothMarkingDirectRestriction E s U W h a b) := by
  unfold smoothMarkingDirectRestriction
  infer_instance

/-- The direct restriction retains the coefficient spectrum map. -/
@[reassoc] theorem smoothMarkingDirectRestriction_over :
    smoothMarkingDirectRestriction E s U W h a b ≫ integralCurveStructure C =
      integralCurveStructure D ≫ Spec.map (S.homOfLE h).appTop := by
  rw [smoothMarkingDirectRestriction, smoothMarkingOpenRestrictionProjection,
    Category.assoc, smoothMarkingCubicProjection_over,
    ← Category.assoc, markedCubicComparison_inv_over]

/-- The direct restriction retains the original whole-family associator. -/
@[reassoc] theorem smoothMarkingDirectRestriction_whole :
    smoothMarkingToIntegralCubic (E.baseChange W.ι) (pullSection W.ι s) b ≫
      smoothMarkingDirectRestriction E s U W h a b =
        (e).hom.curve.left ≫ Limits.pullback.fst (E.baseChange U.ι).curve.hom
          (S.homOfLE h) ≫
            smoothMarkingToIntegralCubic (E.baseChange U.ι) (pullSection U.ι s) a := by
  rw [smoothMarkingDirectRestriction, ← Category.assoc,
    markedCubicComparison_inv_whole, Category.assoc,
    smoothMarkingOpenRestrictionProjection_whole]

end FLT.Mazur.GeneralizedEllipticCurve
