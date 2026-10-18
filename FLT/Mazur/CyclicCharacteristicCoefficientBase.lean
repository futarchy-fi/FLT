/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicNormalizedSubgroup
public import FLT.Mazur.GeneralizedCurveBaseChangeCompEq

/-!
# The original coefficient maps of normalized characteristic families

Both normalized families are explicit pullbacks of their original smooth
long Weierstrass equations. The comparison retains the full curve and action.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.CyclicCharacteristicAtlas
open WeierstrassIntegralChart GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The coefficient ring of either characteristic chart. -/
def CoefficientRing : Bool → Type
  | false => UniversalWeierstrass.ParameterRing
  | true => IntegralWeierstrassParameter.OddChartRing

instance coefficientRingCommRing : (b : Bool) → CommRing (CoefficientRing b)
  | false => inferInstanceAs (CommRing UniversalWeierstrass.ParameterRing)
  | true => inferInstanceAs (CommRing IntegralWeierstrassParameter.OddChartRing)

/-- The original long equation, before introducing any subgroup parameters. -/
def coefficientEquation : (b : Bool) → WeierstrassCurve (CoefficientRing b)
  | false => UniversalWeierstrass.smoothEquation
  | true => IntegralWeierstrassParameter.oddChartEquation

/-- Both coefficient charts retain their proved unit discriminants. -/
theorem coefficientEquation_unit (b : Bool) : IsUnit (coefficientEquation b).Δ := by
  cases b
  · exact UniversalWeierstrass.smoothEquation_discriminant
  · exact IntegralWeierstrassParameter.oddChart_discriminant

/-- The full smooth generalized model on each original coefficient chart. -/
def coefficientModel (b : Bool) : GeneralizedEllipticCurve (Spec (.of (CoefficientRing b))) :=
  integralGeneralizedEllipticCurve (coefficientEquation b) (coefficientEquation_unit b)

variable (n : ℕ) [NeZero n]

/-- Forget auxiliary and cyclic markings to recover the original coefficient map. -/
def locusCoefficientMap : (b : Bool) → locus n b ⟶ Spec (.of (CoefficientRing b))
  | false => UniversalWeierstrass.cyclicHomAuxiliaryPoint n
      (UniversalWeierstrass.cyclicHomUniversalMultiplicationLocusInclusion n) ≫
        UniversalWeierstrass.levelFour.hom
  | true => OddWeierstrassParameter.cyclicHomAuxiliaryPoint n
      (OddWeierstrassParameter.cyclicHomUniversalMultiplicationLocusInclusion n) ≫
        OddWeierstrassParameter.levelThree.hom

/-- The actual unnormalized full family is exactly its coefficient pullback. -/
theorem curve_eq_coefficient (b : Bool) : curve n b =
    (coefficientModel b).baseChange (locusCoefficientMap n b) := by
  cases b <;> rfl

/-- The normalized chart keeps its original coefficient map. -/
def normalizedCoefficientMap (b : Bool) :
    normalizedLocus n b ⟶ Spec (.of (CoefficientRing b)) :=
  normalizedInclusion n b ≫ locusCoefficientMap n b

/-- Collapse the iterated pullback as an isomorphism of whole generalized curves. -/
def normalizedCoefficientIso (b : Bool) :
    (coefficientModel b).baseChange (normalizedCoefficientMap n b) ≅ normalizedCurve n b :=
  (coefficientModel b).baseChangeCompIso (locusCoefficientMap n b) (normalizedInclusion n b) ≪≫
      (baseChangeFunctor (normalizedInclusion n b)).mapIso (eqToIso (curve_eq_coefficient n b).symm)

end FLT.Mazur.CyclicCharacteristicAtlas
