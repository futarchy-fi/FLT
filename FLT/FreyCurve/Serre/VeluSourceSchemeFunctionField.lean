/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluSourceFractionField
public import FLT.Mazur.WeierstrassIntegralDomain
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# The quadratic model and the actual cubic's generic stalk

The affine chart fraction field agrees with its generic stalk. The original
open immersion identifies that stalk with the generic stalk of the whole cubic.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] (E : WeierstrassCurve K)

/-- The original affine coordinates act on the affine generic stalk. -/
instance sourceAffineStalkAlgebra :
    Algebra (Coordinate E 2) (chartScheme E 2).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of (Coordinate E 2))

/-- The affine generic stalk is a fraction ring for its original coordinates. -/
instance sourceAffineStalkFractionRing :
    IsFractionRing (Coordinate E 2) (chartScheme E 2).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of (Coordinate E 2))

/-- The quadratic model is the actual affine chart's scheme function field. -/
def sourceAffineFunctionFieldEquiv :
    FunctionField E ≃ₐ[Coordinate E 2] (chartScheme E 2).functionField :=
  IsLocalization.algEquiv (nonZeroDivisors (Coordinate E 2)) _ _

/-- The original affine inclusion identifies the two actual generic stalks. -/
def sourceCurveFunctionFieldIso :
    (integralCurve E).functionField ≅ (chartScheme E 2).functionField :=
  (integralCurve E).presheaf.stalkCongr
    (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion (integralCurveChart E 2)).symm) ≪≫
      asIso ((integralCurveChart E 2).stalkMap (genericPoint (chartScheme E 2)))

omit [CharZero K] in
/-- The generic-stalk comparison retains the original affine open immersion. -/
@[reassoc] theorem sourceCurveFunctionFieldIso_fromSpecStalk :
    Spec.map (sourceCurveFunctionFieldIso E).hom ≫
        (integralCurve E).fromSpecStalk (genericPoint (integralCurve E)) =
      (chartScheme E 2).fromSpecStalk (genericPoint (chartScheme E 2)) ≫
        integralCurveChart E 2 := by
  simp only [sourceCurveFunctionFieldIso, Iso.trans_hom,
    TopCat.Presheaf.stalkCongr_hom, asIso_hom, Spec.map_comp, Category.assoc]
  rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- Identify the original quadratic field with the actual glued cubic's function field. -/
def sourceSchemeFunctionFieldEquiv :
    FunctionField E ≃+* (integralCurve E).functionField :=
  (sourceAffineFunctionFieldEquiv E).toRingEquiv.trans
    (CategoryTheory.Iso.commRingCatIsoToRingEquiv (sourceCurveFunctionFieldIso E)).symm

end WeierstrassCurve.Velu
