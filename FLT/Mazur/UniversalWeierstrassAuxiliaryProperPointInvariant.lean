/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizationRigidity
public import FLT.Mazur.UniversalWeierstrassNormalizedCoefficientTransport
public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeAffineAgreement

/-!
# Proper comparisons identify normalized auxiliary scheme points

A marked comparison over the original global sections determines all normalized
coefficients and labeled coordinates, without assuming the source is affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {T : Scheme} (f g : T ⟶ levelFour.left)
  (e : integralCurve (auxiliaryPullbackEquation f.appTop.hom) ≅
    integralCurve (auxiliaryPullbackEquation g.appTop.hom))
  (hb : e.hom ≫ integralCurveStructure (auxiliaryPullbackEquation g.appTop.hom) =
    integralCurveStructure (auxiliaryPullbackEquation f.appTop.hom))
  (hz : integralCurveZero (auxiliaryPullbackEquation f.appTop.hom) ≫ e.hom =
    integralCurveZero (auxiliaryPullbackEquation g.appTop.hom))
  (hm : ∀ (a : Labels 4) (ha : a ≠ 1),
    auxiliaryPullbackSection f.appTop.hom a ha ≫ e.hom =
      auxiliaryPullbackSection g.appTop.hom a ha)

include hb hz hm in
/-- An actual marked proper comparison identifies the entire normalized auxiliary point. -/
theorem auxiliarySchemeNormalizedPoint_invariant_of_proper_comparison :
    auxiliarySchemeNormalizedPoint f = auxiliarySchemeNormalizedPoint g := by
  have he := (auxiliaryNormalization_invariant f.appTop.hom g.appTop.hom e hb hz hm).1
  have hc := auxiliaryNormalizedCoefficientHom_eq_of_equation f.appTop.hom g.appTop.hom he
  apply auxiliarySchemePoint_ext_coordinates
  · rw [auxiliarySchemeNormalizedPoint_base, auxiliarySchemeNormalizedPoint_base]
    exact congrArg (fun k ↦ T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k)) hc
  · intro a ha i
    rw [auxiliarySchemeNormalizedPoint_coordinate, auxiliarySchemeNormalizedPoint_coordinate]
    exact auxiliaryNormalizedMarking_invariant f.appTop.hom g.appTop.hom e hb hz hm a ha i

end FLT.Mazur.UniversalWeierstrass
