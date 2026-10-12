/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizationRigidity
public import FLT.Mazur.UniversalWeierstrassNormalizedCoefficientTransport
public import FLT.Mazur.UniversalWeierstrassCyclicNormalizedValueCubic
public import FLT.Mazur.UniversalWeierstrassCyclicNormalizationRelation

/-!
# Full cyclic normalization is invariant under actual proper presentations

An actual isomorphism of the original cubics over source global sections,
preserving the auxiliary frame and all original full values, identifies the
complete normalized parameters. No affine-chart hypothesis on cyclic values is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f g : T ⟶ (cyclicAuxiliaryScheme n).left)
variable (e : integralCurve (auxiliaryPullbackEquation (cyclicSchemeAuxiliaryPoint n
  f).appTop.hom) ≅
    integralCurve (auxiliaryPullbackEquation (cyclicSchemeAuxiliaryPoint n g).appTop.hom))
  (hb : e.hom ≫ integralCurveStructure (auxiliaryPullbackEquation (cyclicSchemeAuxiliaryPoint n
    g).appTop.hom) =
    integralCurveStructure (auxiliaryPullbackEquation (cyclicSchemeAuxiliaryPoint n f).appTop.hom))
  (hz : integralCurveZero (auxiliaryPullbackEquation (cyclicSchemeAuxiliaryPoint n f).appTop.hom)
    ≫ e.hom =
    integralCurveZero (auxiliaryPullbackEquation (cyclicSchemeAuxiliaryPoint n g).appTop.hom))
  (hm : ∀ (c : Labels 4) (hc : c ≠ 1),
    auxiliaryPullbackSection (cyclicSchemeAuxiliaryPoint n f).appTop.hom c hc ≫ e.hom =
      auxiliaryPullbackSection (cyclicSchemeAuxiliaryPoint n g).appTop.hom c hc)
  (hv : ∀ c : CyclicLabels n,
    cyclicSchemeOriginalCubicValue n f c ≫ e.hom = cyclicSchemeOriginalCubicValue n g c)

include hb hz hm hv in
/-- Actual original marked proper comparisons identify every normalized cyclic value. -/
theorem cyclicSchemeNormalizedPoint_invariant_of_proper_comparison :
    cyclicSchemeNormalizedPoint n f = cyclicSchemeNormalizedPoint n g := by
  have he := (auxiliaryNormalization_invariant (cyclicSchemeAuxiliaryPoint n f).appTop.hom
    (cyclicSchemeAuxiliaryPoint n g).appTop.hom e hb hz hm).1
  have hc := auxiliaryNormalizedCoefficientHom_eq_of_equation (cyclicSchemeAuxiliaryPoint n
    f).appTop.hom (cyclicSchemeAuxiliaryPoint n g).appTop.hom he
  apply cyclicSchemePoint_ext n
  · rw [cyclicSchemeNormalizedPoint_base, cyclicSchemeNormalizedPoint_base,
      auxiliarySchemeNormalizedPoint_base, auxiliarySchemeNormalizedPoint_base]
    exact congrArg (fun k ↦ T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k)) hc
  · intro c
    rw [cyclicSchemeNormalizedPoint_value_cubic n f c,
      cyclicSchemeNormalizedPoint_value_cubic n g c]
    have hs := auxiliaryProperSection_normalization_invariant (cyclicSchemeAuxiliaryPoint n
      f).appTop.hom (cyclicSchemeAuxiliaryPoint n g).appTop.hom e hb hz hm
      (cyclicSchemeOriginalCubicValue n f c) (cyclicSchemeOriginalCubicValue n g c) (hv c) he
    have hp := congrArg (fun z ↦ z ≫ auxiliaryNormalizedCoefficientProjection
      (cyclicSchemeAuxiliaryPoint n g).appTop.hom) hs
    simpa only [Category.assoc, auxiliaryNormalizedCoefficientProjection_transport
      (cyclicSchemeAuxiliaryPoint n f).appTop.hom
      (cyclicSchemeAuxiliaryPoint n g).appTop.hom he] using hp

include hb hz hm hv in
/-- The same actual comparison identifies the complete original closed-slice parameters. -/
theorem cyclicNormalizationSliceMap_invariant_of_proper_comparison :
    f ≫ cyclicNormalizationSliceMap n = g ≫ cyclicNormalizationSliceMap n :=
  (cyclicNormalizationRelation_iff n f g).mpr
    (cyclicSchemeNormalizedPoint_invariant_of_proper_comparison n f g e hb hz hm hv)

end FLT.Mazur.UniversalWeierstrass
