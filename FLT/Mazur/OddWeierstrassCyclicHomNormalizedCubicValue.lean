/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomNormalizationNaturality
public import FLT.Mazur.OddWeierstrassAuxiliaryNormalizationCubic
public import FLT.Mazur.OddWeierstrassAuxiliaryCubicCoefficient

/-!
# Proper cubic values of unrestricted cyclic parameters

The actual normalization formula holds for every cyclic label, including
coincident labels and values on the zero section.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
open AuxiliaryLevel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)

/-- Every original cyclic label has its actual value on the proper coefficient cubic. -/
def cyclicHomOriginalCubicValue (c : Multiplicative (ZMod n)) :
    T ⟶ WeierstrassIntegralChart.integralCurve
      (auxiliaryPullbackEquation (cyclicHomAuxiliaryPoint n f).appTop.hom) :=
  (cyclicHomSourceMarking n f c).left ≫
    auxiliarySchemeOriginalCubicProjection (cyclicHomAuxiliaryPoint n f)

/-- Normalization transports each full cyclic value through the original proper comparison. -/
theorem cyclicHomNormalizedPoint_value_cubic (c : Multiplicative (ZMod n)) :
    cyclicHomNormalizedPoint n f ≫
        (cyclicHomParameter n ≫ value universalGroup (Multiplicative (ZMod n)) c).left =
      cyclicHomOriginalCubicValue n f c ≫
        (auxiliaryProperNormalization (cyclicHomAuxiliaryPoint n f).appTop.hom).inv ≫
          auxiliaryNormalizedCoefficientProjection (cyclicHomAuxiliaryPoint n f).appTop.hom := by
  rw [cyclicHomNormalizedPoint_value,
    ← auxiliarySchemeNormalizedCubicProjection_coefficient,
    ← Category.assoc (auxiliarySchemeNormalizationGroupIso
      (cyclicHomAuxiliaryPoint n f)).inv.hom.hom.hom.left,
    auxiliarySchemeNormalizationGroupIso_inv_cubic]
  simp only [cyclicHomOriginalCubicValue, Category.assoc]

/-- Projection retains the original universal cyclic value exactly. -/
@[reassoc] theorem cyclicHomOriginalCubicValue_coefficient (c : Multiplicative (ZMod n)) :
    cyclicHomOriginalCubicValue n f c ≫
        auxiliaryOriginalCoefficientProjection (cyclicHomAuxiliaryPoint n f).appTop.hom =
      f ≫ (cyclicHomParameter n ≫ value universalGroup (Multiplicative (ZMod n)) c).left := by
  rw [cyclicHomOriginalCubicValue, Category.assoc,
    auxiliarySchemeOriginalCubicProjection_coefficient, cyclicHomSourceMarking_fst]

end FLT.Mazur.OddWeierstrassParameter
