/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicFullNaturality

/-!
# The actual cubic formula for every normalized full cyclic value

Every original label, including those outside the auxiliary factor, is projected
to its original proper cubic before applying the actual normalization comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f : T ⟶ (cyclicAuxiliaryScheme n).left)

/-- The original proper cubic value of each label of a full scheme-valued parameter. -/
def cyclicSchemeOriginalCubicValue (c : CyclicLabels n) :
    T ⟶ WeierstrassIntegralChart.integralCurve
      (auxiliaryPullbackEquation (cyclicSchemeAuxiliaryPoint n f).appTop.hom) :=
  (cyclicSchemeOriginalMarking n f c).left ≫
    auxiliarySchemeOriginalCubicProjection (cyclicSchemeAuxiliaryPoint n f)

/-- Every normalized cyclic label follows the original proper normalization formula. -/
theorem cyclicSchemeNormalizedPoint_value_cubic (c : CyclicLabels n) :
    cyclicSchemeNormalizedPoint n f ≫
      (cyclicAuxiliaryInclusion n ≫ AuxiliaryLevel.value universalGroup (CyclicLabels n) c).left =
    cyclicSchemeOriginalCubicValue n f c ≫
      (auxiliaryProperNormalization (cyclicSchemeAuxiliaryPoint n f).appTop.hom).inv ≫
        auxiliaryNormalizedCoefficientProjection (cyclicSchemeAuxiliaryPoint n f).appTop.hom := by
  rw [← cyclicSchemeNormalizedMarking_fst,
    ← auxiliarySchemeNormalizedCubicProjection_coefficient,
    cyclicSchemeNormalizedMarking]
  change ((_ ≫ (auxiliarySchemeNormalizationGroupIso
    (cyclicSchemeAuxiliaryPoint n f)).inv.hom.hom.hom).left) ≫ _ = _
  rw [Over.comp_left, Category.assoc,
    ← Category.assoc (auxiliarySchemeNormalizationGroupIso
      (cyclicSchemeAuxiliaryPoint n f)).inv.hom.hom.hom.left,
    auxiliarySchemeNormalizationGroupIso_inv_cubic]
  simp only [cyclicSchemeOriginalCubicValue, Category.assoc]

/-- The proper cubic formula retains the exact original universal value. -/
@[reassoc] theorem cyclicSchemeOriginalCubicValue_coefficient (c : CyclicLabels n) :
    cyclicSchemeOriginalCubicValue n f c ≫
        auxiliaryOriginalCoefficientProjection (cyclicSchemeAuxiliaryPoint n f).appTop.hom =
      f ≫
        (cyclicAuxiliaryInclusion n ≫
          AuxiliaryLevel.value universalGroup (CyclicLabels n) c).left :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ (cyclicSchemeOriginalMarking n f c).left ≫ z)
      (auxiliarySchemeOriginalCubicProjection_coefficient (cyclicSchemeAuxiliaryPoint n f))).trans
        (cyclicSchemeOriginalMarking_fst n f c))

end FLT.Mazur.UniversalWeierstrass
