/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryEtale

/-!
# Faithful affine level-three markings

The original scheme-valued markings give injective additive markings of the
classical affine point group over every coefficient field, including at two.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry WeierstrassCurve MonObj

namespace FLT.Mazur.OddWeierstrassParameter

open IntegralWeierstrassParameter (OddChartRing oddChartEquation oddChart_discriminant)
open UniversalWeierstrass (Labels)

variable (K : Type) [Field K] [DecidableEq K] [Algebra OddChartRing K]

/-- The original auxiliary sections, expressed as classical affine points. -/
def auxiliaryAffineMarking (f : fieldTest K ⟶ levelThree) :
    (ZMod 3 × ZMod 3) →+ (oddChartEquation.map (algebraMap OddChartRing K)).toAffine.Point :=
  (WeierstrassIntegralChart.integralAffinePointAddEquiv (K := K)
    oddChartEquation oddChart_discriminant).symm.toAddMonoidHom.comp
      (AuxiliaryLevel.markingOf universalGroup (Labels 3)
        (f ≫ levelThreeInclusion)).toAdditiveRight

/-- Faithfulness is inherited from the actual auxiliary scheme, on every coefficient field. -/
theorem auxiliaryAffineMarking_injective (f : fieldTest K ⟶ levelThree) :
    Function.Injective (auxiliaryAffineMarking K f) := by
  let _ : Nonempty (fieldTest K).left := ⟨IsLocalRing.closedPoint K⟩
  intro a b h
  apply levelThreeMarking_injective f
  exact congrArg Additive.toMul
    ((WeierstrassIntegralChart.integralAffinePointAddEquiv (K := K)
      oddChartEquation oddChart_discriminant).symm.injective h)

end FLT.Mazur.OddWeierstrassParameter
