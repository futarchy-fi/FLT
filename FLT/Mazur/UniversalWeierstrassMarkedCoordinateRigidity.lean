/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryEtale
public import FLT.Mazur.WeierstrassFourMarkingRigidity

/-!
# Coordinate rigidity on the actual auxiliary cover

The field-valued markings here are obtained from the original universal
sections on the constructed etale auxiliary cover. Their faithfulness makes
any marking-preserving admissible coordinate automorphism the identity.
The classification of all scheme automorphisms as coordinate changes is a
separate step.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry WeierstrassCurve MonObj

namespace FLT.Mazur.UniversalWeierstrass

variable (K : Type) [Field K] [DecidableEq K] [Algebra ParameterRing K]

/-- The original auxiliary sections, expressed as classical affine points. -/
def auxiliaryAffineMarking (f : fieldTest K ⟶ levelFour) :
    (ZMod 4 × ZMod 4) →+ (smoothEquation.map (algebraMap ParameterRing K)).toAffine.Point :=
  (WeierstrassIntegralChart.integralAffinePointAddEquiv (K := K)
    smoothEquation smoothEquation_discriminant).symm.toAddMonoidHom.comp
      (AuxiliaryLevel.markingOf universalGroup (Labels 4)
        (f ≫ auxiliaryInclusion 4)).toAdditiveRight

/-- Faithfulness is inherited from the actual auxiliary scheme, on every coefficient field. -/
theorem auxiliaryAffineMarking_injective (f : fieldTest K ⟶ levelFour) :
    Function.Injective (auxiliaryAffineMarking K f) := by
  let _ : Nonempty (fieldTest K).left := ⟨IsLocalRing.closedPoint K⟩
  intro a b h
  apply auxiliaryMarking_injective 4 f
  exact congrArg Additive.toMul
    ((WeierstrassIntegralChart.integralAffinePointAddEquiv (K := K)
      smoothEquation smoothEquation_discriminant).symm.injective h)

/-- The three distinguished original sections give a nondegenerate affine coordinate frame. -/
theorem auxiliaryAffineMarking_frame (f : fieldTest K ⟶ levelFour) :
    ∃ (x y z w : K)
      (hP : (smoothEquation.map (algebraMap ParameterRing K)).toAffine.Nonsingular x y)
      (hQ : (smoothEquation.map (algebraMap ParameterRing K)).toAffine.Nonsingular z w),
      auxiliaryAffineMarking K f (1, 0) = .some x y hP ∧
      auxiliaryAffineMarking K f (0, 1) = .some z w hQ ∧ x ≠ z ∧
      y ≠ (smoothEquation.map (algebraMap ParameterRing K)).toAffine.negY x y :=
  WeierstrassFourMarkingFrame.exists_frame _ _ (auxiliaryAffineMarking_injective K f)

/-- On an actual auxiliary-cover point, preserving its marking kills coordinate automorphisms. -/
theorem auxiliary_coordinate_rigidity (f : fieldTest K ⟶ levelFour)
    (C : VariableChange K)
    (hC : C • smoothEquation.map (algebraMap ParameterRing K) =
      smoothEquation.map (algebraMap ParameterRing K))
    (hf : let _ : smoothEquation.IsElliptic := ⟨smoothEquation_discriminant⟩
      ∀ a, WeierstrassFourMarkingRigidity.action _ C hC (auxiliaryAffineMarking K f a) =
        auxiliaryAffineMarking K f a) : C = 1 := by
  let _ : smoothEquation.IsElliptic := ⟨smoothEquation_discriminant⟩
  exact WeierstrassFourMarkingRigidity.eq_one _ C hC _
    (auxiliaryAffineMarking_injective K f) hf

end FLT.Mazur.UniversalWeierstrass
