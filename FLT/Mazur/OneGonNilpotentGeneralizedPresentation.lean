/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonNormalizedGeneralizedCurve
public import FLT.Mazur.ArithmeticOneGonAlgebraicFamily

/-!
# Full arithmetic presentations of arbitrary nilpotent nodal equations

Starting with the original reduced equation, choose a proved admissible normal
form and construct the generalized curve on that very cubic. Its intrinsic
group and whole action are identified with a pullback of the fixed arithmetic
family. This does not assume a presentation for an arbitrary abstract curve.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj WeierstrassCurve
namespace FLT.Mazur.OneGonInfinitesimal
open OneGonSmoothing WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (I : Ideal R)
  (hI : IsNilpotent I) (hW : W.map (Ideal.Quotient.mk I) = equation 0)

/-- Choose an admissible change whose existence was proved from the original coefficients. -/
def presentationChange : VariableChange R := (exists_relative_presentation W I hI hW).choose

/-- The actual nilpotent parameter belonging to that proved presentation. -/
def presentationParameter : R := (exists_relative_presentation W I hI hW).choose_spec.choose

/-- The chosen change normalizes the original equation. -/
theorem presentation_equation :
    presentationChange W I hI hW • W = equation (presentationParameter W I hI hW) :=
  (exists_relative_presentation W I hI hW).choose_spec.choose_spec.1

/-- The presentation fixes the original nodal reduction. -/
theorem presentationChange_reduction :
    (presentationChange W I hI hW).map (Ideal.Quotient.mk I) = 1 :=
  (exists_relative_presentation W I hI hW).choose_spec.choose_spec.2.1

/-- The constructed parameter lies in the original infinitesimal ideal. -/
theorem presentationParameter_mem : presentationParameter W I hI hW ∈ I :=
  (exists_relative_presentation W I hI hW).choose_spec.choose_spec.2.2.1

/-- The parameter belongs to the fixed arithmetic open in every characteristic. -/
theorem presentationParameter_unit : IsUnit (1 + 432 * presentationParameter W I hI hW) :=
  (exists_relative_presentation W I hI hW).choose_spec.choose_spec.2.2.2

/-- The generalized deformation with the independently constructed original operations. -/
def deformationCurve : GeneralizedEllipticCurve (Spec (.of R)) :=
  curveOfNormalForm W (presentationParameter W I hI hW) (presentationChange W I hI hW)
    (presentation_equation W I hI hW) (presentationParameter_unit W I hI hW)

/-- This is the original cubic over the original coefficient spectrum. -/
theorem deformationCurve_curve :
    (deformationCurve W I hI hW).curve = integralCurveOver W := rfl

/-- The generalized group is the independently constructed original smooth group. -/
theorem deformationCurve_group :
    (deformationCurve W I hI hW).group = (integralSmoothGroup W).X := rfl

/-- The action is exactly the original smooth-by-whole addition, including singular inputs. -/
theorem deformationCurve_action :
    (deformationCurve W I hI hW).act = integralSmoothWholeAction W := rfl

/-- The original infinity section is the identity of the full generalized deformation. -/
theorem deformationCurve_identity :
    (deformationCurve W I hI hW).identitySection.left = integralCurveZero W := by
  change (η[(integralSmoothGroup W).X] ≫
    (curveOfNormalForm W _ _ _ _).inclusion).left = _
  rw [curveOfNormalForm_inclusion]
  exact integralSmoothZero_inclusion W

/-- Every original nilpotent nodal equation is a full pullback of the arithmetic family. -/
@[irreducible] def algebraicPresentationIso :
    deformationCurve W I hI hW ≅
      ArithmeticOneGonParameter.universalCurve.baseChange
        (ArithmeticOneGonParameter.parameterMap (presentationParameter W I hI hW)
          (presentationParameter_unit W I hI hW)) :=
  (generalizedNormalFormIso W _ _ (presentation_equation W I hI hW)
    (presentationParameter_unit W I hI hW)).symm ≪≫
      ArithmeticOneGonParameter.specializationIso _ (presentationParameter_unit W I hI hW)

/-- The full algebraic presentation retains the original coefficient structural map. -/
@[reassoc] theorem algebraicPresentationIso_over :
    (algebraicPresentationIso W I hI hW).hom.curve.left ≫
      (ArithmeticOneGonParameter.universalCurve.baseChange
        (ArithmeticOneGonParameter.parameterMap (presentationParameter W I hI hW)
          (presentationParameter_unit W I hI hW))).curve.hom = integralCurveStructure W :=
  (algebraicPresentationIso W I hI hW).hom.curve.w

end FLT.Mazur.OneGonInfinitesimal
