/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonParameterIso
public import FLT.Mazur.CharacterSchemeBaseChange

/-!
# Full arithmetic one-gon comparison from two coefficient rings

Equal images of the smoothing parameters identify the full generalized curves,
including their actions on the whole cubic. Projection recovers the established
common whole-curve comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonGeneralizedCurve
open OneGonSmoothing CharacterSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A C] [Algebra B C] (a : A) (b : B)
  (ha : IsUnit (1 + 432 * a)) (hb : IsUnit (1 + 432 * b))
  (h : algebraMap A C a = algebraMap B C b)

/-- The full arithmetic comparison between two independent coefficient models. -/
irreducible_def commonCoefficientIso :
    (curve a ha).baseChange (baseMap A C) ≅ (curve b hb).baseChange (baseMap B C) :=
  (coefficientIso (S := C) a ha).symm ≪≫
    parameterIso h (coefficientParameter_isUnit (S := C) a ha)
      (coefficientParameter_isUnit (S := C) b hb) ≪≫ coefficientIso (S := C) b hb

/-- Both comparisons recover from the same intrinsic arithmetic curve. -/
@[reassoc] theorem commonCoefficientIso_recovery :
    (coefficientIso (S := C) a ha).hom ≫ (commonCoefficientIso a b ha hb h).hom =
      (parameterIso h (coefficientParameter_isUnit (S := C) a ha)
        (coefficientParameter_isUnit (S := C) b hb)).hom ≫
      (coefficientIso (S := C) b hb).hom := by
  rw [commonCoefficientIso_def]
  exact iso_common_recovery _ _ _

/-- The full comparison retains the original whole-cubic isomorphism. -/
theorem commonCoefficientIso_curve :
    (commonCoefficientIso a b ha hb h).hom.curve = (commonCoefficientCurveIso a b h).hom := by
  apply (cancel_epi (coefficientCurveOverIso (C := C) a).hom).mp
  have he := congrArg (fun f => f.curve) (commonCoefficientIso_recovery a b ha hb h)
  change _ ≫ _ = _ ≫ _ at he
  rw [coefficientIso_curve, coefficientIso_curve, parameterIso_curve] at he
  exact he.trans (commonCoefficientCurveIso_recovery _ _ _).symm

end FLT.Mazur.ArithmeticOneGonGeneralizedCurve
