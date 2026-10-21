/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonCommonCoefficientIso

/-!
# Three-presentation coherence of full arithmetic coefficient comparisons

The common-ring comparison satisfies the identity and composition laws as
an isomorphism of full generalized curves, including the entire group action.
Only equality of the actual smoothing parameters in the common ring is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonGeneralizedCurve
open OneGonSmoothing CharacterSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A D] [Algebra B D] [Algebra C D]
  (a : A) (b : B) (c : C)
  (ha : IsUnit (1 + 432 * a)) (hb : IsUnit (1 + 432 * b))
  (hc : IsUnit (1 + 432 * c))

/-- Comparison of an arithmetic presentation with itself is the full identity. -/
theorem commonCoefficientIso_refl :
    commonCoefficientIso a a ha ha (rfl : algebraMap A D a = algebraMap A D a) =
      Iso.refl ((curve a ha).baseChange (baseMap A D)) := by
  apply Iso.ext
  rw [commonCoefficientIso_def, parameterIso_def]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, Category.id_comp,
    Iso.inv_hom_id]

/-- Three full arithmetic presentations satisfy the cocycle equation over the common ring. -/
@[reassoc] theorem commonCoefficientIso_trans
    (hab : algebraMap A D a = algebraMap B D b)
    (hbc : algebraMap B D b = algebraMap C D c) :
    (commonCoefficientIso a b ha hb hab).hom ≫ (commonCoefficientIso b c hb hc hbc).hom =
      (commonCoefficientIso a c ha hc (hab.trans hbc)).hom := by
  apply (cancel_epi (coefficientIso (S := D) a ha).hom).mp
  rw [← Category.assoc, commonCoefficientIso_recovery, Category.assoc,
    commonCoefficientIso_recovery, ← Category.assoc, parameterIso_trans,
    commonCoefficientIso_recovery]

/-- Reversing the two presentations gives the inverse full arithmetic comparison. -/
theorem commonCoefficientIso_symm (hab : algebraMap A D a = algebraMap B D b) :
    (commonCoefficientIso a b ha hb hab).symm =
      commonCoefficientIso b a hb ha hab.symm := by
  apply Iso.ext
  apply (cancel_epi (commonCoefficientIso a b ha hb hab).hom).mp
  rw [Iso.symm_hom, Iso.hom_inv_id, commonCoefficientIso_trans,
    commonCoefficientIso_refl]
  rfl

end FLT.Mazur.ArithmeticOneGonGeneralizedCurve
