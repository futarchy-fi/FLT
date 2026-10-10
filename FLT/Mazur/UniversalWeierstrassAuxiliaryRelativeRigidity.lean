/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryCoordinateInverse
public import FLT.Mazur.UniversalWeierstrassAuxiliaryCoordinateUnits
public import FLT.Mazur.WeierstrassVariableChangeFrame

/-!
# Relative coordinate rigidity from the actual auxiliary marking

After any ring-valued pullback of the original auxiliary coordinate functions,
an admissible change of variables fixing the marked coordinates is the
identity. The unit differences and inverse formulas have been proved on the
actual auxiliary scheme, so this includes nonreduced coefficient rings.

To apply this to an arbitrary origin-preserving scheme automorphism, one still
needs to construct its admissible coordinate change and identify its action
on these coordinates.
-/

@[expose] public noncomputable section

open WeierstrassCurve

namespace FLT.Mazur.UniversalWeierstrass

/-- No nontrivial admissible coordinate change fixes the actual pulled-back marking. -/
theorem auxiliary_coordinate_rigidity_after_pullback {R : Type*} [CommRing R]
    (g : AuxiliarySectionRing →+* R) (C : VariableChange R)
    (hf : ∀ (a : Labels 4) (ha : a ≠ 1),
      (C.u : R) ^ 2 * g (auxiliaryCoordinate a ha 0) + C.r =
        g (auxiliaryCoordinate a ha 0) ∧
      (C.u : R) ^ 3 * g (auxiliaryCoordinate a ha 1) +
        (C.u : R) ^ 2 * C.s * g (auxiliaryCoordinate a ha 0) + C.t =
          g (auxiliaryCoordinate a ha 1)) : C = 1 := by
  let a : Labels 4 := Multiplicative.ofAdd (1, 0)
  let b : Labels 4 := Multiplicative.ofAdd (0, 1)
  have ha : a ≠ 1 := by decide
  have hb : b ≠ 1 := by decide
  have hab : a ≠ b := by decide
  have hab' : a ≠ b⁻¹ := by decide
  have han : a ≠ a⁻¹ := by decide
  have hx : IsUnit (g (auxiliaryCoordinate a ha 0) - g (auxiliaryCoordinate b hb 0)) := by
    simpa only [map_sub] using (auxiliaryCoordinate_x_sub_isUnit a b ha hb hab hab').map g
  have hy : IsUnit (g (auxiliaryCoordinate a ha 1) -
      g (auxiliarySectionEquation.toAffine.negY
        (auxiliaryCoordinate a ha 0) (auxiliaryCoordinate a ha 1))) := by
    simpa only [map_sub] using (auxiliaryCoordinate_y_sub_neg_isUnit a ha han).map g
  have hn := (hf a⁻¹ (inv_ne_one.mpr ha)).2
  rw [auxiliaryCoordinate_inverse_x a ha, auxiliaryCoordinate_inverse_y a ha] at hn
  exact WeierstrassVariableChangeFrame.eq_one C _ _ _ _ _ hx hy
    (hf a ha).1 (hf b hb).1 (hf a ha).2 hn (hf b hb).2

end FLT.Mazur.UniversalWeierstrass
