/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassFourMarkingFrame
public import FLT.Mazur.WeierstrassVariableChangeFrame

/-!
# Faithful level-four markings rigidify coordinate automorphisms

An admissible automorphism of a Weierstrass equation over a field that fixes a
faithful level-four marking has all four coefficients equal to those of the
identity. This proves equality of the coordinate transformation, not merely
its restriction to the finite torsion group.
-/

@[expose] public noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine

namespace FLT.Mazur.WeierstrassFourMarkingRigidity

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic]
  (C : VariableChange K) (hC : C • W = W)

/-- The actual action on points of a change of variables preserving the equation. -/
def action : W.toAffine.Point ≃+ W.toAffine.Point :=
  (Point.equivOfEq hC.symm).trans (Point.equivVariableChange W C)

/-- Fixing an affine point gives the two original coordinate equations. -/
theorem fixed_coordinates {x y : K} (h : W.toAffine.Nonsingular x y)
    (hf : action W C hC (.some x y h) = .some x y h) :
    (C.u : K) ^ 2 * x + C.r = x ∧
      (C.u : K) ^ 3 * y + (C.u : K) ^ 2 * C.s * x + C.t = y := by
  simpa only [action, AddEquiv.trans_apply, Point.equivOfEq_some,
    Point.equivVariableChange_some, Point.some.injEq] using hf

/-- A faithful four-marking kills every admissible coordinate automorphism of the curve. -/
theorem eq_one (φ : (ZMod 4 × ZMod 4) →+ W.toAffine.Point)
    (hφ : Function.Injective φ) (hf : ∀ a, action W C hC (φ a) = φ a) : C = 1 := by
  obtain ⟨x, y, z, w, hP, hQ, hp, hq, hxz, hyy⟩ :=
    WeierstrassFourMarkingFrame.exists_frame W φ hφ
  have hpfix : action W C hC (.some x y hP) = .some x y hP := by
    simpa only [hp] using hf (1, 0)
  have hqfix : action W C hC (.some z w hQ) = .some z w hQ := by
    simpa only [hq] using hf (0, 1)
  have hnfix : action W C hC (-Point.some x y hP) = -Point.some x y hP := by
    rw [map_neg, hpfix]
  obtain ⟨hx, hy⟩ := fixed_coordinates W C hC hP hpfix
  obtain ⟨hz, hw⟩ := fixed_coordinates W C hC hQ hqfix
  have hyn := (fixed_coordinates W C hC ((nonsingular_neg ..).mpr hP) hnfix).2
  exact WeierstrassVariableChangeFrame.eq_one C x y (W.toAffine.negY x y) z w
    (sub_ne_zero.mpr hxz).isUnit (sub_ne_zero.mpr hyy).isUnit hx hz hy hyn hw

/-- A coordinate automorphism fixing the marking fixes every point of the original curve. -/
theorem action_eq_refl (φ : (ZMod 4 × ZMod 4) →+ W.toAffine.Point)
    (hφ : Function.Injective φ) (hf : ∀ a, action W C hC (φ a) = φ a) :
    action W C hC = AddEquiv.refl _ := by
  have hc := eq_one W C hC φ hφ hf
  subst C
  ext P
  cases P with
  | zero => exact map_zero _
  | some x y h =>
    simp only [action, AddEquiv.trans_apply, Point.equivOfEq_some,
      Point.equivVariableChange_some, VariableChange.one_def, Units.val_one,
      one_pow, one_mul, zero_mul, add_zero, AddEquiv.refl_apply]

end FLT.Mazur.WeierstrassFourMarkingRigidity
