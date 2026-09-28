/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.ModelGalois
public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Aut

/-!
# The sign ambiguity of Weierstrass model transport

When the fourth and sixth invariants are nonzero, any two changes of coordinates
between the same models induce point-group isomorphisms differing by a sign.
-/

@[expose] public section

namespace WeierstrassCurve.Affine.Point

variable {K : Type*} [Field K] [DecidableEq K]

/-- Composing a model change with the negation automorphism negates its point map. -/
theorem equivVariableChange_mul_neg (V W : WeierstrassCurve K) [V.IsElliptic]
    (C : VariableChange K) (hC : C • V = W)
    (hD : (C * V.negVariableChange) • V = W) (P : W.toAffine.Point) :
    equivVariableChange V (C * V.negVariableChange) (equivOfEq hD.symm P) =
      -equivVariableChange V C (equivOfEq hC.symm P) := by
  cases P with
  | zero => simp only [← zero_def, AddEquiv.map_zero, neg_zero]
  | some x y h =>
    erw [equivOfEq_some, equivVariableChange_some, equivOfEq_some,
      equivVariableChange_some, neg_some, some.injEq]
    constructor <;> simp [VariableChange.mul_def, negVariableChange, negY]
    ring

/-- Two isomorphisms from a model with no extra automorphisms differ by one uniform sign. -/
theorem exists_sign_modelEquiv (V W : WeierstrassCurve K) [V.IsElliptic]
    (h4 : V.c₄ ≠ 0) (h6 : V.c₆ ≠ 0) (C D : VariableChange K)
    (hC : C • V = W) (hD : D • V = W) :
    ∃ ε : ℤˣ, ∀ P : V.toAffine.Point,
      equivOfEq hC ((equivVariableChange V C).symm P) =
        (ε : ℤ) • equivOfEq hD ((equivVariableChange V D).symm P) := by
  have haut : (C⁻¹ * D) • V = V := by
    rw [mul_smul, hD, ← hC, inv_smul_smul]
  rcases V.eq_one_or_eq_negVariableChange_of_smul_eq_of_c₄_ne_zero h4 h6 haut with hid | hneg
  · have hDC : D = C := (inv_mul_eq_one.mp hid).symm
    subst D
    exact ⟨1, fun P ↦ by simp⟩
  · have hDC : D = C * V.negVariableChange := by
      rw [← hneg, mul_inv_cancel_left]
    subst D
    let eC := (equivOfEq hC.symm).trans (equivVariableChange V C)
    let eD := (equivOfEq hD.symm).trans (equivVariableChange V (C * V.negVariableChange))
    have he : ∀ Q, eD Q = -eC Q := equivVariableChange_mul_neg V W C hC hD
    have hinv : ∀ {A B : WeierstrassCurve K} (h : A = B) (Q : A.toAffine.Point),
        equivOfEq h Q = (equivOfEq h.symm).symm Q := by
      intro A B h Q
      subst B
      rfl
    refine ⟨-1, fun P ↦ ?_⟩
    simp only [Units.val_neg, Units.val_one, neg_one_zsmul, hinv]
    change eC.symm P = -eD.symm P
    apply eD.injective
    rw [he, eC.apply_symm_apply, map_neg, eD.apply_symm_apply]

end WeierstrassCurve.Affine.Point
