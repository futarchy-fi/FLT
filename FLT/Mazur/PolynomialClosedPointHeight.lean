/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleDimGe
public import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Heights of closed points of affine space

Every maximal ideal of a polynomial algebra over a field has height equal
to the number of variables. This detects the dimension of smooth charts
through their finite type flat coordinate maps.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FCurve
set_option backward.isDefEq.respectTransparency false

/-- Every closed point of finite dimensional affine space has the expected height. -/
theorem mvPolynomial_maximal_height (K : Type*) [Field K]
    (ι : Type*) [Finite ι] (M : Ideal (MvPolynomial ι K)) [M.IsMaximal] :
    M.height = Nat.card ι := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e H =>
    let e' := (MvPolynomial.renameEquiv K e).toRingEquiv
    let N := M.comap e'
    let _ : N.IsMaximal := Ideal.comap_isMaximal_of_surjective e' e'.surjective
    rw [← e'.height_comap M, H N, Nat.card_congr e]
  | h_empty =>
    let e := (MvPolynomial.isEmptyAlgEquiv K PEmpty).toRingEquiv
    let N := M.map e
    let _ : N.IsMaximal := inferInstanceAs (M.map e).IsMaximal
    have hN : N = ⊥ := Ideal.eq_bot_of_prime N
    rw [← e.height_map M]
    change N.height = _
    rw [hN]
    simp
  | @h_option α _ IH =>
    let e := (MvPolynomial.optionEquivLeft K α).toRingEquiv
    let N := M.map e
    let _ : N.IsMaximal := inferInstanceAs (M.map e).IsMaximal
    let _ : (N.under (MvPolynomial α K)).IsMaximal :=
      maximalUnderOfFiniteType (MvPolynomial α K) _ N
    rw [← e.height_map M,
      Polynomial.height_eq_height_add_one (N.under (MvPolynomial α K)) N, IH]
    simp

end FLT.Mazur.FCurve
