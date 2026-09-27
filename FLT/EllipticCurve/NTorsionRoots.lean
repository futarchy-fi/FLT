/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.NTorsionFinite

/-!
# Division-polynomial roots and torsion points

The multiplication formula identifies the roots of the square division polynomial
with the x-coordinates of nonzero torsion points. The numerator and denominator
of the multiplication formula have no common root.
-/

@[expose] public section

open Polynomial

namespace WeierstrassCurve

variable {k : Type*} [Field k] (E : WeierstrassCurve k)

/-- A nonsingular affine point is killed by `n` exactly when its x-coordinate
is a root of the square division polynomial. -/
theorem isRoot_ΨSq_iff_nsmul_eq_zero [DecidableEq k] {x y : k}
    (h : E.toAffine.Nonsingular x y) (n : ℕ) :
    (E.ΨSq n).IsRoot x ↔ n • Affine.Point.some x y h = 0 := by
  refine ⟨fun hx => ?_, E.isRoot_ΨSq_of_nsmul_eq_zero h n⟩
  have hψ : (E.ψ n).evalEval x y = 0 := by
    apply eq_zero_of_pow_eq_zero
    rw [← E.eval_ΨSq h.1 n]
    exact hx
  have hj : (n : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some x y h) = 0 := by
    apply Jacobian.Point.ext_iff.mpr
    rw [E.zsmul_eq_smulEval h n, Jacobian.Point.zero_point]
    exact Quotient.sound (Jacobian.equiv_zero_of_Z_eq_zero (E.nonsingular_smulEval h n)
      (by simpa [smulEval] using hψ))
  apply (Jacobian.Point.toAffineAddEquiv E).symm.injective
  simpa only [map_nsmul, map_zero, Jacobian.Point.toAffineAddEquiv_symm_apply,
    natCast_zsmul] using hj

/-- For odd `n`, the unsquared division polynomial detects nonzero torsion points. -/
theorem isRoot_preΨ_iff_nsmul_eq_zero [DecidableEq k] {x y : k}
    (h : E.toAffine.Nonsingular x y) {n : ℕ} (hn : Odd n) :
    (E.preΨ n).IsRoot x ↔ n • Affine.Point.some x y h = 0 := by
  rw [← E.isRoot_ΨSq_iff_nsmul_eq_zero h n]
  have he : ¬Even (n : ℤ) := by
    simpa only [Int.even_coe_nat] using (Nat.not_even_iff_odd.mpr hn)
  simp only [ΨSq, ite_eq_right he, mul_one, Polynomial.IsRoot, eval_pow]
  exact ⟨fun hx => by rw [hx, zero_pow two_ne_zero], eq_zero_of_pow_eq_zero⟩

/-- At a root of the square division polynomial, the multiplication numerator
does not vanish on a nonsingular affine point. -/
theorem eval_Φ_ne_zero_of_isRoot_ΨSq {x y : k} (h : E.toAffine.Nonsingular x y)
    (n : ℤ) (hx : (E.ΨSq n).IsRoot x) : (E.Φ n).eval x ≠ 0 := by
  have hψ : (E.ψ n).evalEval x y = 0 := by
    apply eq_zero_of_pow_eq_zero
    rw [← E.eval_ΨSq h.1 n]
    exact hx
  have hu := Jacobian.isUnit_X_of_Z_eq_zero (E.nonsingular_smulEval h n)
    (by simpa [smulEval] using hψ)
  rw [E.eval_Φ h.1 n]
  simpa [smulEval] using hu.ne_zero

/-- The multiplication numerator and square division polynomial are coprime
on an elliptic curve, in every characteristic. -/
theorem isCoprime_Φ_ΨSq_of_isElliptic [E.IsElliptic] (n : ℤ) : IsCoprime (E.Φ n) (E.ΨSq n) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    k (AlgebraicClosure k) (E.Φ n) (E.ΨSq n)).mpr
  intro x
  let E' := E.map (algebraMap k (AlgebraicClosure k))
  by_cases hx : (E'.ΨSq n).IsRoot x
  · obtain ⟨y, hy⟩ := E'.exists_equation x
    have hns := E'.toAffine.equation_iff_nonsingular.mp hy
    left
    simpa only [E', map_Φ, eval_map_algebraMap] using
      E'.eval_Φ_ne_zero_of_isRoot_ΨSq hns n hx
  · right
    simpa only [E', map_ΨSq, Polynomial.IsRoot, eval_map_algebraMap] using hx

/-- An odd division polynomial and the two-division polynomial have no common
factor on an elliptic curve, since a nonzero point cannot have both odd order
and order dividing two. -/
theorem isCoprime_preΨ_ΨSq_two [E.IsElliptic] {n : ℕ} (hn : Odd n) :
    IsCoprime (E.preΨ n) (E.ΨSq 2) := by
  classical
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    k (AlgebraicClosure k) (E.preΨ n) (E.ΨSq 2)).mpr
  intro x
  let E' := E.map (algebraMap k (AlgebraicClosure k))
  by_cases hx : (E'.preΨ n).IsRoot x
  · right
    intro hx₂
    have hr₂ : (E'.ΨSq 2).IsRoot x := by
      simpa only [E', map_ΨSq, Polynomial.IsRoot, eval_map_algebraMap] using hx₂
    obtain ⟨y, hy⟩ := E'.exists_equation x
    have hns := E'.toAffine.equation_iff_nonsingular.mp hy
    have ht := (E'.isRoot_preΨ_iff_nsmul_eq_zero hns hn).mp hx
    have ht₂ := (E'.isRoot_ΨSq_iff_nsmul_eq_zero hns 2).mp hr₂
    obtain ⟨m, rfl⟩ := hn
    rw [add_nsmul, mul_nsmul, ht₂,
      smul_zero, one_nsmul, zero_add] at ht
    exact Affine.Point.some_ne_zero hns ht
  · left
    simpa only [E', map_preΨ, Polynomial.IsRoot, eval_map_algebraMap] using hx

end WeierstrassCurve
