/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.Multiplication
public import FLT.EllipticCurve.Infinity
public import Mathlib.RingTheory.Valuation.IsTrivialOn
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
/-!
# Multiplication at infinity

The division-polynomial formula for the multiplied x-coordinate gives its
pole order at infinity. When n is nonzero in the ground field, the numerator
and denominator degrees differ by one, so that pole order remains two.
The Weierstrass equation then forces pole order three
for y. These coordinate orders determine the valuation on all rational functions.
-/

@[expose] public section

open Polynomial WeierstrassCurve
open scoped Polynomial.Bivariate WeierstrassCurve.Affine
namespace WeierstrassCurve
variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F)
/-- The affine multiplication formula, with denominators cleared, follows
from the Jacobian division-polynomial representative. -/
theorem x_mul_ΨSq_eq_Φ_of_nsmul_eq_some {x y u v : F}
    (h : E.toAffine.Nonsingular x y) (h' : E.toAffine.Nonsingular u v) (n : ℕ)
    (he : n • Affine.Point.some x y h = Affine.Point.some u v h') :
    u * (E.ΨSq n).eval x = (E.Φ n).eval x := by
  have hj : (n : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some x y h) =
      Jacobian.Point.fromAffine (Affine.Point.some u v h') := by
    have hh := congrArg (Jacobian.Point.toAffineAddEquiv E.toJacobian).symm he
    simpa only [map_nsmul, natCast_zsmul, Jacobian.Point.toAffineAddEquiv_symm_apply] using hh
  have hh := E.zsmul_eq_smulEval h (n : ℤ)
  rw [hj, Jacobian.Point.fromAffine_some] at hh
  have hx := Jacobian.X_eq_of_equiv (Quotient.exact hh)
  simpa [smulEval, ← E.eval_ΨSq h.1 n, ← E.eval_Φ h.1 n] using hx
end WeierstrassCurve
namespace WeierstrassCurve.Affine.FunctionField
variable {F : Type*} [Field F] (W : Affine F)
variable [W.IsElliptic] [IsAlgClosed F]
/-- Multiplication pullback of x is the division-polynomial quotient Φₙ/Ψₙ². -/
theorem nsmulPullback_genericX_eq (n : ℕ) (hn : n ≠ 0) :
    nsmulPullback W n hn (genericX W) =
      aeval (genericX W) (W.Φ n) / aeval (genericX W) (W.ΨSq n) := by
  classical
  let : (W⁄W.FunctionField).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F W.FunctionField)).IsElliptic
  have he := (W⁄W.FunctionField).x_mul_ΨSq_eq_Φ_of_nsmul_eq_some
    ((W⁄W.FunctionField).equation_iff_nonsingular.mp (generic_equation W))
    (multiplied_nonsingular W n hn) n (multiplied_point W n hn).symm
  change multipliedX W n hn *
      ((W.map (algebraMap F W.FunctionField)).ΨSq n).eval (genericX W) =
      ((W.map (algebraMap F W.FunctionField)).Φ n).eval (genericX W) at he
  simp only [map_ΨSq, map_Φ, eval_map, ← aeval_def] at he
  rw [nsmulPullback_genericX]
  apply (eq_div_iff ?_).mpr he
  simpa only [map_zero] using (transcendental_iff_injective.mp (genericX_transcendental W)).ne
    (W.ΨSq_ne_zero_of_isElliptic (Int.natCast_ne_zero.mpr hn))

omit [W.IsElliptic] [IsAlgClosed F] in
/-- A polynomial in the generic x-coordinate has pole order twice its degree. -/
theorem infinityValuation_aeval_genericX {p : F[X]} (hp : p ≠ 0) :
    infinityValuation W (aeval (genericX W) p) =
      WithZero.exp (2 * (p.natDegree : ℤ)) := by
  rw [aeval_genericX, infinityValuation_algebraMap]
  exact CoordinateRing.infinityValuation_polynomial hp

/-- Multiplication by n prime to the characteristic preserves the pole order of x. -/
theorem infinityValuation_nsmulPullback_genericX {n : ℕ} (hn : n ≠ 0)
    (hchar : (n : F) ≠ 0) :
    infinityValuation W (nsmulPullback W n hn (genericX W)) = WithZero.exp (2 : ℤ) := by
  rw [nsmulPullback_genericX_eq, map_div₀,
    infinityValuation_aeval_genericX W (W.Φ_ne_zero n),
    infinityValuation_aeval_genericX W
      (W.ΨSq_ne_zero_of_isElliptic (Int.natCast_ne_zero.mpr hn)),
    W.natDegree_Φ, W.natDegree_ΨSq (by simpa using hchar), ← WithZero.exp_sub]
  congr 1
  simp only [Int.natAbs_natCast]
  rw [Nat.cast_sub (by exact Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hn)), Nat.cast_one]
  ring
end WeierstrassCurve.Affine.FunctionField

namespace WeierstrassCurve.Affine.FunctionField
open WithZero

variable {F : Type*} [Field F] (W : Affine F)
/-- The valuation at infinity is trivial on nonzero ground-field constants. -/
instance infinityValuation_isTrivialOn : (infinityValuation W).IsTrivialOn F where
  eq_one c hc := by
    simpa using infinityValuation_aeval_genericX W (p := C c) (C_ne_zero.mpr hc)

/-- For a point satisfying the Weierstrass equation in the function field,
a pole of order two in x forces a pole of order three in y. -/
theorem infinityValuation_y_of_equation {x y : W.FunctionField}
    (he : (W⁄W.FunctionField).Equation x y)
    (hx : infinityValuation W x = exp (2 : ℤ)) :
    infinityValuation W y = exp (3 : ℤ) := by
  let v := infinityValuation W
  let b := algebraMap F W.FunctionField W.a₁ * x + algebraMap F W.FunctionField W.a₃
  let p : F[X] := C 1 * X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆
  have hp : p.natDegree = 3 := natDegree_cubic one_ne_zero
  have hp0 : p ≠ 0 := by intro hz; simp [hz] at hp
  have hxpos : 1 < v x := by rw [hx]; exact exp_lt_exp.mpr (by norm_num)
  have hpv : v (aeval x p) = exp (6 : ℤ) := by
    rw [valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X x hxpos hp0,
      hx, hp, ← exp_nsmul]
    rfl
  have hb : v b ≤ exp (2 : ℤ) := by
    apply (v.map_add _ _).trans
    apply max_le
    · rw [map_mul]
      calc
        v (algebraMap F W.FunctionField W.a₁) * v x ≤ 1 * v x := by
          gcongr
          exact Valuation.IsTrivialOn.valuation_algebraMap_le_one _ _
        _ = exp (2 : ℤ) := by rw [one_mul, hx]
    · exact (Valuation.IsTrivialOn.valuation_algebraMap_le_one v W.a₃).trans
        (by exact exp_le_exp.mpr (by norm_num))
  have heq : y ^ 2 + b * y = aeval x p := by
    rw [equation_iff'] at he
    change y ^ 2 + algebraMap F W.FunctionField W.a₁ * x * y +
      algebraMap F W.FunctionField W.a₃ * y -
      (x ^ 3 + algebraMap F W.FunctionField W.a₂ * x ^ 2 +
        algebraMap F W.FunctionField W.a₄ * x + algebraMap F W.FunctionField W.a₆) = 0 at he
    simpa [p, b, add_mul, add_assoc] using sub_eq_zero.mp he
  have hy0 : y ≠ 0 := by
    intro hz
    rw [hz, zero_pow two_ne_zero, mul_zero, add_zero] at heq
    rw [← heq, map_zero] at hpv
    exact exp_ne_zero hpv.symm
  have hyv0 : v y ≠ 0 := (_root_.map_ne_zero v).mpr hy0
  let k : ℤ := log (v y)
  have hyv : v y = exp k := (exp_log hyv0).symm
  have hk : 3 ≤ k := by
    have hh : exp (6 : ℤ) ≤ max (exp (2 * k)) (exp (2 + k)) := by
      rw [← hpv, ← heq]
      apply (v.map_add _ _).trans
      rw [map_pow, map_mul, hyv, ← exp_nsmul, nsmul_eq_mul]
      apply max_le_max le_rfl
      simpa only [exp_add, mul_comm] using mul_le_mul_right hb (exp k)
    rw [le_max_iff, exp_le_exp, exp_le_exp] at hh
    omega
  have hlt : v (b * y) < v (y ^ 2) := by
    rw [map_mul, map_pow, hyv, ← exp_nsmul, nsmul_eq_mul]
    calc
      v b * exp k ≤ exp (2 : ℤ) * exp k := by
        simpa only [mul_comm] using mul_le_mul_right hb (exp k)
      _ < exp (2 * k) := by rw [← exp_add, exp_lt_exp]; omega
  have hh := v.map_add_eq_of_lt_left hlt
  rw [heq, hpv, map_pow, hyv, ← exp_nsmul, exp_inj, nsmul_eq_mul] at hh
  rw [hyv, show k = 3 by omega]
/-- An algebra endomorphism preserving the pole orders of x and y preserves
the infinity valuation of every rational function. Parity separates the two basis terms. -/
theorem infinityValuation_apply_eq_of_coordinates
    (φ : W.FunctionField →ₐ[F] W.FunctionField)
    (hx : infinityValuation W (φ (genericX W)) = exp (2 : ℤ))
    (hy : infinityValuation W (φ (genericY W)) = exp (3 : ℤ)) (f : W.FunctionField) :
    infinityValuation W (φ f) = infinityValuation W f := by
  let v := infinityValuation W
  change v (φ (genericX W)) = exp (2 : ℤ) at hx
  change v (φ (genericY W)) = exp (3 : ℤ) at hy
  have hx0 : v (genericX W) = exp (2 : ℤ) := by
    simpa using infinityValuation_aeval_genericX W (p := X) X_ne_zero
  have hy0 : v (genericY W) = exp (3 : ℤ) :=
    infinityValuation_y_of_equation W (generic_equation W) hx0
  have hp (p : F[X]) : v (φ (aeval (genericX W) p)) = v (aeval (genericX W) p) := by
    by_cases hp0 : p = 0
    · simp [hp0]
    rw [← aeval_algHom_apply,
      valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X _
        (by rw [hx]; exact exp_lt_exp.mpr (by norm_num)) hp0,
      valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X _
        (by rw [hx0]; exact exp_lt_exp.mpr (by norm_num)) hp0, hx, hx0]
  have hform (p q : F[X]) :
      algebraMap W.CoordinateRing W.FunctionField (p • 1 + q • CoordinateRing.mk W Y) =
        aeval (genericX W) p + aeval (genericX W) q * genericY W := by
    simp only [map_add, Algebra.smul_def, map_mul, mul_one, aeval_genericX]
    rfl
  have hreg (a : W.CoordinateRing) :
      v (φ (algebraMap W.CoordinateRing W.FunctionField a)) =
        v (algebraMap W.CoordinateRing W.FunctionField a) := by
    obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq a
    rw [hform]
    by_cases hp0 : p = 0
    · simp [hp0, map_mul, hp, hy, hy0]
    by_cases hq0 : q = 0
    · simp [hq0, hp]
    have hdist : v (aeval (genericX W) p) ≠
        v (aeval (genericX W) q * genericY W) := by
      rw [map_mul, hy0, infinityValuation_aeval_genericX W hp0,
        infinityValuation_aeval_genericX W hq0, ← exp_add, ne_eq, exp_inj]
      omega
    have hdist' : v (φ (aeval (genericX W) p)) ≠
        v (φ (aeval (genericX W) q * genericY W)) := by
      simpa only [map_mul, hp, hy, hy0] using hdist
    rw [map_add φ, v.map_add_of_distinct_val hdist', v.map_add_of_distinct_val hdist,
      hp, map_mul φ, map_mul v, hp, hy, map_mul v, hy0]
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective W.CoordinateRing f
  rw [map_div₀ φ, map_div₀ v, map_div₀ v, hreg, hreg]

variable [W.IsElliptic] [IsAlgClosed F]
/-- Multiplication by an invertible n preserves the pole order three of y. -/
theorem infinityValuation_nsmulPullback_genericY {n : ℕ} (hn : n ≠ 0)
    (hchar : (n : F) ≠ 0) :
    infinityValuation W (nsmulPullback W n hn (genericY W)) = exp (3 : ℤ) := by
  apply infinityValuation_y_of_equation W (x := nsmulPullback W n hn (genericX W))
  · rw [nsmulPullback_genericX, nsmulPullback_genericY]
    exact (multiplied_nonsingular W n hn).1
  · exact infinityValuation_nsmulPullback_genericX W hn hchar

/-- Multiplication by an invertible n preserves the valuation at infinity
on the entire function field. -/
theorem infinityValuation_nsmulPullback {n : ℕ} (hn : n ≠ 0)
    (hchar : (n : F) ≠ 0) (f : W.FunctionField) :
    infinityValuation W (nsmulPullback W n hn f) = infinityValuation W f :=
  infinityValuation_apply_eq_of_coordinates W (nsmulPullback W n hn)
    (infinityValuation_nsmulPullback_genericX W hn hchar)
    (infinityValuation_nsmulPullback_genericY W hn hchar) f

end WeierstrassCurve.Affine.FunctionField
