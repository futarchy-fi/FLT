/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.Multiplication
public import FLT.EllipticCurve.Infinity
/-!
# Multiplication at infinity

The division-polynomial formula for the multiplied x-coordinate gives its
pole order at infinity. When n is nonzero in the ground field, the numerator
and denominator degrees differ by one, so that pole order remains two.
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
