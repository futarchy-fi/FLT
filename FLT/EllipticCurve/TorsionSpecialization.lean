/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.NTorsionFinite

/-!
# Lifting torsion points from the special fiber

The division-polynomial criterion characterizes the nonzero torsion points in
arbitrary characteristic, including torsion at the residue characteristic.
-/

@[expose] public section

open WeierstrassCurve
namespace WeierstrassCurve

variable {k : Type*} [Field k] [DecidableEq k] (E : WeierstrassCurve k)

/-- A point whose x-coordinate is a division-polynomial root is torsion. -/
theorem nsmul_eq_zero_of_isRoot_ΨSq {x y : k} (h : E.toAffine.Nonsingular x y)
    (n : ℕ) (hn : (E.ΨSq n).IsRoot x) : n • Affine.Point.some x y h = 0 := by
  have hψ : (E.ψ n).evalEval x y = 0 := by
    apply eq_zero_of_pow_eq_zero (n := 2)
    rw [← E.eval_ΨSq h.1 n]
    exact hn
  have hz : E.smulEval x y n 2 = 0 := by simpa [smulEval] using hψ
  have hj : (n : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some x y h) = 0 := by
    apply Jacobian.Point.ext
    rw [E.zsmul_eq_smulEval h n, Jacobian.Point.zero_point]
    exact Quotient.sound (Jacobian.equiv_zero_of_Z_eq_zero (E.nonsingular_smulEval h n) hz)
  apply (Jacobian.Point.toAffineAddEquiv E.toJacobian).symm.injective
  simpa only [map_nsmul, map_zero, natCast_zsmul,
    Jacobian.Point.toAffineAddEquiv_symm_apply] using hj

end WeierstrassCurve
