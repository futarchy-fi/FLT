/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.NTorsionFinite
public import FLT.Mathlib.RingTheory.Valuation.RootLifting

/-!
# Lifting torsion points from the special fiber

The division-polynomial criterion characterizes the nonzero torsion points in
arbitrary characteristic, including torsion at the residue characteristic.
Over an algebraically closed valued field, every nonzero special-fiber torsion
point lifts to a generic-fiber torsion point with integral coordinates. This
uses root lifting without a simple-root assumption on the division polynomial.

These coordinate lifts do not yet construct the reduction homomorphism on all
points, including points with nonintegral coordinates.
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

open Polynomial IsLocalRing
namespace WeierstrassCurve

variable {K : Type*} [Field K] [IsAlgClosed K] (A : ValuationSubring K)
  (W : WeierstrassCurve A)

/-- Lift a special-fiber affine point while prescribing any lift of its x-coordinate. -/
theorem exists_equation_lifting (x : A) (yb : ResidueField A)
    (h : (W.map (residue A)).toAffine.Equation (residue A x) yb) :
    ∃ y : A, W.toAffine.Equation x y ∧ residue A y = yb := by
  let f := W.toAffine.polynomial.map (evalRingHom x)
  have hmonic : f.Monic := Affine.monic_polynomial.map _
  have hroot : (f.map (residue A)).IsRoot yb := by
    simpa [f, Polynomial.IsRoot, eval_map, eval₂_evalRingHom,
      Affine.polynomial, Affine.equation_iff', add_mul, ← add_assoc] using h
  obtain ⟨y, hy, hyb⟩ := A.exists_root_lifting f (hmonic.map _).ne_zero yb hroot
  exact ⟨y, by simpa [f, IsRoot, eval_map, eval₂_evalRingHom, Affine.Equation] using hy, hyb⟩

/-- Nonzero special-fiber torsion points lift to integral generic-fiber torsion points. -/
theorem exists_torsion_lifting [DecidableEq K] [DecidableEq (ResidueField A)]
    [(W.map (algebraMap A K)).IsElliptic] [(W.map (residue A)).IsElliptic]
    {xb yb : ResidueField A} (h : (W.map (residue A)).toAffine.Nonsingular xb yb)
    {n : ℕ} (hn : 0 < n) (ht : n • Affine.Point.some xb yb h = 0) :
    ∃ (x y : A) (hxy : (W.map (algebraMap A K)).toAffine.Nonsingular
      (algebraMap A K x) (algebraMap A K y)),
      residue A x = xb ∧ residue A y = yb ∧
      n • Affine.Point.some _ _ hxy = 0 := by
  have hp : (W.ΨSq n).map (residue A) ≠ 0 := by
    rw [← map_ΨSq]
    exact (W.map (residue A)).ΨSq_ne_zero_of_isElliptic (by exact_mod_cast hn.ne')
  have hxb : ((W.ΨSq n).map (residue A)).IsRoot xb := by
    rw [← map_ΨSq]
    exact (W.map (residue A)).isRoot_ΨSq_of_nsmul_eq_zero h n ht
  obtain ⟨x, hx, hxr⟩ := A.exists_root_lifting (W.ΨSq n) hp xb hxb
  obtain ⟨y, hy, hyr⟩ := exists_equation_lifting A W x yb (hxr ▸ h.1)
  have hxy : (W.map (algebraMap A K)).toAffine.Nonsingular
      (algebraMap A K x) (algebraMap A K y) :=
    Affine.equation_iff_nonsingular.mp (hy.map (algebraMap A K))
  refine ⟨x, y, hxy, hxr, hyr, ?_⟩
  apply (W.map (algebraMap A K)).nsmul_eq_zero_of_isRoot_ΨSq hxy n
  rw [map_ΨSq]
  exact hx.map
end WeierstrassCurve
