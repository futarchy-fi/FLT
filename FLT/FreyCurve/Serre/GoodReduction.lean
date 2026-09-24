/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.NTorsionFinite
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.RingTheory.Valuation.Integral

/-!
# Integral coordinates of prime-to-residue-characteristic torsion

Division polynomials force the coordinates of nonzero torsion points into an
integrally closed coefficient ring when the torsion order is a unit.
-/

@[expose] public section

open Polynomial

namespace WeierstrassCurve

/-- The x-coordinate of a nonzero torsion point belongs to the integrally closed
coefficient ring if its order is invertible there. -/
theorem exists_x_of_nsmul_eq_zero {R K : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] [DecidableEq K]
    (W : WeierstrassCurve R) {n : ℕ} (hn : IsUnit (n : R)) {x y : K}
    (h : (W.map (algebraMap R K)).toAffine.Nonsingular x y)
    (hP : n • Affine.Point.some x y h = 0) :
    ∃ r : R, algebraMap R K r = x := by
  have hroot := (W.map (algebraMap R K)).isRoot_ΨSq_of_nsmul_eq_zero h n hP
  have heval : aeval x (W.ΨSq n) = 0 := by
    simpa only [WeierstrassCurve.map_ΨSq, Polynomial.IsRoot, eval_map, aeval_def] using hroot
  obtain ⟨u, hu⟩ := hn
  have hlead : (W.ΨSq (n : ℤ)).leadingCoeff = (n : R) ^ 2 := by
    simpa only [Int.cast_natCast] using
      W.leadingCoeff_ΨSq (n := (n : ℤ)) (by simpa only [Int.cast_natCast, ← hu] using u.ne_zero)
  have hint := isIntegral_leadingCoeff_smul (W.ΨSq n) x heval
  rw [hlead, ← hu] at hint
  have hint' := hint.smul (↑((u ^ 2)⁻¹) : R)
  simp only [smul_smul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_smul] at hint'
  exact IsIntegrallyClosed.isIntegral_iff.mp hint'

/-- An affine point with integral x-coordinate also has integral y-coordinate
over an integrally closed coefficient ring. -/
theorem exists_y_of_equation {R K : Type*} [CommRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve R) (x : R) {y : K}
    (h : (W.map (algebraMap R K)).toAffine.Equation (algebraMap R K x) y) :
    ∃ r : R, algebraMap R K r = y := by
  apply IsIntegrallyClosed.isIntegral_iff.mp
  refine ⟨X ^ 2 + C (W.a₁ * x + W.a₃) * X -
    C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆), by monicity!, ?_⟩
  have he := (Affine.equation_iff _ _).mp h
  simp only [WeierstrassCurve.map, WeierstrassCurve.toAffine] at he
  simpa [map_add, map_mul, map_pow, add_mul, sub_eq_zero, add_assoc] using he

end WeierstrassCurve
