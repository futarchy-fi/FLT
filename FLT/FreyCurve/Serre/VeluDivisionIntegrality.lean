/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.NTorsionRoots
public import FLT.FreyCurve.Serre.Velu
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Integral torsion abscissae away from the torsion order

For odd n, the division polynomial has leading coefficient n. When n is a
unit in the coefficient ring, normalizing that polynomial gives a monic
relation for every nonzero n-torsion abscissa. This needs no completion.
-/

@[expose] public section

namespace WeierstrassCurve.Velu

open Polynomial

variable {R K : Type*} [CommRing R] [Nontrivial R] [Field K] [Algebra R K]
variable [DecidableEq K] (W : WeierstrassCurve R) {n : ℕ}

/-- A unit odd torsion order supplies a monic equation for the affine x-coordinate. -/
theorem affine_torsion_x_isIntegral (hn : Odd n) (hu : IsUnit (n : R))
    {x y : K} (h : (W.map (algebraMap R K)).toAffine.Nonsingular x y)
    (hP : n • Affine.Point.some x y h = 0) : IsIntegral R x := by
  have hr := ((W.map (algebraMap R K)).isRoot_preΨ_iff_nsmul_eq_zero h hn).mpr hP
  have heval : aeval x (W.preΨ n) = 0 := by
    simpa only [map_preΨ, Polynomial.IsRoot, eval_map, aeval_def] using hr
  have hlead : (W.preΨ n).leadingCoeff = (n : R) := by
    rw [W.leadingCoeff_preΨ (by simpa only [Int.cast_natCast] using hu.ne_zero)]
    simp only [Int.even_coe_nat, (Nat.not_even_iff_odd.mpr hn), ↓reduceIte, Int.cast_natCast]
  obtain ⟨u, hu⟩ := hu
  refine ⟨C (↑u⁻¹ : R) * W.preΨ n, monic_C_mul_of_mul_leadingCoeff_eq_one ?_, ?_⟩
  · rw [hlead, ← hu]
    simp
  · change aeval x (C (↑u⁻¹ : R) * W.preΨ n) = 0
    rw [map_mul, heval, mul_zero]

/-- Any point on an integral model killed by a unit odd integer has integral abscissa. -/
theorem torsion_xCoord_isIntegral (E : WeierstrassCurve K)
    (hW : W.map (algebraMap R K) = E) (hn : Odd n) (hu : IsUnit (n : R))
    (P : E.toAffine.Point) (hP : n • P = 0) : IsIntegral R (xCoord P) := by
  subst E
  cases P with
  | zero => exact isIntegral_zero
  | some x y h => exact affine_torsion_x_isIntegral W hn hu h hP

end WeierstrassCurve.Velu
