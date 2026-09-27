/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CoordinateRing
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Valuation.ExtendToLocalization

/-!
# The valuation at infinity on a Weierstrass function field

The degree of the polynomial norm is multiplicative and satisfies the maximum
inequality for sums. Exponentiation gives a valuation on the coordinate ring,
which extends to its fraction field. The sign convention is multiplicative:
values greater than one indicate poles.
-/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate
namespace WeierstrassCurve.Affine.CoordinateRing
variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F}
/-- The norm degree of a sum is at most the larger norm degree. -/
theorem degree_norm_add_le (f g : W.CoordinateRing) :
    (Algebra.norm F[X] (f + g)).degree ≤
      max (Algebra.norm F[X] f).degree (Algebra.norm F[X] g).degree := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq f
  obtain ⟨r, s, rfl⟩ := exists_smul_basis_eq g
  have he : (p • (1 : W.CoordinateRing) + q • mk W Y) + (r • 1 + s • mk W Y) =
      (p + r) • 1 + (q + s) • mk W Y := by module
  rw [he, degree_norm_smul_basis, degree_norm_smul_basis, degree_norm_smul_basis]
  apply max_le
  · calc
      2 • (p + r).degree ≤ 2 • max p.degree r.degree :=
        nsmul_le_nsmul_right (degree_add_le ..) 2
      _ = max (2 • p.degree) (2 • r.degree) := (nsmul_right_mono 2).map_max
      _ ≤ _ := max_le_max (le_max_left ..) (le_max_left ..)
  · calc
      2 • (q + s).degree + 3 ≤ 2 • max q.degree s.degree + 3 :=
        add_le_add (nsmul_le_nsmul_right (degree_add_le ..) 2) le_rfl
      _ = max (2 • q.degree + 3) (2 • s.degree + 3) := by
        rw [(nsmul_right_mono 2).map_max, max_add_add_right]
      _ ≤ _ := max_le_max (le_max_right ..) (le_max_right ..)

open WithZero in
/-- The norm-degree valuation on regular functions: its logarithm is the pole
order at infinity. The zero function has value zero. -/
noncomputable def infinityValuation (W : WeierstrassCurve.Affine F) :
    Valuation W.CoordinateRing ℤᵐ⁰ where
  toFun f := if f = 0 then 0 else exp ((Algebra.norm F[X] f).natDegree : ℤ)
  map_zero' := by simp
  map_one' := by simp
  map_mul' f g := by
    by_cases hf : f = 0
    · simp [hf]
    by_cases hg : g = 0
    · simp [hg]
    have hnf := (Algebra.norm_eq_zero_iff_of_basis (CoordinateRing.basis W)).not.mpr hf
    have hng := (Algebra.norm_eq_zero_iff_of_basis (CoordinateRing.basis W)).not.mpr hg
    simp [hf, hg, mul_ne_zero hf hg, map_mul, natDegree_mul hnf hng, Nat.cast_add, exp_add]
  map_add_le_max' f g := by
    by_cases hf : f = 0
    · simp [hf]
    by_cases hg : g = 0
    · simp [hg]
    by_cases hfg : f + g = 0
    · simp [hfg]
    have hnf := (Algebra.norm_eq_zero_iff_of_basis (CoordinateRing.basis W)).not.mpr hf
    have hng := (Algebra.norm_eq_zero_iff_of_basis (CoordinateRing.basis W)).not.mpr hg
    have hnfg := (Algebra.norm_eq_zero_iff_of_basis (CoordinateRing.basis W)).not.mpr hfg
    have hd := degree_norm_add_le f g
    rw [degree_eq_natDegree hnf, degree_eq_natDegree hng, degree_eq_natDegree hnfg] at hd
    have hn : (Algebra.norm F[X] (f + g)).natDegree ≤
        max (Algebra.norm F[X] f).natDegree (Algebra.norm F[X] g).natDegree := by
      exact le_max_iff.mpr ((le_max_iff.mp hd).imp WithBot.coe_le_coe.mp WithBot.coe_le_coe.mp)
    simp only [ite_eq_right hf, ite_eq_right hg, ite_eq_right hfg, le_max_iff, exp_le_exp]
    exact_mod_cast le_max_iff.mp hn

/-- On a nonzero regular function the valuation is the exponential of its norm degree. -/
theorem infinityValuation_apply_of_ne_zero {f : W.CoordinateRing} (hf : f ≠ 0) :
    infinityValuation W f = WithZero.exp ((Algebra.norm F[X] f).natDegree : ℤ) := by
  change (if f = 0 then 0 else _) = _
  rw [ite_eq_right hf]

/-- The norm-degree valuation has trivial support. -/
theorem infinityValuation_eq_zero_iff (f : W.CoordinateRing) :
    infinityValuation W f = 0 ↔ f = 0 := by
  by_cases hf : f = 0
  · simp [hf]
  · rw [infinityValuation_apply_of_ne_zero hf]
    simp [hf]

end WeierstrassCurve.Affine.CoordinateRing

namespace WeierstrassCurve.Affine.FunctionField
open WithZero
open scoped nonZeroDivisors
variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)
/-- The extension of the norm-degree valuation to the function field. -/
noncomputable def infinityValuation : Valuation W.FunctionField ℤᵐ⁰ :=
  (CoordinateRing.infinityValuation W).extendToLocalization
    (S := W.CoordinateRing⁰) (fun f hf => by
      change CoordinateRing.infinityValuation W f ≠ 0
      exact (CoordinateRing.infinityValuation_eq_zero_iff f).not.mpr
        (nonZeroDivisors.ne_zero hf)) W.FunctionField

/-- The function-field valuation extends the norm-degree valuation on regular functions. -/
theorem infinityValuation_algebraMap (f : W.CoordinateRing) :
    infinityValuation W (algebraMap W.CoordinateRing W.FunctionField f) =
      CoordinateRing.infinityValuation W f :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ f
end WeierstrassCurve.Affine.FunctionField
