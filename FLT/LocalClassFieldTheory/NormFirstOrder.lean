/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The first-order term of the norm

The determinant expansion gives a quadratic remainder over any finite free
commutative algebra. No norm-surjectivity or trace-comparison assumption is used.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [Module.Free R S] [Module.Finite R S]

/-- The linear coefficient of the norm is the trace; the remainder is quadratic. -/
theorem norm_one_add_smul (r : R) (x : S) :
    ∃ a : R, Algebra.norm R (1 + r • x) = 1 + r * Algebra.trace R S x + r ^ 2 * a := by
  classical
  let b := Module.Free.chooseBasis R S
  rw [Algebra.norm_eq_matrix_det b, map_add, map_one, map_smul,
    Matrix.det_one_add_smul, Algebra.trace_eq_matrix_trace b]
  refine ⟨(Matrix.det (1 + (Polynomial.X : Polynomial R) •
    (Algebra.leftMulMatrix b x).map Polynomial.C)).divX.divX.eval r, ?_⟩
  ring

/-- At every positive level, the norm agrees with the trace one level further. -/
theorem norm_one_add_pow_sub_trace_dvd (π : R) (n : ℕ) (hn : 0 < n) (x : S) :
    π ^ (n + 1) ∣ Algebra.norm R (1 + (π ^ n) • x) -
      (1 + π ^ n * Algebra.trace R S x) := by
  obtain ⟨a, ha⟩ := norm_one_add_smul R S (π ^ n) x
  rw [ha, add_sub_cancel_left]
  apply dvd_mul_of_dvd_left
  rw [← pow_mul]
  exact pow_dvd_pow π (by omega)

/-- In particular the norm preserves each positive principal-unit level. -/
theorem norm_one_add_pow_sub_one_dvd (π : R) (n : ℕ) (x : S) :
    π ^ n ∣ Algebra.norm R (1 + (π ^ n) • x) - 1 := by
  obtain ⟨a, ha⟩ := norm_one_add_smul R S (π ^ n) x
  refine ⟨Algebra.trace R S x + π ^ n * a, ?_⟩
  rw [ha]
  ring

end LocalClassFieldTheory
