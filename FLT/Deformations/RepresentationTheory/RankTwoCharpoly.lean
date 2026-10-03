/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
# Rank-two characteristic polynomials, trace and determinant

These identities turn a factor spectrum into trace and determinant statements
without requiring a diagonalization of the original operator.
-/

@[expose] public noncomputable section

namespace LinearMap
open Polynomial
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  [Module.Finite k V] (T : Module.End k V)

/-- In dimension two the characteristic polynomial is determined by trace and determinant. -/
theorem charpoly_eq_quadratic (hV : Module.finrank k V = 2) :
    T.charpoly = X ^ 2 - C (trace k V T) * X + C T.det := by
  let b := Module.Free.chooseBasis k V
  rw [← charpoly_toMatrix T b, trace_eq_matrix_trace k b, ← det_toMatrix b]
  exact Matrix.charpoly_of_card_eq_two _ (by
    simpa only [← Module.finrank_eq_card_chooseBasisIndex] using hV)

/-- A factored rank-two characteristic polynomial has the expected trace and determinant. -/
theorem trace_det_of_charpoly_factors (hV : Module.finrank k V = 2) (a b : k)
    (h : T.charpoly = (X - C a) * (X - C b)) :
    trace k V T = a + b ∧ T.det = a * b := by
  rw [T.charpoly_eq_quadratic hV] at h
  constructor
  · have h₁ : -(trace k V T) = -a - b := by
      simpa [mul_sub, sub_mul, coeff_sub, coeff_add] using
        congrArg (fun P : k[X] ↦ P.coeff 1) h
    linear_combination -h₁
  · simpa [mul_sub, sub_mul, coeff_sub, coeff_add] using
      congrArg (fun P : k[X] ↦ P.coeff 0) h

/-- Trace and determinant conversely recover the two proposed factors. -/
theorem charpoly_factors_of_trace_det (hV : Module.finrank k V = 2) (a b : k)
    (ht : trace k V T = a + b) (hd : T.det = a * b) :
    T.charpoly = (X - C a) * (X - C b) := by
  rw [T.charpoly_eq_quadratic hV, ht, hd, map_add, map_mul]
  ring

end LinearMap
