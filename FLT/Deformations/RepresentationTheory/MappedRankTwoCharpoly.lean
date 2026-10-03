/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.RankTwoCharpoly

/-!
# Trace and determinant of a rank-two characteristic polynomial after mapping

Extract the original trace and determinant through the coefficient embedding.
No scalar-extension representation or diagonalization is assumed.
-/

@[expose] public noncomputable section
namespace LinearMap
open Polynomial

variable {k F V : Type*} [Field k] [Field F] [AddCommGroup V] [Module k V]
  [Module.Finite k V] (T : Module.End k V) (f : k →+* F)

/-- Factoring the mapped charpoly computes the mapped original trace and determinant. -/
theorem trace_det_of_map_charpoly_factors (hV : Module.finrank k V = 2) (a b : F)
    (h : T.charpoly.map f = (X - C a) * (X - C b)) :
    f (trace k V T) = a + b ∧ f T.det = a * b := by
  rw [T.charpoly_eq_quadratic hV] at h
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, map_X, map_C] at h
  constructor
  · have h₁ : -f (trace k V T) = -a - b := by
      simpa [mul_sub, sub_mul, coeff_sub, coeff_add] using
        congrArg (fun P : F[X] ↦ P.coeff 1) h
    linear_combination -h₁
  · simpa [mul_sub, sub_mul, coeff_sub, coeff_add] using
      congrArg (fun P : F[X] ↦ P.coeff 0) h

end LinearMap
