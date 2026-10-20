/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# A monic equation from a polynomial that is locally monic

For every possible degree, replace the top term of the corresponding
truncation by a monic term. Their product is monic. Wherever the original
polynomial is monic, one factor recovers it, so every original root remains
a root of this product. No constant local degree is required.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.LocallyMonicPolynomialEnvelope
variable {R S : Type*} [CommRing R] [CommRing S]

/-- The monic truncation at one possible local degree. -/
def factor (P : R[X]) (n : ℕ) : R[X] :=
  X ^ n + ∑ i : Fin n, C (P.coeff i) * X ^ (i : ℕ)

/-- Every factor is monic, without any assumption on the original polynomial. -/
theorem factor_monic (P : R[X]) (n : ℕ) : (factor P n).Monic :=
  monic_X_pow_add (degree_sum_fin_lt (fun i ↦ P.coeff i))

/-- At the degree of a monic polynomial, the factor is the original polynomial. -/
theorem factor_eq {P : R[X]} (hP : P.Monic) : factor P P.natDegree = P := by
  unfold factor
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ C (P.coeff i) * X ^ i)]
  exact hP.as_sum.symm

/-- Monic truncations commute with arbitrary coefficient maps. -/
theorem factor_map (P : R[X]) (n : ℕ) (f : R →+* S) :
    (factor P n).map f = factor (P.map f) n := by
  simp only [factor, Polynomial.map_add, Polynomial.map_pow, map_X,
    Polynomial.map_sum, Polynomial.map_mul, map_C, coeff_map]

/-- The product includes every possible local degree up to the specified bound. -/
def envelope (P : R[X]) (N : ℕ) : R[X] := ∏ n ∈ Finset.range (N + 1), factor P n

/-- The resulting polynomial is globally monic even if the original local degrees vary. -/
theorem envelope_monic (P : R[X]) (N : ℕ) : (envelope P N).Monic :=
  monic_prod_of_monic _ _ (fun n _ ↦ factor_monic P n)

/-- The same product can be computed after any coefficient extension. -/
theorem envelope_map (P : R[X]) (N : ℕ) (f : R →+* S) :
    (envelope P N).map f = envelope (P.map f) N := by
  simp only [envelope, Polynomial.map_prod, factor_map]

/-- A root of a monic polynomial is a root of the bounded product. -/
theorem envelope_eval_eq_zero {P : R[X]} (hP : P.Monic) (N : ℕ)
    (hN : P.natDegree ≤ N) (x : R) (hx : P.eval x = 0) :
    (envelope P N).eval x = 0 := by
  rw [envelope, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.lt_succ_of_le hN))
  rw [factor_eq hP]
  exact hx

/-- Local monicity and an original root suffice; no degree preservation is assumed. -/
theorem envelope_eval₂_eq_zero (P : R[X]) (f : R →+* S)
    (hP : (P.map f).Monic) (x : S) (hx : P.eval₂ f x = 0) :
    (envelope P P.natDegree).eval₂ f x = 0 := by
  rw [← eval_map, envelope_map]
  apply envelope_eval_eq_zero hP _ natDegree_map_le
  rwa [eval_map]

end FLT.Mazur.LocallyMonicPolynomialEnvelope
