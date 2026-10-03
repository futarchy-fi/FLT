/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Pi
public import Mathlib.Algebra.Algebra.Basic

/-!
# Exponent vectors for cyclic monomials

Elementary product and total-degree identities used to reduce an exponent
at least p with a relation xᵢ^p = aᵢ xⱼ.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.CyclicPresentation

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]

/-- The monomial associated with an exponent vector on a finite index type. -/
def monomial (x : ι → A) (d : ι → ℕ) : A := ∏ i, x i ^ d i

omit [DecidableEq ι] in
/-- Addition of exponent vectors multiplies the associated monomials. -/
theorem monomial_add (x : ι → A) (d e : ι → ℕ) :
    monomial x (d + e) = monomial x d * monomial x e := by
  simp [monomial, pow_add, Finset.prod_mul_distrib]

/-- An exponent vector supported at one index gives a pure power. -/
theorem monomial_single (x : ι → A) (i : ι) (n : ℕ) :
    monomial x (Pi.single i n) = x i ^ n := by
  classical
  unfold monomial
  rw [Finset.prod_eq_single i]
  · simp
  · intro j hj hji
    simp [Pi.single_eq_of_ne hji]
  · simp

omit [DecidableEq ι] in
/-- Total degree adds under addition of exponent vectors. -/
theorem degree_add (d e : ι → ℕ) :
    (∑ i, (d + e) i) = (∑ i, d i) + ∑ i, e i := by
  simp [Finset.sum_add_distrib]

/-- Total degree of a pure power is its exponent. -/
theorem degree_single (i : ι) (n : ℕ) : (∑ j, Pi.single i n j) = n := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [Pi.single_eq_of_ne hji]
  · simp

omit [Fintype ι] in
/-- Removing p copies at an index with exponent at least p reconstructs the vector. -/
theorem sub_single_add (d : ι → ℕ) (i : ι) (p : ℕ) (hi : p ≤ d i) :
    (d - Pi.single i p) + Pi.single i p = d := by
  funext j
  by_cases hj : j = i
  · subst j
    simpa using Nat.sub_add_cancel hi
  · simp [Pi.single_eq_of_ne hj]

end ThreeAdicPlan.CyclicPresentation
