/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentBoundaryVectorField

/-!
# The maximal polynomial part of a Laurent boundary field fixing its origin

Removing the constant term of the Laurent truncation retains precisely the
strictly positive coefficients. The complementary Laurent field has only
nonpositive exponents, making the remaining boundary obstruction explicit.
-/

@[expose] public noncomputable section
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.LaurentPositivePart
open LaurentPolynomial LaurentBoundaryVectorField
variable {R : Type*} [CommRing R]

/-- Truncation retains each original nonnegative Laurent coefficient. -/
theorem trunc_coeff (q : R[T;T⁻¹]) (n : ℕ) : (trunc q).coeff n = q.coeff (n : ℤ) := by
  simp [trunc, Finsupp.comapDomain_apply]

/-- The polynomial consisting of the strictly positive Laurent terms. -/
def positivePart (q : R[T;T⁻¹]) : R[X] := trunc q - Polynomial.C (q.coeff 0)

/-- Its boundary origin is fixed without an extra condition on the original Laurent field. -/
theorem positivePart_coeff_zero (q : R[T;T⁻¹]) : (positivePart q).coeff 0 = 0 := by
  simp only [positivePart, Polynomial.coeff_sub, trunc_coeff, Nat.cast_zero,
    Polynomial.coeff_C_zero, sub_self]

/-- Every strictly positive coefficient is retained exactly. -/
theorem positivePart_coeff_succ (q : R[T;T⁻¹]) (n : ℕ) :
    (positivePart q).coeff (n + 1) = q.coeff ((n + 1 : ℕ) : ℤ) := by
  simp only [positivePart, Polynomial.coeff_sub, trunc_coeff,
    Polynomial.coeff_C_succ, sub_zero]

/-- The nonpositive Laurent tail omitted by the constructed polynomial extension. -/
def boundaryTail (q : R[T;T⁻¹]) : R[T;T⁻¹] := q - (positivePart q).toLaurent

/-- The tail retains all nonpositive coefficients of the original field. -/
theorem boundaryTail_coeff_nonpos (q : R[T;T⁻¹]) (d : ℤ) (hd : d ≤ 0) :
    (boundaryTail q).coeff d = q.coeff d := by
  change q.coeff d - ((positivePart q).toLaurent).coeff d = q.coeff d
  rcases lt_or_eq_of_le hd with hd | rfl
  · rw [polynomial_coeff_neg _ d hd, sub_zero]
  · rw [polynomial_coeff_zero, positivePart_coeff_zero, sub_zero]

/-- Polynomial embedding retains the coefficient at every natural exponent. -/
theorem toLaurent_coeff_nat (p : R[X]) (n : ℕ) : p.toLaurent.coeff (n : ℤ) = p.coeff n := by
  exact Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective _ n

/-- The tail has no strictly positive coefficients. -/
theorem boundaryTail_coeff_pos (q : R[T;T⁻¹]) (d : ℤ) (hd : 0 < d) :
    (boundaryTail q).coeff d = 0 := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hd)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  change q.coeff _ - ((positivePart q).toLaurent).coeff _ = 0
  rw [toLaurent_coeff_nat, positivePart_coeff_succ, sub_self]

/-- Vanishing of the tail is exactly the missing nonpositive-coefficient condition. -/
theorem boundaryTail_eq_zero_iff (q : R[T;T⁻¹]) :
    boundaryTail q = 0 ↔ ∀ d : ℤ, d ≤ 0 → q.coeff d = 0 := by
  constructor
  · intro he d hd
    rw [← boundaryTail_coeff_nonpos q d hd, he]
    rfl
  · intro he
    ext d
    change (boundaryTail q).coeff d = 0
    by_cases hd : d ≤ 0
    · rw [boundaryTail_coeff_nonpos q d hd, he d hd]
    · exact boundaryTail_coeff_pos q d (by omega)

/-- With zero tail the constructed polynomial is the entire original Laurent field. -/
theorem positivePart_toLaurent_iff (q : R[T;T⁻¹]) :
    (positivePart q).toLaurent = q ↔ boundaryTail q = 0 := by
  rw [boundaryTail, sub_eq_zero, eq_comm]

end FLT.Mazur.LaurentPositivePart
