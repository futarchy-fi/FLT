/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Tactic

/-!
# Laurent vector fields fixing both boundary points

A vector field q(X) transforms to -Y²q(Y⁻¹) in the reciprocal coordinate.
If both expressions are polynomial and vanish at their boundary origins,
then q is a scalar multiple of X. Fixing the marked point X = 1 kills it.
The coefficient ring may have nilpotents and arbitrary characteristic.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial Polynomial
namespace FLT.Mazur.LaurentBoundaryVectorField
open LaurentPolynomial
variable {R : Type*} [CommRing R]

/-- Polynomial Laurent coefficients vanish at every negative exponent. -/
theorem polynomial_coeff_neg (p : R[X]) (d : ℤ) (hd : d < 0) :
    (Polynomial.toLaurent p).coeff d = 0 := by
  apply Finsupp.notMem_support_iff.mp
  rw [support_coeff_toLaurent, Finset.mem_map]
  rintro ⟨k, _, hk⟩
  change (k : ℤ) = d at hk
  omega

/-- Passing to Laurent polynomials retains the coefficient at zero. -/
theorem polynomial_coeff_zero (p : R[X]) :
    (Polynomial.toLaurent p).coeff 0 = p.coeff 0 := by
  exact Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective _ 0

/-- The reciprocal-coordinate vector field, including its derivative sign. -/
def reciprocalField (q : R[T;T⁻¹]) : R[T;T⁻¹] := - (T 2 * invert q)

/-- The reciprocal vector field reverses exponents about two. -/
theorem reciprocalField_coeff (q : R[T;T⁻¹]) (d : ℤ) :
    (reciprocalField q).coeff d = -q.coeff (2 - d) := by
  simp only [reciprocalField, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply]
  change -((T 2 * invert q).coeff d) = _
  congr 1
  rw [show (T 2 : R[T;T⁻¹]) = AddMonoidAlgebra.single 2 1 from rfl]
  rw [AddMonoidAlgebra.coeff_single_mul_apply]
  simp [sub_eq_add_neg, add_comm]

/-- Boundary-vanishing polynomial vector fields on both charts are precisely scalings. -/
theorem eq_scaling_of_boundary (q : R[T;T⁻¹]) (p r : R[X])
    (hp : Polynomial.toLaurent p = q) (hr : Polynomial.toLaurent r = reciprocalField q)
    (hp0 : p.coeff 0 = 0) (hr0 : r.coeff 0 = 0) : q = C (q.coeff 1) * T 1 := by
  have hlow (d : ℤ) (hd : d ≤ 0) : q.coeff d = 0 := by
    rcases lt_or_eq_of_le hd with hd | rfl
    · rw [← hp]
      exact polynomial_coeff_neg p d hd
    · rw [← hp, polynomial_coeff_zero, hp0]
  have hhigh (d : ℤ) (hd : 2 ≤ d) : q.coeff d = 0 := by
    have he : (reciprocalField q).coeff (2 - d) = 0 := by
      rw [← hr]
      rcases lt_or_eq_of_le hd with hd | rfl
      · exact polynomial_coeff_neg r _ (by omega)
      · simpa only [sub_self, polynomial_coeff_zero] using hr0
    rw [reciprocalField_coeff, sub_sub_cancel, neg_eq_zero] at he
    exact he
  ext d
  rw [← single_eq_C_mul_T]
  change q.coeff d = Finsupp.single 1 (q.coeff 1) d
  by_cases hd : d = 1
  · subst d
    simp
  · rw [Finsupp.single_eq_of_ne hd]
    rcases le_or_gt d 0 with h | h
    · exact hlow d h
    · exact hhigh d (by omega)

/-- A boundary-preserving vector field fixing the marked unit is zero. -/
theorem eq_zero_of_boundary (q : R[T;T⁻¹]) (p r : R[X])
    (hp : Polynomial.toLaurent p = q) (hr : Polynomial.toLaurent r = reciprocalField q)
    (hp0 : p.coeff 0 = 0) (hr0 : r.coeff 0 = 0)
    (h1 : eval₂ (RingHom.id R) (1 : Rˣ) q = 0) : q = 0 := by
  have he := eq_scaling_of_boundary q p r hp hr hp0 hr0
  have hc : q.coeff 1 = 0 := by
    have hh := congrArg (eval₂ (RingHom.id R) (1 : Rˣ)) he
    simp only [map_mul, eval₂_C, RingHom.id_apply, eval₂_T,
      one_zpow, Units.val_one, mul_one] at hh
    exact hh.symm.trans h1
  rw [he, hc, map_zero, zero_mul]

end FLT.Mazur.LaurentBoundaryVectorField
