/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineMarkedPolynomialBounds
/-!
# Reciprocal companions of bounded marked polynomials

Every bounded left polynomial has an explicit bounded right companion with
the required Laurent transition. Actual global sections have exactly this
companion. Gluing the corresponding actual chart sections is still required
to obtain surjectivity of the global-section polynomial map.
-/

open Polynomial CategoryTheory
open scoped LaurentPolynomial
@[expose] public noncomputable section
namespace FLT.Mazur.ProjectiveLineMarkedPolynomialReciprocal
open LaurentPolynomial ProjectiveLineMarkedPolynomialBounds
variable {K : Type*} [Field K]
/-- Reverse and shift a polynomial, including the marked transition coefficient. -/
def reciprocal (a : Kˣ) (m : ℕ) (p : K[X]) : K[X] :=
  Polynomial.C ((↑((-a)⁻¹) : K) ^ m) * p.reverse * Polynomial.X ^ (m - p.natDegree)
/-- The reciprocal companion satisfies the Laurent transition. -/
lemma reciprocal_transition (a : Kˣ) (m : ℕ) (p : K[X]) (hp : p.natDegree ≤ m) :
    invert (toLaurent (reciprocal a m p)) =
      (ProjectiveLineMarkedTransition.transition a : K[T;T⁻¹]) ^ m * toLaurent p := by
  have hq : toLaurent (reciprocal a m p) =
      LaurentPolynomial.C ((↑((-a)⁻¹) : K) ^ m) * invert (toLaurent p) * T m := by
    simp only [reciprocal, map_mul, Polynomial.toLaurent_C,
      Polynomial.toLaurent_X_pow, LaurentPolynomial.toLaurent_reverse]
    rw [← mul_assoc, mul_T_assoc]
    congr 2
    omega
  rw [hq, map_mul, map_mul, invert_C, involutive_invert, invert_T]
  change _ = (LaurentPolynomial.C (↑((-a)⁻¹) : K) * T (-1)) ^ m * toLaurent p
  rw [mul_pow, ← map_pow, T_pow]
  simp only [mul_neg_one]
  ring
/-- A polynomial in degreeLT (m+1) has natural degree at most m, including zero. -/
lemma natDegree_le_of_bounded (m : ℕ) (p : degreeLT K (m + 1)) : p.val.natDegree ≤ m := by
  have hp := mem_degreeLT.mp p.property
  by_cases hz : p.val = 0
  · simp [hz]
  · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hz).mpr hp)
/-- Every bounded polynomial has the required reciprocal Laurent companion. -/
lemma bounded_reciprocal_transition (a : Kˣ) (m : ℕ) (p : degreeLT K (m + 1)) :
    invert (toLaurent (reciprocal a m p.val)) =
      (ProjectiveLineMarkedTransition.transition a : K[T;T⁻¹]) ^ m * toLaurent p.val :=
  reciprocal_transition a m p.val (natDegree_le_of_bounded m p)
/-- The reciprocal companion of a bounded polynomial is also bounded. -/
lemma reciprocal_bounded (a : Kˣ) (m : ℕ) (p : degreeLT K (m + 1)) :
    reciprocal a m p.val ∈ degreeLT K (m + 1) :=
  right_mem_degreeLT a m (bounded_reciprocal_transition a m p)
/-- The right polynomial of a genuine section is its explicit reciprocal companion. -/
lemma rightPolynomial_eq_reciprocal (a : Kˣ) (m : ℕ)
    (s : FCurve.structureModule (ProjectiveLine.scheme K) ⟶
      ProjectiveLineMarkedSectionTransition.line K a m) :
    ProjectiveLineMarkedSectionTransition.rightPolynomial K a m s =
      reciprocal a m (ProjectiveLineMarkedSectionTransition.leftPolynomial K a m s) := by
  apply Polynomial.toLaurent_injective
  apply LaurentPolynomial.invert.injective
  rw [ProjectiveLineMarkedSectionTransition.transition]
  exact (bounded_reciprocal_transition a m
    ⟨_, leftPolynomial_bounded K a m s⟩).symm
end FLT.Mazur.ProjectiveLineMarkedPolynomialReciprocal
