/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberAlgebra
public import Mathlib.Algebra.Polynomial.Laurent

/-!
# A unit product fiber is the multiplicative affine line

When c is invertible the actual equation pq = c has Laurent coordinate p,
with q = c/p. This comparison applies to the middle split-depth residue fiber.
-/

@[expose] public noncomputable section

open LaurentPolynomial
open scoped LaurentPolynomial

namespace FLT.Mazur.NodalFiber

variable {R : Type*} [CommRing R] (c : Rˣ)

/-- The first tangent coordinate is a unit with its explicit inverse. -/
def tangentUnit : (Coordinate (↑c : R))ˣ where
  val := p (↑c : R)
  inv := algebraMap R _ (↑c⁻¹ : R) * q (↑c : R)
  val_inv := by
    rw [mul_left_comm, relation, ← map_mul, Units.inv_mul, map_one]
  inv_val := by
    rw [mul_assoc, mul_comm (q _) (p _), relation, ← map_mul, Units.inv_mul, map_one]

/-- The product fiber maps to Laurent polynomials by p = T and q = cT⁻¹. -/
def toLaurent : Coordinate (↑c : R) →ₐ[R] R[T;T⁻¹] :=
  evaluation (↑c : R) (T 1) (C (↑c : R) * T (-1)) (by
    rw [mul_left_comm, ← T_add, add_neg_cancel, T_zero, mul_one]
    rfl)

/-- Evaluation at the actual invertible tangent coordinate gives the inverse map. -/
def fromLaurent : R[T;T⁻¹] →ₐ[R] Coordinate (↑c : R) where
  toRingHom := eval₂ (algebraMap R _) (tangentUnit c)
  commutes' r := eval₂_C _ _ r

/-- The Laurent comparison preserves the first coordinate. -/
@[simp] theorem toLaurent_p : toLaurent c (p (↑c : R)) = T 1 := evaluation_p _ _ _ _

/-- The second coordinate is precisely c times the inverse Laurent parameter. -/
@[simp] theorem toLaurent_q :
    toLaurent c (q (↑c : R)) = C (↑c : R) * T (-1) := evaluation_q _ _ _ _

/-- The positive Laurent parameter evaluates to p. -/
@[simp] theorem fromLaurent_T : fromLaurent c (T 1) = p (↑c : R) := by
  change eval₂ _ _ (T 1) = _
  simp [tangentUnit]

/-- The negative Laurent parameter evaluates to c⁻¹q. -/
@[simp] theorem fromLaurent_T_inv : fromLaurent c (T (-1)) =
    algebraMap R _ (↑c⁻¹ : R) * q (↑c : R) := by
  change eval₂ _ _ (T (-1)) = _
  simp [tangentUnit]

/-- Constants retain their original coefficient map. -/
@[simp] theorem fromLaurent_C (r : R) : fromLaurent c (C r) = algebraMap R _ r :=
  eval₂_C _ _ _

/-- The actual unit product fiber has Laurent coordinate algebra. -/
def laurentEquiv : Coordinate (↑c : R) ≃ₐ[R] R[T;T⁻¹] := by
  apply AlgEquiv.ofAlgHom (toLaurent c) (fromLaurent c)
  · apply AlgHom.ext
    intro z
    change toLaurent c (fromLaurent c z) = z
    induction z using LaurentPolynomial.induction_on with
    | h_C r => simp [AlgHom.commutes]
    | h_add hf hg => simp [hf, hg]
    | h_C_mul_T n a h =>
      rw [T_add, ← mul_assoc]
      rw [map_mul, map_mul, h, fromLaurent_T, toLaurent_p]
    | h_C_mul_T_Z n a h =>
      have hi : toLaurent c (fromLaurent c (T (-1))) = T (-1) := by
        rw [fromLaurent_T_inv, map_mul, AlgHom.commutes, toLaurent_q]
        change C (↑c⁻¹ : R) * (C (↑c : R) * T (-1)) = _
        rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      rw [sub_eq_add_neg, T_add, ← mul_assoc]
      rw [map_mul, map_mul, h, hi]
  · apply hom_ext
    · simp
    · simp only [AlgHom.comp_apply, toLaurent_q, map_mul, fromLaurent_C,
        fromLaurent_T_inv, AlgHom.id_apply]
      rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]

end FLT.Mazur.NodalFiber
