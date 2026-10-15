/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentWeightedEvaluation
public import Mathlib.Tactic.LinearCombination

/-!
# Invertible square-zero changes of Laurent coordinate

The change u ↦ u + e q(u), for e² = 0, is a natural bijection on units.
Its inverse subtracts the same polynomial. No group law is assumed or changed
by this construction; comparison with an existing law is a separate theorem.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentSquareZeroCoordinate
open LaurentPolynomial LaurentWeightedEvaluation
variable {R B : Type*} [CommRing R] [CommRing B]

/-- The explicit inverse of a square-zero perturbation of a unit. -/
theorem perturb_mul_inverse (e : B) (he : e ^ 2 = 0) (u : Bˣ) (a : B) :
    (u.val + e * a) * (u⁻¹.val - e * a * u⁻¹.val ^ 2) = 1 := by
  linear_combination (1 - e * a * u⁻¹.val) * u.val_inv - a ^ 2 * u⁻¹.val ^ 2 * he

/-- Adding a square-zero multiple preserves invertibility, with a specified inverse. -/
def perturb (e : B) (he : e ^ 2 = 0) (u : Bˣ) (a : B) : Bˣ where
  val := u.val + e * a
  inv := u⁻¹.val - e * a * u⁻¹.val ^ 2
  val_inv := perturb_mul_inverse e he u a
  inv_val := (mul_comm _ _).trans (perturb_mul_inverse e he u a)

/-- The perturbed unit has exactly the prescribed first-order coordinate. -/
theorem perturb_val (e : B) (he : e ^ 2 = 0) (u : Bˣ) (a : B) :
    (perturb e he u a).val = u.val + e * a := rfl

/-- Perturbation preserves a coordinate after multiplication by its square-zero weight. -/
theorem perturb_weighted (e : B) (he : e ^ 2 = 0) (u : Bˣ) (a : B) :
    e * (perturb e he u a).val = e * u.val := by
  rw [perturb_val, mul_add, ← mul_assoc e e, ← pow_two, he, zero_mul, add_zero]

/-- Apply a Laurent vector field to a unit with square-zero weight. -/
def change (f : R →+* B) (e : B) (he : e ^ 2 = 0) (q : R[T;T⁻¹]) (u : Bˣ) : Bˣ :=
  perturb e he u (eval₂ f u q)

/-- Its value is the original coordinate plus the evaluated vector field. -/
theorem change_val (f : R →+* B) (e : B) (he : e ^ 2 = 0) (q : R[T;T⁻¹]) (u : Bˣ) :
    (change f e he q u).val = u.val + e * eval₂ f u q := rfl

/-- Evaluating a second vector field after the change has the same weighted value. -/
theorem change_eval (f : R →+* B) (e : B) (he : e ^ 2 = 0)
    (p q : R[T;T⁻¹]) (u : Bˣ) :
    e * eval₂ f (change f e he q u) p = e * eval₂ f u p :=
  weighted_eval₂ e f f _ u (fun _ ↦ rfl) (perturb_weighted e he u _) p

/-- Square-zero coordinate changes compose by addition of their vector fields. -/
theorem change_change (f : R →+* B) (e : B) (he : e ^ 2 = 0)
    (p q : R[T;T⁻¹]) (u : Bˣ) :
    change f e he p (change f e he q u) = change f e he (p + q) u := by
  apply Units.ext
  simp only [change_val, change_eval, map_add]
  ring

/-- The zero vector field gives the unchanged unit. -/
theorem change_zero (f : R →+* B) (e : B) (he : e ^ 2 = 0) (u : Bˣ) :
    change f e he 0 u = u := by
  apply Units.ext
  simp only [change_val, map_zero, mul_zero, add_zero]

/-- Negating the vector field constructs an actual inverse to the coordinate change. -/
def changeEquiv (f : R →+* B) (e : B) (he : e ^ 2 = 0) (q : R[T;T⁻¹]) : Bˣ ≃ Bˣ where
  toFun := change f e he q
  invFun := change f e he (-q)
  left_inv u := by rw [change_change, neg_add_cancel, change_zero]
  right_inv u := by rw [change_change, add_neg_cancel, change_zero]

/-- A normalized vector field preserves the identity unit. -/
theorem change_one (f : R →+* B) (e : B) (he : e ^ 2 = 0) (q : R[T;T⁻¹])
    (hq : eval₂ f (1 : Bˣ) q = 0) : change f e he q 1 = 1 := by
  apply Units.ext
  simp only [change_val, hq, mul_zero, add_zero]

end FLT.Mazur.LaurentSquareZeroCoordinate
