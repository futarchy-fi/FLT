/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentSquareZeroCoordinate

/-!
# Linearizing an actual square-zero law with a specified coboundary

The explicit coordinate bijection intertwines a unit law with multiplication
when its actual error is the coboundary of that coordinate's vector field.
This does not identify the unchanged law with multiplication.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentSquareZeroCoordinate
open LaurentPolynomial LaurentWeightedEvaluation
variable {R B : Type*} [CommRing R] [CommRing B]

/-- An explicitly specified coboundary is killed by the corresponding coordinate change. -/
theorem change_mul_of_coboundary (f : R →+* B) (e : B) (he : e ^ 2 = 0)
    (q : R[T;T⁻¹]) (M : Bˣ → Bˣ → Bˣ)
    (hM : ∀ u v, (M u v).val = u.val * v.val +
      e * (u.val * eval₂ f v q + v.val * eval₂ f u q - eval₂ f (u * v) q))
    (u v : Bˣ) : change f e he q (M u v) = change f e he q u * change f e he q v := by
  have hw : e * (M u v).val = e * (u * v).val := by
    rw [hM, mul_add, ← mul_assoc e e, ← pow_two, he, zero_mul, add_zero, Units.val_mul]
  have hq := weighted_eval₂ e f f (M u v) (u * v) (fun _ ↦ rfl) hw q
  apply Units.ext
  simp only [change_val, Units.val_mul]
  rw [hq, hM]
  linear_combination -(eval₂ f u q * eval₂ f v q) * he

end FLT.Mazur.LaurentSquareZeroCoordinate
