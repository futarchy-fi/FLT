/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentBoundaryVectorField
public import FLT.Mazur.LaurentSquareZeroCoordinate

/-!
# The reciprocal chart of a square-zero coordinate change

Inverting the perturbed unit gives the change defined by the reciprocal vector
field, including the minus sign and the squared reciprocal coordinate. Thus the
two boundary tests apply to the same actual unit automorphism.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentSquareZeroCoordinate
open LaurentPolynomial LaurentBoundaryVectorField PolygonScalingNaturality
variable {R B : Type*} [CommRing R] [CommRing B]

/-- Inverting a Laurent variable before evaluation inverts the evaluation unit. -/
theorem eval₂_invert (f : R →+* B) (u : Bˣ) (q : R[T;T⁻¹]) :
    eval₂ f u (invert q) = eval₂ f u⁻¹ q := by
  have he : (eval₂ f u).comp (invert (R := R)).toRingHom = eval₂ f u⁻¹ := by
    apply ringHom_ext <;> simp [eval₂_C, eval₂_T]
  exact congrArg (fun F : R[T;T⁻¹] →+* B ↦ F q) he

/-- The reciprocal vector field evaluates with the derivative factor -u². -/
theorem eval₂_reciprocalField (f : R →+* B) (u : Bˣ) (q : R[T;T⁻¹]) :
    eval₂ f u (reciprocalField q) = -(u.val ^ 2 * eval₂ f u⁻¹ q) := by
  simp only [reciprocalField, map_neg, map_mul, eval₂_T, eval₂_invert,
    zpow_ofNat, Units.val_pow_eq_pow_val]

/-- Both coordinate charts describe the inverse of the same perturbed unit. -/
theorem change_inv (f : R →+* B) (e : B) (he : e ^ 2 = 0)
    (q : R[T;T⁻¹]) (u : Bˣ) :
    (change f e he q u)⁻¹ = change f e he (reciprocalField q) u⁻¹ := by
  apply Units.ext
  change u⁻¹.val - e * eval₂ f u q * u⁻¹.val ^ 2 =
    u⁻¹.val + e * eval₂ f u⁻¹ (reciprocalField q)
  rw [eval₂_reciprocalField, inv_inv]
  ring

end FLT.Mazur.LaurentSquareZeroCoordinate
