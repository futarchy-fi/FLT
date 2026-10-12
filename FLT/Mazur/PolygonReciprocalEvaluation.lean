/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonScaledReciprocal

/-!
# Reciprocal evaluation reverses a Laurent action character

The equality holds on the entire Laurent algebra over any coefficient
algebra. Both signed tangent scales are allowed, including in characteristic two.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonScaledReciprocal
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Evaluate every Laurent function at a unit of a coefficient algebra. -/
def evaluation (z : Aˣ) : R[T;T⁻¹] →ₐ[R] A :=
  { LaurentPolynomial.eval₂ (algebraMap R A) z with
    commutes' := fun r => LaurentPolynomial.eval₂_C _ _ r }

/-- Evaluation fixes the coefficient algebra structure. -/
theorem evaluation_C (z : Aˣ) (r : R) :
    evaluation z (LaurentPolynomial.C r) = algebraMap R A r :=
  LaurentPolynomial.eval₂_C _ _ _

/-- Evaluation remembers every positive and negative power. -/
theorem evaluation_T (z : Aˣ) (n : ℤ) :
    evaluation (R := R) z (LaurentPolynomial.T n) = (z ^ n : Aˣ) :=
  LaurentPolynomial.eval₂_T _ _ _

/-- A scaled reciprocal substitutes the inverse unit into the full Laurent algebra. -/
theorem evaluation_comp_reciprocal (a : Rˣ) (z : Aˣ) :
    (evaluation z).comp (reciprocal a) =
      evaluation (Units.map (algebraMap R A) a * z⁻¹) := by
  apply AlgHom.coe_ringHom_injective
  apply PolygonScalingNaturality.ringHom_ext
  · intro r
    simp only [AlgHom.coe_toRingHom, AlgHom.comp_apply, reciprocal_C, evaluation_C]
  · simp only [AlgHom.coe_toRingHom, AlgHom.comp_apply, reciprocal_T, map_mul,
      evaluation_C, evaluation_T, zpow_one, zpow_neg_one, Units.val_mul, Units.coe_map]
    rfl
  · simp only [AlgHom.coe_toRingHom, AlgHom.comp_apply, reciprocal_T_inv, map_mul,
      evaluation_C, evaluation_T, zpow_one, zpow_neg_one, mul_inv_rev, inv_inv,
      Units.val_mul, ← map_inv, Units.coe_map]
    exact mul_comm _ _

/-- Positive conic scaling becomes inverse scaling of the actual reciprocal parameter. -/
theorem evaluation_reciprocal_mul (a : Rˣ) (τ z : Aˣ) :
    (evaluation (τ * z)).comp (reciprocal a) =
      evaluation (τ⁻¹ * (Units.map (algebraMap R A) a * z⁻¹)) := by
  rw [evaluation_comp_reciprocal]
  apply congrArg (evaluation (R := R))
  rw [mul_inv_rev]
  ac_rfl

/-- The opposite conic character becomes the positive next-line character. -/
theorem evaluation_reciprocal_inv_mul (a : Rˣ) (τ z : Aˣ) :
    (evaluation (τ⁻¹ * z)).comp (reciprocal a) =
      evaluation (τ * (Units.map (algebraMap R A) a * z⁻¹)) := by
  simpa only [inv_inv] using evaluation_reciprocal_mul a τ⁻¹ z

end FLT.Mazur.PolygonScaledReciprocal
