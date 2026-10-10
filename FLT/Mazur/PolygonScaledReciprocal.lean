/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonScalingNaturality

/-!+# Scaled reciprocal Laurent parameters

The substitution U = a/Z is an involution for every unit a. It records
the scale as well as the inversion when comparing adjacent component charts.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonScaledReciprocal
variable {R : Type*} [CommRing R]

/-- Laurent scaling as an algebra map over the original coefficient ring. -/
def scaling (a : Rˣ) : R[T;T⁻¹] →ₐ[R] R[T;T⁻¹] where
  __ := PolygonChartScaling.laurent a
  commutes' := PolygonChartScaling.laurent_C a

/-- Substitute a divided by the original Laurent parameter. -/
def reciprocal (a : Rˣ) : R[T;T⁻¹] →ₐ[R] R[T;T⁻¹] :=
  LaurentPolynomial.invert.toAlgHom.comp (scaling a)

/-- The original parameter keeps its specified reciprocal scale. -/
@[simp] theorem reciprocal_T (a : Rˣ) :
    reciprocal a (LaurentPolynomial.T 1) =
      LaurentPolynomial.C (a : R) * LaurentPolynomial.T (-1) := by
  change LaurentPolynomial.invert (PolygonChartScaling.laurent a _) = _
  rw [PolygonChartScaling.laurent_T_one, map_mul,
    LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]

/-- The inverse parameter has the inverse scale and the original exponent. -/
@[simp] theorem reciprocal_T_inv (a : Rˣ) :
    reciprocal a (LaurentPolynomial.T (-1)) =
      LaurentPolynomial.C (↑a⁻¹ : R) * LaurentPolynomial.T 1 := by
  change LaurentPolynomial.invert (PolygonChartScaling.laurent a _) = _
  rw [PolygonChartScaling.laurent_T_neg_one, map_mul,
    LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
  rfl

/-- Every coefficient is fixed by the reciprocal substitution. -/
@[simp] theorem reciprocal_C (a : Rˣ) (r : R) :
    reciprocal a (LaurentPolynomial.C r) = LaurentPolynomial.C r :=
  (reciprocal a).commutes r

/-- Applying the same scaled reciprocal twice fixes every Laurent function. -/
theorem reciprocal_involutive (a : Rˣ) : Function.Involutive (reciprocal a) := by
  have H : (reciprocal a).comp (reciprocal a) = AlgHom.id R _ := by
    apply AlgHom.coe_ringHom_injective
    apply PolygonScalingNaturality.ringHom_ext
    · intro r
      simp
    · simp only [AlgHom.coe_toRingHom, AlgHom.comp_apply,
        AlgHom.id_apply]
      rw [reciprocal_T, map_mul, reciprocal_C, reciprocal_T_inv,
        ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
    · simp only [AlgHom.coe_toRingHom, AlgHom.comp_apply,
        AlgHom.id_apply]
      rw [reciprocal_T_inv, map_mul, reciprocal_C, reciprocal_T,
        ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  intro z
  exact congrArg (fun f : R[T;T⁻¹] →ₐ[R] R[T;T⁻¹] => f z) H

/-- The scaled reciprocal is a genuine Laurent algebra automorphism. -/
def equiv (a : Rˣ) : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹] :=
  AlgEquiv.ofBijective (reciprocal a) (reciprocal_involutive a).bijective

/-- The reciprocal with inverse scale removes the scale of an affine parameter. -/
theorem reciprocal_scaled_affine (a : Rˣ) :
    (reciprocal a⁻¹).comp
      (Polynomial.toLaurentAlg.comp (Polynomial.aeval (Polynomial.C (a : R) * Polynomial.X))) =
        LaurentPolynomial.invert.toAlgHom.comp Polynomial.toLaurentAlg := by
  apply Polynomial.algHom_ext
  simp only [AlgHom.comp_apply, Polynomial.aeval_X, Polynomial.toLaurentAlg_apply,
    AlgEquiv.coe_toAlgHom, Polynomial.toLaurent_X, LaurentPolynomial.invert_T]
  rw [map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X, map_mul,
    reciprocal_C, reciprocal_T, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]

end FLT.Mazur.PolygonScaledReciprocal
