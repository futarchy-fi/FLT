/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingBoundaryLift
public import FLT.Mazur.PolygonScaledReciprocal

/-!
# A necessary weight equation from the actual two Laurent boundaries

A single coefficient equation already constrains both branch weights.
The hypotheses concern full weighted Laurent values; no polynomial form
of a hypothetical node endomorphism is assumed.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial PolygonScaledReciprocal
variable {R : Type*} [CommRing R] (t : R)
local notation "L" => R[T;T⁻¹]

/-- Multiplication by a Laurent constant multiplies every coefficient. -/
theorem laurent_constant_mul_coeff (r : R) (z : L) (k : ℤ) :
    (C r * z).coeff k = r * z.coeff k := by
  simp only [← smul_eq_C_mul, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]

/-- The coefficient of a Laurent monomial at its own exponent is its coefficient. -/
theorem laurent_monomial_coeff_self (r : R) (k : ℤ) :
    (C r * T k).coeff k = r := by
  rw [← single_eq_C_mul_T]
  exact Finsupp.single_eq_same

/-- Both prescribed boundaries force the product weight even for arbitrary nonlinear maps. -/
theorem boundary_weight_constraint (f g : L →ₐ[R] L) (a b : Rˣ)
    (hf : C t * f (T 1) = C t * scaling a (T 1))
    (hg : C t * g (T (-1)) = C t * scaling b (T (-1)))
    (h : LaurentCompatible t (f (leftLaurentMap t (leftCoordinate t)))
      (invert (g (((leftLaurentMap t).comp (branchSwapMap t)) (leftCoordinate t))))) :
    (a : R) * (b : R) * t = t := by
  have hp := congrArg (fun z : L ↦ z.coeff 1) hf
  have hq := congrArg (fun z : L ↦ z.coeff (-1)) hg
  change (C t * f (T 1)).coeff 1 =
    (C t * PolygonChartScaling.laurent a (T 1)).coeff 1 at hp
  change (C t * g (T (-1))).coeff (-1) =
    (C t * PolygonChartScaling.laurent b (T (-1))).coeff (-1) at hq
  rw [PolygonChartScaling.laurent_T_one, ← mul_assoc, ← map_mul,
    laurent_monomial_coeff_self, laurent_constant_mul_coeff] at hp
  rw [PolygonChartScaling.laurent_T_neg_one, ← mul_assoc, ← map_mul,
    laurent_monomial_coeff_self, laurent_constant_mul_coeff] at hq
  have hc := h.1 1
  simp only [Nat.cast_one, pow_one, leftLaurentMap_left, AlgHom.comp_apply,
    branchSwapMap_left, leftLaurentMap_right, invert_apply] at hc
  rw [map_mul, show g (C t) = C t from g.commutes t,
    laurent_constant_mul_coeff] at hc
  have he : t * (a : R) = t * (↑b⁻¹ : R) := hp.symm.trans (hc.symm.trans hq)
  have hb := congrArg (fun r : R ↦ r * (b : R)) he
  rw [mul_assoc t (↑b⁻¹ : R), Units.inv_mul, mul_one] at hb
  exact (by ring : (a : R) * (b : R) * t = t * (a : R) * (b : R)).trans hb

end FLT.Mazur.PolygonSmoothing
