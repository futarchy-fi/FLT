/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentCocycleCoefficientRecovery
public import FLT.Mazur.LaurentPositivePart
public import FLT.Mazur.LaurentCoefficientEvaluation

/-!
# Boundary coefficients of a multiplicative Laurent coboundary

The mixed coefficient at inner exponent one and outer exponent d recovers
the original coordinate correction at d, whenever d differs from one.
Thus boundary support of the actual multiplication error controls the
coordinate correction without constructing a coordinate conjugacy at a node.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentCoboundaryBoundary
open LaurentPolynomial PolygonChartScaling PolygonScalingNaturality
open LaurentScaledEvaluationCoefficients LaurentPositivePart LaurentCoefficientEvaluation
variable {R : Type*} [CommRing R]

/-- The full two-variable coboundary in the original independent Laurent variables. -/
def coboundary (q : R[T;T⁻¹]) : R[T;T⁻¹][T;T⁻¹] :=
  C (T 1) * coeffMap C q + C q * T 1 -
    eval₂ (C.comp C) (coordinateUnit (coordinateUnit (1 : Rˣ))) q

/-- Away from exponent one, the outer coefficient keeps both original monomials. -/
theorem coboundary_coeff (q : R[T;T⁻¹]) (d : ℤ) (hd : d ≠ 1) :
    (coboundary q).coeff d = T 1 * C (q.coeff d) - C (q.coeff d) * T d := by
  simp only [coboundary, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ← smul_eq_C_mul,
    AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, coeffMap_coeff,
    T_apply, ite_eq_right (Ne.symm hd), mul_zero, add_zero,
    eval₂_scaled_coeff, coordinate_one_zpow]

/-- A single mixed coefficient recovers every non-scaling coefficient of the correction. -/
theorem coboundary_coeff_one (q : R[T;T⁻¹]) (d : ℤ) (hd : d ≠ 1) :
    ((coboundary q).coeff d).coeff 1 = q.coeff d := by
  rw [coboundary_coeff q d hd, mul_comm (T 1)]
  simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, ← smul_eq_C_mul,
    AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, T_apply, ite_true,
    ite_eq_right hd, mul_one, mul_zero, sub_zero]

/-- A polynomial boundary for the original error kills the correction's nonpositive tail. -/
theorem boundaryTail_eq_zero_of_coboundary (q : R[T;T⁻¹])
    (h : ∀ d : ℤ, d ≤ 0 → (coboundary q).coeff d = 0) : boundaryTail q = 0 := by
  apply (boundaryTail_eq_zero_iff q).mpr
  intro d hd
  rw [← coboundary_coeff_one q d (by omega), h d hd]
  rfl

/-- The opposite boundary support kills every coefficient above the scaling degree. -/
theorem high_coeff_eq_zero_of_coboundary (q : R[T;T⁻¹])
    (h : ∀ d : ℤ, 2 ≤ d → (coboundary q).coeff d = 0) (d : ℤ) (hd : 2 ≤ d) :
    q.coeff d = 0 := by
  rw [← coboundary_coeff_one q d (by omega), h d hd]
  rfl

/-- Both boundary tails of the correction follow from support of the original error. -/
theorem reciprocal_boundaryTail_eq_zero_of_coboundary (q : R[T;T⁻¹])
    (h : ∀ d : ℤ, 2 ≤ d → (coboundary q).coeff d = 0) :
    boundaryTail (LaurentBoundaryVectorField.reciprocalField q) = 0 := by
  apply (boundaryTail_eq_zero_iff _).mpr
  intro d hd
  rw [LaurentBoundaryVectorField.reciprocalField_coeff,
    high_coeff_eq_zero_of_coboundary q h (2 - d) (by omega), neg_zero]

end FLT.Mazur.LaurentCoboundaryBoundary
