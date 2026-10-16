/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentBoundaryVectorField
public import FLT.Mazur.PolygonStageTopScalar
public import FLT.Mazur.LaurentCoefficientEvaluation

/-!
# Boundary rigidity at every top smoothing layer

Polynomial extensions fixing both boundary origins force a top-weight
Laurent vector field to be a scaling. Normalization at the marked unit
kills that scaling, with faithful coefficients over arbitrary base rings.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial Polynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial LaurentBoundaryVectorField PolygonScalingNaturality
open LaurentCoefficientEvaluation
variable {R : Type*} [CommRing R] (m : ℕ)

/-- The original Laurent coordinate plus a vector field in the top smoothing layer. -/
def topOrderLaurentCoordinate (q : R[T;T⁻¹]) : (Ring R m)[T;T⁻¹] :=
  T 1 + C (parameter R m ^ m) * coeffMap (algebraMap R (Ring R m)) q

/-- Every coefficient of this coordinate retains its precise top smoothing coefficient. -/
theorem topOrderLaurentCoordinate_coeff (q : R[T;T⁻¹]) (d : ℤ) :
    (topOrderLaurentCoordinate m q).coeff d =
      (T 1 : (Ring R m)[T;T⁻¹]).coeff d +
        parameter R m ^ m * algebraMap R (Ring R m) (q.coeff d) := by
  simp only [topOrderLaurentCoordinate, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    ← smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, coeffMap_coeff]

/-- A polynomial extension fixing its origin kills every nonpositive vector-field coefficient. -/
theorem topOrderLaurentCoordinate_boundary_coeff (q : R[T;T⁻¹])
    (p : (Ring R m)[X]) (hp : Polynomial.toLaurent p = topOrderLaurentCoordinate m q)
    (hp0 : p.coeff 0 = 0) (d : ℤ) (hd : d ≤ 0) : q.coeff d = 0 := by
  have hz : (Polynomial.toLaurent p).coeff d = 0 := by
    rcases lt_or_eq_of_le hd with hd | rfl
    · exact polynomial_coeff_neg p d hd
    · rw [polynomial_coeff_zero, hp0]
  rw [hp, topOrderLaurentCoordinate_coeff, T_apply,
    ite_eq_right (show (1 : ℤ) ≠ d by omega), zero_add] at hz
  apply parameter_top_scalar_injective R m
  simpa only [map_zero, mul_zero] using hz

/-- Actual polynomial extensions on both charts force the top-weight field to be a scaling. -/
theorem topOrderLaurentCoordinate_boundary_scaling (q : R[T;T⁻¹])
    (p r : (Ring R m)[X])
    (hp : Polynomial.toLaurent p = topOrderLaurentCoordinate m q)
    (hr : Polynomial.toLaurent r = topOrderLaurentCoordinate m (reciprocalField q))
    (hp0 : p.coeff 0 = 0) (hr0 : r.coeff 0 = 0) : q = C (q.coeff 1) * T 1 := by
  ext d
  rw [← single_eq_C_mul_T]
  change q.coeff d = Finsupp.single 1 (q.coeff 1) d
  by_cases hd : d = 1
  · subst d
    simp
  · rw [Finsupp.single_eq_of_ne hd]
    by_cases hlow : d ≤ 0
    · exact topOrderLaurentCoordinate_boundary_coeff m q p hp hp0 d hlow
    · have he := topOrderLaurentCoordinate_boundary_coeff m
        (reciprocalField q) r hr hr0 (2 - d) (by omega)
      simpa only [reciprocalField_coeff, sub_sub_cancel, neg_eq_zero] using he

/-- Fixing the marked unit removes the remaining scaling coefficient. -/
theorem topOrderLaurentCoordinate_boundary_rigid (q : R[T;T⁻¹])
    (p r : (Ring R m)[X])
    (hp : Polynomial.toLaurent p = topOrderLaurentCoordinate m q)
    (hr : Polynomial.toLaurent r = topOrderLaurentCoordinate m (reciprocalField q))
    (hp0 : p.coeff 0 = 0) (hr0 : r.coeff 0 = 0)
    (h1 : eval₂ (RingHom.id R) (1 : Rˣ) q = 0) : q = 0 := by
  have he := topOrderLaurentCoordinate_boundary_scaling m q p r hp hr hp0 hr0
  have hh := congrArg (eval₂ (RingHom.id R) (1 : Rˣ)) he
  simp only [map_mul, eval₂_C, RingHom.id_apply, eval₂_T,
    one_zpow, Units.val_one, mul_one] at hh
  rw [he, hh.symm.trans h1, map_zero, zero_mul]

end FLT.Mazur.PolygonInfinitesimalStages
