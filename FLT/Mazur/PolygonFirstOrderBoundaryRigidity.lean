/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentBoundaryVectorField
public import FLT.Mazur.PolygonStageCoefficientChange
public import FLT.Mazur.LaurentCoefficientEvaluation

/-!
# Boundary rigidity on the actual first smoothing stage

A normalized first-order Laurent coordinate is unchanged if its corrections
on both reciprocal charts extend to polynomial coordinates fixing their
origins. Faithful extraction of the smoothing coefficient retains all base
nilpotents. These are extension hypotheses, not asserted extensions.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial Polynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial LaurentBoundaryVectorField PolygonScalingNaturality
open LaurentCoefficientEvaluation
variable {R : Type*} [CommRing R]

/-- The original Laurent coordinate plus a vector field in the first smoothing layer. -/
def firstOrderLaurentCoordinate (q : R[T;T⁻¹]) : (Ring R 1)[T;T⁻¹] :=
  T 1 + C (parameter R 1) * coeffMap (algebraMap R (Ring R 1)) q

/-- Every coefficient of this coordinate retains its precise first smoothing coefficient. -/
theorem firstOrderLaurentCoordinate_coeff (q : R[T;T⁻¹]) (d : ℤ) :
    (firstOrderLaurentCoordinate q).coeff d =
      (T 1 : (Ring R 1)[T;T⁻¹]).coeff d +
        parameter R 1 * algebraMap R (Ring R 1) (q.coeff d) := by
  simp only [firstOrderLaurentCoordinate, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    ← smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, coeffMap_coeff]

/-- A polynomial extension fixing its origin kills every nonpositive vector-field coefficient. -/
theorem firstOrderLaurentCoordinate_boundary_coeff (q : R[T;T⁻¹])
    (p : (Ring R 1)[X]) (hp : Polynomial.toLaurent p = firstOrderLaurentCoordinate q)
    (hp0 : p.coeff 0 = 0) (d : ℤ) (hd : d ≤ 0) : q.coeff d = 0 := by
  have hz : (Polynomial.toLaurent p).coeff d = 0 := by
    rcases lt_or_eq_of_le hd with hd | rfl
    · exact polynomial_coeff_neg p d hd
    · rw [polynomial_coeff_zero, hp0]
  rw [hp, firstOrderLaurentCoordinate_coeff, T_apply,
    ite_eq_right (show (1 : ℤ) ≠ d by omega), zero_add] at hz
  apply parameter_scalar_one_injective (S := R)
  simpa only [map_zero, mul_zero] using hz

/-- Actual polynomial extensions on both charts force the first-order field to be a scaling. -/
theorem firstOrderLaurentCoordinate_boundary_scaling (q : R[T;T⁻¹])
    (p r : (Ring R 1)[X])
    (hp : Polynomial.toLaurent p = firstOrderLaurentCoordinate q)
    (hr : Polynomial.toLaurent r = firstOrderLaurentCoordinate (reciprocalField q))
    (hp0 : p.coeff 0 = 0) (hr0 : r.coeff 0 = 0) : q = C (q.coeff 1) * T 1 := by
  ext d
  rw [← single_eq_C_mul_T]
  change q.coeff d = Finsupp.single 1 (q.coeff 1) d
  by_cases hd : d = 1
  · subst d
    simp
  · rw [Finsupp.single_eq_of_ne hd]
    by_cases hlow : d ≤ 0
    · exact firstOrderLaurentCoordinate_boundary_coeff q p hp hp0 d hlow
    · have he := firstOrderLaurentCoordinate_boundary_coeff
        (reciprocalField q) r hr hr0 (2 - d) (by omega)
      simpa only [reciprocalField_coeff, sub_sub_cancel, neg_eq_zero] using he

/-- Fixing the marked unit removes the remaining scaling coefficient. -/
theorem firstOrderLaurentCoordinate_boundary_rigid (q : R[T;T⁻¹])
    (p r : (Ring R 1)[X])
    (hp : Polynomial.toLaurent p = firstOrderLaurentCoordinate q)
    (hr : Polynomial.toLaurent r = firstOrderLaurentCoordinate (reciprocalField q))
    (hp0 : p.coeff 0 = 0) (hr0 : r.coeff 0 = 0)
    (h1 : eval₂ (RingHom.id R) (1 : Rˣ) q = 0) : q = 0 := by
  have he := firstOrderLaurentCoordinate_boundary_scaling q p r hp hr hp0 hr0
  have hh := congrArg (eval₂ (RingHom.id R) (1 : Rˣ)) he
  simp only [map_mul, eval₂_C, RingHom.id_apply, eval₂_T,
    one_zpow, Units.val_one, mul_one] at hh
  rw [he, hh.symm.trans h1, map_zero, zero_mul]

end FLT.Mazur.PolygonInfinitesimalStages
