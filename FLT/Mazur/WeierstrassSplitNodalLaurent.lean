/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalChart

/-!
# The split nodal infinity chart is the Laurent algebra

The coordinate t=1+aX has inverse given by the cubic relation. Conversely
X=a⁻¹(t-1) and Z=X³t⁻¹ give a normalized solution. These are inverse algebra
maps on the actual chart, over any coefficient ring and any unit a.
-/

@[expose] public noncomputable section

open scoped LaurentPolynomial

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (a : Rˣ)

/-- The normalized X coordinate in Laurent coordinates. -/
def splitNodalLaurentX : R[T;T⁻¹] :=
  algebraMap R _ (↑(a⁻¹) : R) * (LaurentPolynomial.T 1 - 1)

/-- The normalized Z coordinate in Laurent coordinates. -/
def splitNodalLaurentZ : R[T;T⁻¹] :=
  splitNodalLaurentX a ^ 3 * LaurentPolynomial.T (-1)

/-- The chosen Laurent X coordinate recovers t as the tangent factor. -/
theorem splitNodalLaurent_tangent :
    1 + algebraMap R R[T;T⁻¹] a * splitNodalLaurentX a = LaurentPolynomial.T 1 := by
  rw [splitNodalLaurentX, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
  ring

/-- The Laurent coordinates satisfy the normalized nodal equation. -/
theorem splitNodalLaurent_relation :
    splitNodalLaurentZ a * (1 + algebraMap R _ a * splitNodalLaurentX a) =
      splitNodalLaurentX a ^ 3 := by
  rw [splitNodalLaurent_tangent, splitNodalLaurentZ, mul_assoc,
    ← LaurentPolynomial.T_add]
  simp

/-- Evaluation gives an actual map from the original chart to the Laurent algebra. -/
def splitNodalChartToLaurent : Coordinate (splitNodalEquation a) 1 →ₐ[R] R[T;T⁻¹] :=
  evaluation (splitNodalEquation a) 1 ![splitNodalLaurentX a, 1, splitNodalLaurentZ a]
    (by
      rw [WeierstrassCurve.Projective.equation_iff]
      simp only [splitNodalEquation, WeierstrassCurve.map, WeierstrassCurve.toProjective,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, map_zero,
        one_pow, one_mul, mul_one, zero_mul, add_zero]
      change splitNodalLaurentZ a + algebraMap R _ a * splitNodalLaurentX a *
        splitNodalLaurentZ a - splitNodalLaurentX a ^ 3 = 0
      linear_combination splitNodalLaurent_relation a) rfl

/-- The forward map has precisely the displayed normalized coordinates. -/
@[simp] theorem splitNodalChartToLaurent_coord (i : Fin 3) :
    splitNodalChartToLaurent a (coord (splitNodalEquation a) 1 i) =
      ![splitNodalLaurentX a, 1, splitNodalLaurentZ a] i :=
  evaluation_coord _ _ _ _ _ i

/-- The tangent factor maps to the positive Laurent generator. -/
theorem splitNodalChartToLaurent_tangent :
    splitNodalChartToLaurent a
      (1 + algebraMap R _ a * coord (splitNodalEquation a) 1 0) = LaurentPolynomial.T 1 := by
  simpa only [map_add, map_one, map_mul, AlgHom.commutes, splitNodalChartToLaurent_coord,
    Matrix.cons_val_zero] using splitNodalLaurent_tangent a

/-- The polynomial inverse maps to the negative Laurent generator. -/
theorem splitNodalChartToLaurent_inverse :
    splitNodalChartToLaurent a (splitNodalTangentInverse a) = LaurentPolynomial.T (-1) := by
  apply (IsUnit.mul_right_inj (LaurentPolynomial.isUnit_T (R := R) 1)).mp
  rw [← splitNodalChartToLaurent_tangent, ← map_mul, splitNodalTangent_mul_inverse, map_one,
    splitNodalChartToLaurent_tangent, ← LaurentPolynomial.T_add]
  simp

/-- The Laurent-to-chart map recovers X. -/
theorem splitNodalLaurentToChart_x :
    splitNodalLaurentToChart a (splitNodalLaurentX a) = coord (splitNodalEquation a) 1 0 := by
  simpa only [splitNodalLaurentX, map_mul, AlgHom.commutes, map_sub, map_one,
    splitNodalLaurentToChart_pos] using splitNodalChart_x_recovery a

/-- The Laurent-to-chart map recovers Z. -/
theorem splitNodalLaurentToChart_z :
    splitNodalLaurentToChart a (splitNodalLaurentZ a) = coord (splitNodalEquation a) 1 2 := by
  rw [splitNodalLaurentZ, map_mul, map_pow, splitNodalLaurentToChart_x,
    splitNodalLaurentToChart_neg, splitNodalChart_z_recovery]

/-- The two explicit maps compose to the identity on the actual cubic chart. -/
theorem splitNodalLaurentToChart_comp :
    (splitNodalLaurentToChart a).comp (splitNodalChartToLaurent a) = AlgHom.id R _ := by
  apply hom_ext
  intro i
  fin_cases i <;> simp [AlgHom.comp_apply, splitNodalLaurentToChart_x,
    splitNodalLaurentToChart_z]

/-- The two explicit maps also compose to the identity on the Laurent algebra. -/
theorem splitNodalChartToLaurent_comp :
    (splitNodalChartToLaurent a).comp (splitNodalLaurentToChart a) = AlgHom.id R _ := by
  apply LaurentUnitPoints.hom_ext
  · simp [AlgHom.comp_apply, splitNodalChartToLaurent_tangent]
  · simp [AlgHom.comp_apply, splitNodalChartToLaurent_inverse]

/-- The original infinity chart is explicitly the multiplicative group's coordinate algebra. -/
def splitNodalChartLaurentEquiv : Coordinate (splitNodalEquation a) 1 ≃ₐ[R] R[T;T⁻¹] :=
  AlgEquiv.ofAlgHom (splitNodalChartToLaurent a) (splitNodalLaurentToChart a)
    (splitNodalChartToLaurent_comp a) (splitNodalLaurentToChart_comp a)

end FLT.Mazur.WeierstrassIntegralChart
