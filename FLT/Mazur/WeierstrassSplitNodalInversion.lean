/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalLaurent
public import FLT.Mazur.WeierstrassInfinityNegationChart

/-!
# Laurent inversion is normalized homogeneous negation

Inverting the tangent parameter rescales X and Z by -t⁻¹. The homogeneous
negated Y coordinate is -t, so these are exactly the original normalized
negation formulas on the split nodal chart.
-/

@[expose] public noncomputable section

open scoped LaurentPolynomial

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (a : Rˣ)

/-- Inversion of the Laurent parameter gives the normalized negated X coordinate. -/
theorem splitNodalLaurentX_invert :
    LaurentPolynomial.invert (splitNodalLaurentX a) =
      -LaurentPolynomial.T (-1) * splitNodalLaurentX a := by
  simp only [splitNodalLaurentX, map_mul, AlgEquiv.commutes, map_sub,
    LaurentPolynomial.invert_T, map_one]
  have h : (LaurentPolynomial.T (-1) : R[T;T⁻¹]) * LaurentPolynomial.T 1 = 1 := by
    rw [← LaurentPolynomial.T_add]; rfl
  linear_combination algebraMap R R[T;T⁻¹] (↑(a⁻¹) : R) * h

/-- Inversion gives the same normalization factor on the Z coordinate. -/
theorem splitNodalLaurentZ_invert :
    LaurentPolynomial.invert (splitNodalLaurentZ a) =
      -LaurentPolynomial.T (-1) * splitNodalLaurentZ a := by
  rw [splitNodalLaurentZ, map_mul, map_pow, splitNodalLaurentX_invert,
    LaurentPolynomial.invert_T, neg_neg]
  have h : (LaurentPolynomial.T (-1) : R[T;T⁻¹]) * LaurentPolynomial.T 1 = 1 := by
    rw [← LaurentPolynomial.T_add]; rfl
  linear_combination -splitNodalLaurentX a ^ 3 * LaurentPolynomial.T (-1) ^ 2 * h

/-- Homogeneous negation's output Y coordinate is minus the tangent parameter. -/
theorem splitNodalLaurent_negationDen :
    splitNodalChartToLaurent a (infinityNegationDen (splitNodalEquation a)) =
      -LaurentPolynomial.T 1 := by
  have ht := splitNodalLaurent_tangent a
  change 1 + algebraMap R R[T;T⁻¹] a * splitNodalLaurentX a = _ at ht
  simp only [infinityNegationDen, chartNegationCoordinates,
    WeierstrassCurve.Projective.negY, Matrix.cons_val_one,
    map_sub, map_neg, coord_self, map_one, map_mul,
    splitNodalChartToLaurent_coord, Matrix.cons_val_zero]
  change -1 - splitNodalChartToLaurent a (algebraMap R _ a) * splitNodalLaurentX a -
    splitNodalChartToLaurent a (algebraMap R _ 0) * splitNodalLaurentZ a = _
  rw [AlgHom.commutes, map_zero, map_zero, zero_mul, sub_zero]
  linear_combination -ht

/-- The homogeneous negation formulas are precisely Laurent inversion after normalization. -/
theorem splitNodalLaurent_negation_coord (i : Fin 3) :
    LaurentPolynomial.invert
        (splitNodalChartToLaurent a (coord (splitNodalEquation a) 1 i)) =
      -LaurentPolynomial.T (-1) *
        splitNodalChartToLaurent a (chartNegationCoordinates (splitNodalEquation a) 1 i) := by
  fin_cases i
  · change LaurentPolynomial.invert (splitNodalChartToLaurent a (coord _ 1 0)) =
      -LaurentPolynomial.T (-1) * splitNodalChartToLaurent a (coord _ 1 0)
    rw [splitNodalChartToLaurent_coord]
    exact splitNodalLaurentX_invert a
  · change LaurentPolynomial.invert
      (splitNodalChartToLaurent a (coord (splitNodalEquation a) 1 1)) =
        -LaurentPolynomial.T (-1) *
          splitNodalChartToLaurent a (infinityNegationDen (splitNodalEquation a))
    rw [coord_self, map_one, map_one, splitNodalLaurent_negationDen,
      neg_mul_neg, ← LaurentPolynomial.T_add]
    rfl
  · change LaurentPolynomial.invert (splitNodalChartToLaurent a (coord _ 1 2)) =
      -LaurentPolynomial.T (-1) * splitNodalChartToLaurent a (coord _ 1 2)
    rw [splitNodalChartToLaurent_coord]
    exact splitNodalLaurentZ_invert a

end FLT.Mazur.WeierstrassIntegralChart
