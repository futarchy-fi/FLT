/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonChartScaling

/-!
# Scaling with a variable unit parameter

The outer Laurent coordinate supplies the parameter. The inner polynomial
or Laurent coordinate is the chart coordinate; only this inner coordinate
is inverted in the transition between charts.
-/

@[expose] public noncomputable section

open scoped Polynomial LaurentPolynomial

namespace FLT.Mazur.PolygonUniversalScaling

variable {R : Type*} [CommRing R]

/-- The universal unit parameter. -/
def u : R[T;T⁻¹]ˣ := PolygonChartScaling.coordinateUnit (1 : Rˣ)

/-- Scale the first chart by the universal parameter. -/
def scaleLeft : R[X] →+* R[T;T⁻¹][X] :=
  (PolygonChartScaling.affine (u (R := R))).comp
    (Polynomial.mapRingHom LaurentPolynomial.C)

/-- Scale the second chart by the inverse universal parameter. -/
def scaleRight : R[X] →+* R[T;T⁻¹][X] :=
  (PolygonChartScaling.affine (u (R := R))⁻¹).comp
    (Polynomial.mapRingHom LaurentPolynomial.C)

/-- Specialize the parameter, leaving the chart coordinate unchanged. -/
def specialize (a : Rˣ) : R[T;T⁻¹][X] →+* R[X] :=
  Polynomial.mapRingHom (LaurentPolynomial.eval₂ (RingHom.id R) a)

@[simp]
theorem specialize_u (a : Rˣ) :
    LaurentPolynomial.eval₂ (RingHom.id R) a (u (R := R) : R[T;T⁻¹]) = a := by
  simp [u, PolygonChartScaling.coordinateUnit]

@[simp]
theorem specialize_u_inv (a : Rˣ) :
    LaurentPolynomial.eval₂ (RingHom.id R) a (↑(u (R := R))⁻¹ : R[T;T⁻¹]) =
      (↑a⁻¹ : R) := by
  simp [u, PolygonChartScaling.coordinateUnit]

/-- The universal first-chart map recovers each constant scaling. -/
theorem specialize_left (a : Rˣ) :
    (specialize a).comp scaleLeft = PolygonChartScaling.affine a := by
  ext <;> simp [specialize, scaleLeft]

/-- The universal second-chart map recovers inverse scaling. -/
theorem specialize_right (a : Rˣ) :
    (specialize a).comp scaleRight = PolygonChartScaling.affine a⁻¹ := by
  ext <;> simp [specialize, scaleRight]

/-- The common scaling map on the punctured chart. -/
def overlapScale : R[T;T⁻¹] →+* R[T;T⁻¹][T;T⁻¹] :=
  LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp LaurentPolynomial.C)
    (PolygonChartScaling.coordinateUnit (u (R := R)))

@[simp]
theorem overlapScale_C (r : R) :
    overlapScale (LaurentPolynomial.C r) =
      LaurentPolynomial.C (LaurentPolynomial.C r) := by
  simp [overlapScale]

@[simp]
theorem overlapScale_T_one :
    overlapScale (LaurentPolynomial.T 1 : R[T;T⁻¹]) =
      LaurentPolynomial.C (u (R := R) : R[T;T⁻¹]) * LaurentPolynomial.T 1 := by
  simp [overlapScale, PolygonChartScaling.coordinateUnit]

@[simp]
theorem overlapScale_T_neg_one :
    overlapScale (LaurentPolynomial.T (-1) : R[T;T⁻¹]) =
      LaurentPolynomial.C (↑(u (R := R))⁻¹ : R[T;T⁻¹]) * LaurentPolynomial.T (-1) := by
  simp [overlapScale, PolygonChartScaling.coordinateUnit]

/-- Restriction of the first scaling agrees with the common overlap map. -/
theorem overlap_left :
    Polynomial.toLaurent.comp (scaleLeft (R := R)) =
      overlapScale.comp Polynomial.toLaurent := by
  ext <;> simp [scaleLeft]

/-- The transition inverts the chart coordinate while fixing the parameter. -/
theorem overlap_right :
    LaurentPolynomial.invert.toRingHom.comp
        (Polynomial.toLaurent.comp (scaleRight (R := R))) =
      overlapScale.comp
        (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent) := by
  ext <;> simp [scaleRight]

/-- The first endpoint is fixed over the parameter ring. -/
theorem scaleLeft_zero :
    (Polynomial.evalRingHom 0).comp (scaleLeft (R := R)) =
      LaurentPolynomial.C.comp (Polynomial.evalRingHom 0) := by
  ext <;> simp [scaleLeft]

/-- The second endpoint is fixed over the parameter ring. -/
theorem scaleRight_zero :
    (Polynomial.evalRingHom 0).comp (scaleRight (R := R)) =
      LaurentPolynomial.C.comp (Polynomial.evalRingHom 0) := by
  ext <;> simp [scaleRight]

end FLT.Mazur.PolygonUniversalScaling
