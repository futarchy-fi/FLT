/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberConic
public import FLT.Mazur.WeierstrassSuccessiveXMonic

/-!
# Regularity of the original incidence coordinate on the conic

The conic is monic in its slope over the polynomial incidence line. Hence
its incidence coordinate is regular over every coefficient ring, including
when the residual conic splits.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c : R)

/-- The conic equation is monic in the slope over the original incidence line. -/
theorem conicPolynomial_monic : (conicPolynomial a c).Monic := by
  have h : conicPolynomial a c =
      Cubic.toPoly ⟨0, 1, C a, -(C c * X ^ 2)⟩ := by
    simp only [conicPolynomial, Cubic.toPoly, C_0, C_1, C_neg,
      zero_mul, one_mul, zero_add]
    ring
  rw [h]
  exact Cubic.monic_of_b_eq_one'

/-- The conic algebra is free over its incidence-coordinate polynomial ring. -/
instance conicCoordinate_free : Module.Free R[X] (ConicCoordinate a c) :=
  (conicPolynomial_monic a c).free_adjoinRoot

/-- The retained conic incidence function is regular without a domain hypothesis. -/
theorem conicT_regular : IsRegular (conicT a c) :=
  WeierstrassIntegralChart.flatRingHom_isRegular _
    (RingHom.flat_algebraMap_iff.mpr inferInstance) Polynomial.isRegular_X

end FLT.Mazur.WeierstrassModificationX
