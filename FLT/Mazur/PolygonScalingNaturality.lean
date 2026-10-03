/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonChartScaling

/-!
# Naturality of polygon chart scaling

Scaling commutes with coefficient maps between arbitrary commutative rings.
The Laurent identities also give multiplication and identity laws on overlaps.
These are coordinate identities, not geometric base-change identifications.
-/

@[expose] public noncomputable section

open scoped Polynomial LaurentPolynomial

namespace FLT.Mazur.PolygonScalingNaturality

open PolygonChartScaling

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Ring maps on Laurent polynomials are determined by constants and inverse generators. -/
theorem ringHom_ext {f g : R[T;T⁻¹] →+* S}
    (hC : ∀ r, f (LaurentPolynomial.C r) = g (LaurentPolynomial.C r))
    (hp : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1))
    (hn : f (LaurentPolynomial.T (-1)) = g (LaurentPolynomial.T (-1))) : f = g := by
  apply RingHom.ext
  intro p
  induction p using LaurentPolynomial.induction_on with
  | h_C r => exact hC r
  | h_add ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
  | h_C_mul_T n r ih =>
    rw [LaurentPolynomial.T_add, ← mul_assoc, map_mul, ih, hp]
    simp only [map_mul]
  | h_C_mul_T_Z n r ih =>
    rw [sub_eq_add_neg, LaurentPolynomial.T_add, ← mul_assoc, map_mul, ih, hn]
    simp only [map_mul]

/-- Affine scaling is natural in the coefficient ring. -/
theorem affine_natural (f : R →+* S) (a : Rˣ) :
    (Polynomial.mapRingHom f).comp (affine a) =
      (affine (Units.map f a)).comp (Polynomial.mapRingHom f) := by
  ext <;> simp

/-- Change coefficients without changing the Laurent coordinate. -/
def coeffMap (f : R →+* S) : R[T;T⁻¹] →+* S[T;T⁻¹] :=
  LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp f) (coordinateUnit (1 : Sˣ))

@[simp]
theorem coeffMap_C (f : R →+* S) (r : R) :
    coeffMap f (LaurentPolynomial.C r) = LaurentPolynomial.C (f r) := by
  simp [coeffMap]

@[simp]
theorem coeffMap_T_one (f : R →+* S) :
    coeffMap f (LaurentPolynomial.T 1) = LaurentPolynomial.T 1 := by
  simp [coeffMap, coordinateUnit]

@[simp]
theorem coeffMap_T_neg_one (f : R →+* S) :
    coeffMap f (LaurentPolynomial.T (-1)) = LaurentPolynomial.T (-1) := by
  simp [coeffMap, coordinateUnit]

/-- Laurent scaling is natural in the coefficient ring. -/
theorem laurent_natural (f : R →+* S) (a : Rˣ) :
    (coeffMap f).comp (laurent a) =
      (laurent (Units.map f a)).comp (coeffMap f) := by
  apply ringHom_ext <;> simp

@[simp]
theorem laurent_one : laurent (1 : Rˣ) = RingHom.id _ := by
  apply ringHom_ext <;> simp

/-- Successive overlap scalings multiply their parameters. -/
theorem laurent_mul (a b : Rˣ) : laurent (a * b) = (laurent a).comp (laurent b) := by
  apply ringHom_ext
  · intro r; simp
  · simp only [laurent_T_one, RingHom.comp_apply, map_mul, laurent_C, Units.val_mul]
    ac_rfl
  · simp only [laurent_T_neg_one, RingHom.comp_apply, map_mul, laurent_C,
      mul_inv_rev, Units.val_mul]
    ac_rfl

/-- Coefficient maps agree with polynomial coefficient maps on the affine chart. -/
theorem coeffMap_toLaurent (f : R →+* S) :
    (coeffMap f).comp Polynomial.toLaurent =
      Polynomial.toLaurent.comp (Polynomial.mapRingHom f) := by
  ext <;> simp

@[simp]
theorem coeffMap_id : coeffMap (RingHom.id R) = RingHom.id _ := by
  apply ringHom_ext <;> simp

/-- Laurent coefficient change respects composition. -/
theorem coeffMap_comp {T : Type*} [CommRing T] (g : S →+* T) (f : R →+* S) :
    coeffMap (g.comp f) = (coeffMap g).comp (coeffMap f) := by
  apply ringHom_ext <;> simp

end FLT.Mazur.PolygonScalingNaturality
