/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodeLocalization
public import FLT.Mazur.PolygonScalingNaturality
public import FLT.Mazur.PolygonUniversalScaling

/-!
# Reciprocal scaling on the node algebra

The two branches scale by reciprocal units. Equality of endpoint values is
preserved, giving node endomorphisms natural in the coefficient ring. The
universal parameter produces a map to the node over the Laurent ring; no
identification with a tensor product or a scheme action is assumed.
-/

@[expose] public noncomputable section

open scoped Polynomial LaurentPolynomial

namespace FLT.Mazur.PolygonNodeScaling

open PolygonNodeEqualizer PolygonChartScaling PolygonScalingNaturality

variable {R S : Type*} [CommRing R] [CommRing S]

@[simp]
theorem eval_zero_affine (a : Rˣ) (p : R[X]) : (affine a p).eval 0 = p.eval 0 :=
  RingHom.congr_fun (affine_zero a) p

/-- Reciprocal scaling preserves the matching endpoint values. -/
def scaling (a : Rˣ) : A (R := R) →+* A (R := R) where
  toFun p := ⟨(affine a p.val.1, affine a⁻¹ p.val.2), by
    simpa only [mem_A, eval_zero_affine] using p.property⟩
  map_one' := by apply Subtype.ext; ext <;> simp
  map_mul' p q := by apply Subtype.ext; ext <;> simp
  map_zero' := by apply Subtype.ext; ext <;> simp
  map_add' p q := by apply Subtype.ext; ext <;> simp

@[simp]
theorem first_scaling (a : Rˣ) (p : A (R := R)) :
    first (scaling a p) = affine a (first p) := rfl

@[simp]
theorem second_scaling (a : Rˣ) (p : A (R := R)) :
    second (scaling a p) = affine a⁻¹ (second p) := rfl

/-- The value at the node is fixed by scaling. -/
theorem origin_scaling (a : Rˣ) (p : A (R := R)) :
    (first (scaling a p)).eval 0 = (first p).eval 0 := by simp

@[simp]
theorem scaling_one : scaling (1 : Rˣ) = RingHom.id _ := by
  ext p : 1
  apply Subtype.ext
  simp [scaling]

/-- Multiplication of parameters agrees with composition on node functions. -/
theorem scaling_mul (a b : Rˣ) : scaling (a * b) = (scaling a).comp (scaling b) := by
  ext p : 1
  apply Subtype.ext
  dsimp [scaling]
  rw [affine_mul, mul_inv_rev, mul_comm b⁻¹ a⁻¹, affine_mul]
  rfl

/-- Scaling is invertible, including over rings with nilpotents. -/
def scalingEquiv (a : Rˣ) : A (R := R) ≃+* A (R := R) where
  __ := scaling a
  invFun := scaling a⁻¹
  left_inv p := by
    have h := RingHom.congr_fun (scaling_mul a⁻¹ a) p
    simpa using h.symm
  right_inv p := by
    have h := RingHom.congr_fun (scaling_mul a a⁻¹) p
    simpa using h.symm

/-- Apply a coefficient map on both branches. -/
def map (f : R →+* S) : A (R := R) →+* A (R := S) where
  toFun p := ⟨(Polynomial.map f p.val.1, Polynomial.map f p.val.2), by
    rw [mem_A]
    simpa using congrArg f ((mem_A _).mp p.property)⟩
  map_one' := by apply Subtype.ext; ext <;> simp
  map_mul' p q := by apply Subtype.ext; ext <;> simp
  map_zero' := by apply Subtype.ext; ext <;> simp
  map_add' p q := by apply Subtype.ext; ext <;> simp

@[simp]
theorem first_map (f : R →+* S) (p : A (R := R)) :
    first (map f p) = Polynomial.map f (first p) := rfl

@[simp]
theorem second_map (f : R →+* S) (p : A (R := R)) :
    second (map f p) = Polynomial.map f (second p) := rfl

/-- Node scaling commutes with arbitrary coefficient maps. -/
theorem map_scaling (f : R →+* S) (a : Rˣ) :
    (map f).comp (scaling a) = (scaling (Units.map f a)).comp (map f) := by
  ext p : 1
  apply Subtype.ext
  apply Prod.ext
  · exact RingHom.congr_fun (affine_natural f a) p.val.1
  · change Polynomial.map f (affine a⁻¹ p.val.2) =
      affine ((Units.map f a)⁻¹) (Polynomial.map f p.val.2)
    rw [← map_inv]
    exact RingHom.congr_fun (affine_natural f a⁻¹) p.val.2

/-- Scaling on the first punctured branch is Laurent scaling by the same unit. -/
theorem leftMap_scaling (a : Rˣ) :
    PolygonNodeLocalization.leftMap.comp (scaling a) =
      (laurent a).comp PolygonNodeLocalization.leftMap := by
  ext p : 1
  exact RingHom.congr_fun (toLaurent_affine a) (first p)

/-- Scaling on the second punctured branch uses the inverse unit. -/
theorem rightMap_scaling (a : Rˣ) :
    PolygonNodeLocalization.rightMap.comp (scaling a) =
      (laurent a⁻¹).comp PolygonNodeLocalization.rightMap := by
  ext p : 1
  exact RingHom.congr_fun (toLaurent_affine a⁻¹) (second p)

/-- Node scaling with the universal Laurent unit as parameter. -/
def universal : A (R := R) →+* A (R := R[T;T⁻¹]) :=
  (scaling (PolygonUniversalScaling.u (R := R))).comp (map LaurentPolynomial.C)

/-- Restriction of universal node scaling to the first normalization branch. -/
theorem first_universal :
    first.toRingHom.comp (universal (R := R)) =
      PolygonUniversalScaling.scaleLeft.comp first.toRingHom := rfl

/-- Restriction of universal node scaling to the second normalization branch. -/
theorem second_universal :
    second.toRingHom.comp (universal (R := R)) =
      PolygonUniversalScaling.scaleRight.comp second.toRingHom := rfl

end FLT.Mazur.PolygonNodeScaling
