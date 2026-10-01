/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodeEqualizer
public import Mathlib.Algebra.Polynomial.Laurent

/-!
# Localizations of the two branches of an affine node

For polynomial pairs with equal values at zero, inverting `(X, 0)` gives the
Laurent ring of the first branch; inverting `(0, X)` gives the second branch.
These explicit localizations supply the open overlap maps for node charts.
-/

@[expose] public noncomputable section

open scoped Polynomial LaurentPolynomial

namespace FLT.Mazur.PolygonNodeLocalization

open PolygonNodeEqualizer

variable {R : Type*} [CommRing R]

/-- Coordinate on the first branch, zero on the second. -/
def x : A (R := R) := ⟨(Polynomial.X, 0), by simp⟩

/-- Coordinate on the second branch, zero on the first. -/
def y : A (R := R) := ⟨(0, Polynomial.X), by simp⟩

@[simp]
theorem first_x : first (x (R := R)) = Polynomial.X := rfl

@[simp]
theorem second_x : second (x (R := R)) = 0 := rfl

@[simp]
theorem first_y : first (y (R := R)) = 0 := rfl

@[simp]
theorem second_y : second (y (R := R)) = Polynomial.X := rfl

@[simp]
theorem x_mul_y : x (R := R) * y = 0 := by
  apply Subtype.ext
  exact Prod.ext (mul_zero _) (zero_mul _)

/-- Every function on the first branch extends by a constant on the other. -/
theorem first_surjective : Function.Surjective (first (R := R)) := by
  intro p
  exact ⟨⟨(p, Polynomial.C (p.eval 0)), by simp⟩, rfl⟩

/-- Every function on the second branch extends by a constant on the other. -/
theorem second_surjective : Function.Surjective (second (R := R)) := by
  intro p
  exact ⟨⟨(Polynomial.C (p.eval 0), p), by simp⟩, rfl⟩

/-- Restriction to the punctured first branch. -/
def leftMap : A (R := R) →+* R[T;T⁻¹] :=
  Polynomial.toLaurent.comp first.toRingHom

/-- Restriction to the punctured second branch. -/
def rightMap : A (R := R) →+* R[T;T⁻¹] :=
  Polynomial.toLaurent.comp second.toRingHom

@[simp]
theorem leftMap_apply (a : A (R := R)) : leftMap a = (first a).toLaurent := rfl

@[simp]
theorem rightMap_apply (a : A (R := R)) : rightMap a = (second a).toLaurent := rfl

theorem leftMap_x : leftMap (x (R := R)) = LaurentPolynomial.T 1 := by simp

theorem leftMap_y : leftMap (y (R := R)) = 0 := by simp

theorem rightMap_x : rightMap (x (R := R)) = 0 := by simp

theorem rightMap_y : rightMap (y (R := R)) = LaurentPolynomial.T 1 := by simp

/-- The first branch map is the localization at its branch coordinate. -/
theorem left_isLocalization :
    let := (leftMap (R := R)).toAlgebra
    IsLocalization.Away (x (R := R)) R[T;T⁻¹] := by
  let := (leftMap (R := R)).toAlgebra
  apply IsLocalization.Away.mk
  · change IsUnit (leftMap (x (R := R)))
    rw [leftMap_x]
    exact LaurentPolynomial.isUnit_T 1
  · intro z
    obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj (Polynomial.X : R[X]) z
    obtain ⟨a, rfl⟩ := first_surjective p
    refine ⟨n, a, ?_⟩
    simpa only [RingHom.algebraMap_toAlgebra, leftMap_x, leftMap_apply, first_x,
      LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_X] using hp
  · intro a b h
    change leftMap a = leftMap b at h
    have hab : first a = first b := Polynomial.toLaurent_injective h
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change Polynomial.X ^ 1 * first a = Polynomial.X ^ 1 * first b
      rw [hab]
    · change (0 : R[X]) ^ 1 * second a = 0 ^ 1 * second b
      simp

/-- The second branch map is the localization at its branch coordinate. -/
theorem right_isLocalization :
    let := (rightMap (R := R)).toAlgebra
    IsLocalization.Away (y (R := R)) R[T;T⁻¹] := by
  let := (rightMap (R := R)).toAlgebra
  apply IsLocalization.Away.mk
  · change IsUnit (rightMap (y (R := R)))
    rw [rightMap_y]
    exact LaurentPolynomial.isUnit_T 1
  · intro z
    obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj (Polynomial.X : R[X]) z
    obtain ⟨a, rfl⟩ := second_surjective p
    refine ⟨n, a, ?_⟩
    simpa only [RingHom.algebraMap_toAlgebra, rightMap_y, rightMap_apply, second_y,
      LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_X] using hp
  · intro a b h
    change rightMap a = rightMap b at h
    have hab : second a = second b := Polynomial.toLaurent_injective h
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change (0 : R[X]) ^ 1 * first a = 0 ^ 1 * first b
      simp
    · change Polynomial.X ^ 1 * second a = Polynomial.X ^ 1 * second b
      rw [hab]

end FLT.Mazur.PolygonNodeLocalization
