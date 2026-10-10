/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassAffineMonicComparison

/-!
# Unique polynomial normal forms on the original affine chart

Every actual affine function has a unique expression p(x) + q(x)y over the
original coefficient ring. This is the algebraic input for the pole filtration
used to classify origin-preserving automorphisms.
-/

@[expose] public noncomputable section

open Polynomial WeierstrassCurve
open scoped Polynomial.Bivariate

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Evaluate a polynomial pair on the original affine chart. -/
def affineNormalForm (p q : R[X]) : Coordinate W 2 :=
  aeval (coord W 2 0) p + aeval (coord W 2 0) q * coord W 2 1

/-- The monic comparison identifies normal form with its actual two basis coefficients. -/
theorem affineNormalForm_monic (p q : R[X]) :
    affineChartMonicEquiv W (affineNormalForm W p q) =
      p • (1 : W.toAffine.CoordinateRing) +
        q • Affine.CoordinateRing.mk W.toAffine Y := by
  have hp (s : R[X]) : affineChartMonicEquiv W (aeval (coord W 2 0) s) =
      algebraMap R[X] W.toAffine.CoordinateRing s := by
    have he : (affineChartMonicEquiv W).toAlgHom.comp (aeval (coord W 2 0)) =
        IsScalarTower.toAlgHom R R[X] W.toAffine.CoordinateRing := by
      apply Polynomial.algHom_ext
      simp [affineChartMonicEquiv, affineChartToMonic]
    exact DFunLike.congr_fun he s
  have hy : affineChartMonicEquiv W (coord W 2 1) =
      Affine.CoordinateRing.mk W.toAffine Y := by
    simp [affineChartMonicEquiv, affineChartToMonic, Affine.CoordinateRing.mk]
  simp only [affineNormalForm, map_add, map_mul, hp, hy, Algebra.smul_def, mul_one]

/-- Every function of the actual affine chart has a polynomial normal form. -/
theorem exists_affineNormalForm (a : Coordinate W 2) :
    ∃ p q : R[X], affineNormalForm W p q = a := by
  obtain ⟨p, q, h⟩ := Affine.CoordinateRing.exists_smul_basis_eq (affineChartMonicEquiv W a)
  exact ⟨p, q, (affineChartMonicEquiv W).injective ((affineNormalForm_monic W p q).trans h)⟩

/-- The actual affine function is zero exactly when both polynomial coefficients vanish. -/
theorem affineNormalForm_eq_zero (p q : R[X]) :
    affineNormalForm W p q = 0 ↔ p = 0 ∧ q = 0 := by
  constructor
  · intro h
    apply Affine.CoordinateRing.smul_basis_eq_zero (W' := W.toAffine)
    rw [← affineNormalForm_monic, h, map_zero]
  · rintro ⟨rfl, rfl⟩
    simp [affineNormalForm]

/-- Subtraction is coefficientwise in the original polynomial normal form. -/
theorem affineNormalForm_sub (p q p' q' : R[X]) :
    affineNormalForm W (p - p') (q - q') =
      affineNormalForm W p q - affineNormalForm W p' q' := by
  simp only [affineNormalForm, map_sub]
  ring

/-- Uniqueness of normal form retains nilpotent coefficients as well. -/
theorem affineNormalForm_injective {p q p' q' : R[X]}
    (h : affineNormalForm W p q = affineNormalForm W p' q') : p = p' ∧ q = q' := by
  have he : affineNormalForm W (p - p') (q - q') = 0 := by
    rw [affineNormalForm_sub, h, sub_self]
  exact ⟨sub_eq_zero.mp ((affineNormalForm_eq_zero W _ _).mp he).1,
    sub_eq_zero.mp ((affineNormalForm_eq_zero W _ _).mp he).2⟩

/-- Polynomial pairs parametrize the original affine coordinate ring bijectively. -/
theorem affineNormalForm_bijective :
    Function.Bijective (fun pq : R[X] × R[X] ↦ affineNormalForm W pq.1 pq.2) := by
  constructor
  · intro a b h
    exact Prod.ext (affineNormalForm_injective W h).1 (affineNormalForm_injective W h).2
  · intro a
    obtain ⟨p, q, h⟩ := exists_affineNormalForm W a
    exact ⟨(p, q), h⟩

end FLT.Mazur.WeierstrassIntegralChart
