/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXOverlap

/-!
# Inverse substitutions and contraction compatibility

The overlap substitutions are inverse on all three successive x-chart
coordinates, including the retained old horizontal coordinate. The maps
also identify the actual contractions to the preceding divided chart.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "A" => Coordinate W s π b3 b4 b6
local notation "D" => WeierstrassDilatation.Coordinate W (s * π) b3 b4 b6
local notation "DX" => WeierstrassDilatation.x W (s * π) b3 b4 b6

/-- Incidence determines the retained coordinate wherever the incidence factor is a unit. -/
theorem incidence_inverse (f : A →ₐ[R] S) (a : Sˣ)
    (ha : f (coord W s π b3 b4 b6 0) = a) :
    algebraMap R S π * (↑a⁻¹ : S) = f (coord W s π b3 b4 b6 2) := by
  have h := congrArg f (incidence W s π b3 b4 b6)
  simp only [map_mul, AlgHom.commutes, ha] at h
  rw [← h, mul_right_comm, Units.mul_inv, one_mul]

/-- Both substitutions compose to the original map on all three x-chart coordinates. -/
theorem xOverlapMap_dividedOverlapMap (f : A →ₐ[R] S) (a : Sˣ)
    (ha : f (coord W s π b3 b4 b6 0) = a) :
    xOverlapMap W s π b3 b4 b6 (dividedOverlapMap W s π b3 b4 b6 f a ha) a⁻¹
      (dividedOverlapMap_x W s π b3 b4 b6 f a ha) = f := by
  apply hom_ext
  intro i
  fin_cases i
  · change (xOverlapMap W s π b3 b4 b6
        (dividedOverlapMap W s π b3 b4 b6 f a ha) a⁻¹ _)
        (coord W s π b3 b4 b6 0) = f (coord W s π b3 b4 b6 0)
    simp only [xOverlapMap_t, inv_inv, ha]
  · change (xOverlapMap W s π b3 b4 b6
        (dividedOverlapMap W s π b3 b4 b6 f a ha) a⁻¹ _)
        (coord W s π b3 b4 b6 1) = f (coord W s π b3 b4 b6 1)
    simp only [xOverlapMap_v, inv_inv, dividedOverlapMap_y]
    rw [← mul_assoc, Units.mul_inv, one_mul]
  · change (xOverlapMap W s π b3 b4 b6
        (dividedOverlapMap W s π b3 b4 b6 f a ha) a⁻¹ _)
        (coord W s π b3 b4 b6 2) = f (coord W s π b3 b4 b6 2)
    rw [xOverlapMap_u]
    exact incidence_inverse W s π b3 b4 b6 f a ha

/-- The opposite composite is the original map on the new divided chart. -/
theorem dividedOverlapMap_xOverlapMap (f : D →ₐ[R] S) (a : Sˣ) (ha : f DX = a) :
    dividedOverlapMap W s π b3 b4 b6 (xOverlapMap W s π b3 b4 b6 f a ha) a⁻¹
      (xOverlapMap_t W s π b3 b4 b6 f a ha) = f := by
  apply WeierstrassDilatation.hom_ext
  · simp only [dividedOverlapMap_x, inv_inv, ha]
  · simp only [dividedOverlapMap_y, inv_inv, xOverlapMap_v]
    rw [← mul_assoc, Units.mul_inv, one_mul]

/-- On the overlap both actual maps to the preceding divided chart agree. -/
theorem xOverlapMap_fromDivided (f : D →ₐ[R] S) (a : Sˣ) (ha : f DX = a) :
    (xOverlapMap W s π b3 b4 b6 f a ha).comp (fromDivided W s π b3 b4 b6) =
      f.comp (WeierstrassDilatation.refinement W s π
        (π * b3) (π * b4) (π ^ 2 * b6) b3 b4 b6 rfl rfl rfl) := by
  apply WeierstrassDilatation.hom_ext
  · simp only [AlgHom.comp_apply, fromDivided_x, xOverlapMap_u,
      WeierstrassDilatation.refinement_x, map_mul, AlgHom.commutes, ha]
  · simp only [AlgHom.comp_apply, fromDivided_y, map_mul, xOverlapMap_u, xOverlapMap_v,
      WeierstrassDilatation.refinement_y, AlgHom.commutes]
    rw [mul_assoc, ← mul_assoc (↑a : S), Units.mul_inv, one_mul]

end FLT.Mazur.WeierstrassSuccessiveX
