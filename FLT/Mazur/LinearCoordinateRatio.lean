/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Unit ratios between rank-one coordinates

Two linear coordinates on a rank-one module differ by a unit. Three
coordinates satisfy the cocycle equation without any extra hypothesis.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.Approximation

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Changing coordinates is multiplication by the coordinate of the other generator. -/
theorem linearCoordinateRatio_apply (e f : M ≃ₗ[R] R) (x : R) :
    e (f.symm x) = x * e (f.symm 1) := by
  have h := congrArg e (f.symm.map_smul x 1)
  simpa only [smul_eq_mul, mul_one, e.map_smul] using h

/-- The scalar coefficient for a change of rank-one coordinates is a unit. -/
def linearCoordinateRatio (e f : M ≃ₗ[R] R) : Rˣ where
  val := e (f.symm 1)
  inv := f (e.symm 1)
  val_inv := by
    rw [mul_comm, ← linearCoordinateRatio_apply, f.symm_apply_apply, e.apply_symm_apply]
  inv_val := by
    rw [mul_comm, ← linearCoordinateRatio_apply, e.symm_apply_apply, f.apply_symm_apply]

/-- A coordinate agrees with the other coordinate multiplied by their ratio. -/
theorem linearCoordinateRatio_smul (e f : M ≃ₗ[R] R) (m : M) :
    e m = (linearCoordinateRatio e f : R) * f m := by
  rw [mul_comm]
  simpa only [f.symm_apply_apply, linearCoordinateRatio] using linearCoordinateRatio_apply e f (f m)

/-- Coordinate ratios obey the multiplicative cocycle law. -/
theorem linearCoordinateRatio_mul (e f g : M ≃ₗ[R] R) :
    linearCoordinateRatio e f * linearCoordinateRatio f g = linearCoordinateRatio e g := by
  apply Units.ext
  change e (f.symm 1) * f (g.symm 1) = e (g.symm 1)
  rw [mul_comm, ← linearCoordinateRatio_apply, f.symm_apply_apply]

/-- A coordinate's self-ratio is one. -/
@[simp]
theorem linearCoordinateRatio_self (e : M ≃ₗ[R] R) : linearCoordinateRatio e e = 1 := by
  apply Units.ext
  exact e.apply_symm_apply 1

end FLT.Mazur.Approximation
