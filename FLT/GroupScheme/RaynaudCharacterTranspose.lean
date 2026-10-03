/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterProjector
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Transpose scalar actions and character projectors

The commutative scalar group acts on the linear dual by transposition.
A character projector commutes with the original action, and pairing with
a transpose eigenvector removes the matching projector.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.CharacterProjector

variable {R G V : Type*} [CommRing R] [CommGroup G] [AddCommGroup V] [Module R V]
  (ρ : Representation R G V)

/-- The transpose action of a commutative scalar group. -/
def transpose : Representation R G (Module.Dual R V) where
  toFun g := (ρ g).dualMap
  map_one' := by ext φ v; simp
  map_mul' g h := by
    ext φ v
    change φ (ρ (g * h) v) = φ (ρ h (ρ g v))
    rw [mul_comm g h, map_mul]
    rfl

variable [Fintype G] [Invertible (Fintype.card G : R)] (χ : G →* Rˣ)

/-- The character projector commutes with each scalar action. -/
theorem projector_commutes (g : G) (v : V) :
    projector ρ χ (ρ g v) = ρ g (projector ρ χ v) := by
  rw [projector_apply, projector_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  rw [map_smul]
  congr 1
  change (ρ h * ρ g) v = (ρ g * ρ h) v
  rw [← map_mul, ← map_mul, mul_comm h g]

/-- Applying a scalar before the projector multiplies the result by its character. -/
theorem projector_scalar (g : G) (v : V) :
    projector ρ χ (ρ g v) = (χ g : R) • projector ρ χ v := by
  rw [projector_commutes]
  exact (mem_eigenspace_iff ρ χ _).mp (projector_mem ρ χ v) g

/-- A transpose eigenvector pairs only with the matching projection. -/
theorem transpose_pair_projector (φ : eigenspace (transpose ρ) χ) (v : V) :
    φ.val (projector ρ χ v) = φ.val v := by
  have hφ (g : G) : φ.val (ρ g v) = (χ g : R) * φ.val v :=
    congrArg (fun f : Module.Dual R V ↦ f v)
      ((mem_eigenspace_iff (transpose ρ) χ φ.val).mp φ.property g)
  rw [projector_apply, map_smul, map_sum]
  simp_rw [map_smul, hφ, smul_eq_mul, ← mul_assoc, Units.inv_mul, one_mul]
  simp [← Nat.cast_smul_eq_nsmul R]

end ThreeAdicPlan.CharacterProjector
