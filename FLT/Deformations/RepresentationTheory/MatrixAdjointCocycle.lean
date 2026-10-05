/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.ContinuousClass
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Topology.Instances.Matrix

/-!
# Normalizing matrix derivatives to adjoint cocycles

Right multiplication by the inverse residual matrix turns the differentiated
representation law into the adjoint cocycle identity. A strict frame change
adds a coboundary, with its sign determined by the conjugation convention.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Deformation
open GaloisRepresentation.Extensions
variable {k G n : Type*} [CommRing k] [Group G] [Fintype n] [DecidableEq n]

/-- Matrices with the adjoint action of the specified residual representation. -/
def AdjointMatrices (_r : G →* GL n k) := Matrix n n k

namespace AdjointMatrices
variable (r : G →* GL n k)
instance : AddCommGroup (AdjointMatrices r) := inferInstanceAs (AddCommGroup (Matrix n n k))
instance : Module k (AdjointMatrices r) := inferInstanceAs (Module k (Matrix n n k))
instance [TopologicalSpace k] : TopologicalSpace (AdjointMatrices r) :=
  inferInstanceAs (TopologicalSpace (Matrix n n k))
instance [TopologicalSpace k] [IsTopologicalRing k] :
    IsTopologicalAddGroup (AdjointMatrices r) :=
  inferInstanceAs (IsTopologicalAddGroup (Matrix n n k))

instance : DistribMulAction G (AdjointMatrices r) where
  smul g X := (r g).val * (show Matrix n n k from X) * (r g)⁻¹.val
  one_smul X := by change (r 1).val * (show Matrix n n k from X) * (r 1)⁻¹.val = X; simp
  mul_smul g h X := by
    change (r (g * h)).val * (show Matrix n n k from X) * (r (g * h))⁻¹.val =
      (r g).val * ((r h).val * (show Matrix n n k from X) * (r h)⁻¹.val) * (r g)⁻¹.val
    simp [mul_assoc]
  smul_zero g := by change (r g).val * 0 * (r g)⁻¹.val = 0; simp
  smul_add g X Y := by
    change (r g).val * (show Matrix n n k from X + Y) * (r g)⁻¹.val =
      (r g).val * (show Matrix n n k from X) * (r g)⁻¹.val +
      (r g).val * (show Matrix n n k from Y) * (r g)⁻¹.val
    simp [mul_add, add_mul]

/-- The adjoint action preserves matrix trace. -/
theorem trace_smul (g : G) (X : AdjointMatrices r) :
    Matrix.trace (show Matrix n n k from (g • X : AdjointMatrices r)) =
      Matrix.trace (show Matrix n n k from X) :=
  Matrix.trace_units_conj (r g) X

variable [TopologicalSpace G] [TopologicalSpace k] [IsTopologicalRing k]

/-- Continuity of the original representation gives continuous adjoint orbits. -/
theorem continuous_orbit (hr : Continuous r) (X : AdjointMatrices r) :
    Continuous (fun g : G ↦ g • X) :=
  ((Units.continuous_val.comp hr).mul continuous_const).mul
    (Units.continuous_coe_inv.comp hr)

end AdjointMatrices

variable (r : G →* GL n k) (D : G → Matrix n n k)

/-- The normalized derivative has adjoint, rather than left/right, coefficients. -/
def normalizedMatrixDerivative (g : G) : AdjointMatrices r := D g * (r g)⁻¹.val

/-- The matrix product rule gives the actual adjoint cocycle equation. -/
theorem normalizedMatrixDerivative_isCocycle
    (hD : ∀ g h, D (g * h) = (r g).val * D h + D g * (r h).val) :
    groupCohomology.IsCocycle₁ (normalizedMatrixDerivative r D) := by
  intro g h
  change D (g * h) * (r (g * h))⁻¹.val =
    (r g).val * (D h * (r h)⁻¹.val) * (r g)⁻¹.val + D g * (r g)⁻¹.val
  rw [hD, map_mul, mul_inv_rev, Units.val_mul, add_mul]
  simp [← mul_assoc]

variable [TopologicalSpace G] [TopologicalSpace k] [IsTopologicalRing k]

/-- Continuous derivatives give bundled continuous cocycles. -/
def matrixDerivativeCocycle (hr : Continuous r) (hDc : Continuous D)
    (hD : ∀ g h, D (g * h) = (r g).val * D h + D g * (r h).val) :
    ContinuousCocycle G (AdjointMatrices r) :=
  ⟨⟨normalizedMatrixDerivative r D, hDc.mul (Units.continuous_coe_inv.comp hr)⟩,
    normalizedMatrixDerivative_isCocycle r D hD⟩

omit [TopologicalSpace G] [TopologicalSpace k] [IsTopologicalRing k] in
/-- Conjugating by `1 + εX` changes the normalized derivative by the boundary of `-X`. -/
theorem normalizedMatrixDerivative_frame (X : Matrix n n k) :
    normalizedMatrixDerivative r (fun g ↦ D g + X * (r g).val - (r g).val * X) =
      changeSplitting (normalizedMatrixDerivative r D) (-X) := by
  funext g
  change (D g + X * (r g).val - (r g).val * X) * (r g)⁻¹.val =
    D g * (r g)⁻¹.val + ((r g).val * (-X) * (r g)⁻¹.val - (-X))
  simp [add_mul, mul_assoc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

end Deformation
