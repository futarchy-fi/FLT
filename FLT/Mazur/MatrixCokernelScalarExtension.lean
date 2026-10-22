/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# The mapped matrix presents the actual scalar-extended cokernel

The comparison is linear over the new ring and requires no flatness of the
coefficient map. It identifies the original presentation, not a substitute
module chosen after extension.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.MatrixCokernel
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  {m n : Type*} [Finite m] [Fintype n]

/-- Coordinate comparison with finiteness carried propositionally. -/
def scalarCoordinates : S ⊗[R] (m → R) ≃ₗ[S] (m → S) := by
  classical
  let _ := Fintype.ofFinite m
  exact TensorProduct.piScalarRight R S S m

/-- The standard coordinate comparison sends a unit tensor to its mapped vector. -/
theorem scalarPi_one_tmul (v : m → R) :
    scalarCoordinates (R := R) (m := m) S (1 ⊗ₜ[R] v) = fun i ↦ algebraMap R S (v i) := by
  classical
  let _ := Fintype.ofFinite m
  change TensorProduct.piScalarRightHom R S S m (1 ⊗ₜ[R] v) = _
  rw [TensorProduct.piScalarRightHom_tmul]
  ext i
  change v i • (1 : S) = algebraMap R S (v i)
  simp only [Algebra.smul_def, mul_one]

/-- The extended relation submodule is the range of the coefficient-mapped matrix. -/
theorem scalarPi_map_range (A : Matrix m n R) :
    ((LinearMap.range A.mulVecLin).baseChange S).map
      (scalarCoordinates (R := R) (m := m) S).toLinearMap =
        LinearMap.range (A.map (algebraMap R S)).mulVecLin := by
  rw [Matrix.range_mulVecLin, Submodule.baseChange_span, Submodule.map_span,
    Matrix.range_mulVecLin]
  congr 1
  ext v
  constructor
  · rintro ⟨_, ⟨_, ⟨j, rfl⟩, rfl⟩, rfl⟩
    exact ⟨j, (scalarPi_one_tmul S (A.col j)).symm⟩
  · rintro ⟨j, rfl⟩
    refine ⟨1 ⊗ₜ[R] A.col j, ⟨A.col j, ⟨j, rfl⟩, rfl⟩, ?_⟩
    exact scalarPi_one_tmul S (A.col j)

/-- Scalar extension of the whole original cokernel is the mapped-matrix cokernel. -/
def scalarExtensionEquiv (A : Matrix m n R) :
    S ⊗[R] ((m → R) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[S]
      (m → S) ⧸ LinearMap.range (A.map (algebraMap R S)).mulVecLin :=
  (AlgebraTensorModule.tensorQuotientEquiv S R S (LinearMap.range A.mulVecLin)).trans
    (Submodule.Quotient.equiv _ _ (scalarCoordinates (R := R) (m := m) S)
      (scalarPi_map_range S A))

/-- Recovery preserves the class of each original numerator. -/
theorem scalarExtensionEquiv_one_tmul (A : Matrix m n R) (v : m → R) :
    scalarExtensionEquiv S A (1 ⊗ₜ[R] (LinearMap.range A.mulVecLin).mkQ v) =
      (LinearMap.range (A.map (algebraMap R S)).mulVecLin).mkQ
        (fun i ↦ algebraMap R S (v i)) := by
  change (LinearMap.range (A.map (algebraMap R S)).mulVecLin).mkQ
    (scalarCoordinates (R := R) (m := m) S (1 ⊗ₜ[R] v)) = _
  rw [scalarPi_one_tmul]

end FLT.Mazur.MatrixCokernel
