/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudFlatKernelExactness
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Rank of the fibre of a finite free algebra over an augmentation -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace AlgHom
variable {R D A : Type*} [CommRing R] [CommRing D] [CommRing A]
  [Nontrivial R] [Nontrivial D] [Algebra R D] [Algebra R A] [Algebra D A]
  [IsScalarTower R D A] [Module.Free D A]

/-- The augmentation fibre has the same rank as the original free relative algebra. -/
theorem quotient_map_ker_finrank (ε : D →ₐ[R] R) :
    Module.finrank R (A ⧸ (RingHom.ker ε.toRingHom).map (algebraMap D A)) =
      Module.finrank D A := by
  let I := RingHom.ker ε.toRingHom
  have hε : Function.Surjective ε := fun r ↦ ⟨algebraMap R D r, by simp⟩
  let e : (D ⧸ I) ≃ₐ[R] R := Ideal.quotientKerAlgEquivOfSurjective hε
  let : Module.Free R (D ⧸ I) := Module.Free.of_equiv e.toLinearEquiv.symm
  let t := ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).toLinearEquiv.restrictScalars R)
    ≪≫ₗ ((Algebra.TensorProduct.comm D A (D ⧸ I)).toLinearEquiv.restrictScalars R)
  let : Algebra D R := ε.toRingHom.toAlgebra
  let : IsScalarTower D R (D ⧸ I) := IsScalarTower.of_algebraMap_eq (fun d ↦ by
    apply e.injective
    change ε d = e (algebraMap R (D ⧸ I) (ε d))
    exact (e.commutes _).symm)
  rw [t.finrank_eq, Module.finrank_tensorProduct, e.toLinearEquiv.finrank_eq,
    Module.finrank_self, one_mul]
end AlgHom
