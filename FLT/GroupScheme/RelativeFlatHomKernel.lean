/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RelativeHomRelations
public import Mathlib.LinearAlgebra.TensorProduct.Free

/-! # Flat tensoring of original relation functionals over an arbitrary test algebra -/

@[expose] public noncomputable section
open TensorProduct
namespace LinearMap
variable {R B S U V M : Type*} [CommRing R] [CommRing B] [CommRing S]
  [Algebra R B] [Algebra B S] [Algebra R S] [IsScalarTower R B S]
  [AddCommGroup U] [AddCommGroup V] [AddCommGroup M]
  [Module R U] [Module R V] [Module R M] [Module B M] [IsScalarTower R B M]
  [Module.Free R U] [Module.Finite R U] [Module.Free R V] [Module.Finite R V]
  [Module.Flat B S]

/-- The cover need only be flat over the actual test algebra, not over the original base. -/
def relativeFlatHomKernelEquiv (r : U →ₗ[R] V) :
    S ⊗[B] ker (relativeRelationPrecomp (B := B) (M := M) r) ≃ₗ[B]
      ker (relativeRelationPrecomp (B := B) (M := S ⊗[B] M) r) :=
  (TensorProduct.congr (LinearEquiv.refl B S) (relativeRelationKernelEquiv r).symm).trans
    ((flatTensorHomKernelEquiv (r.baseChange B)).trans (relativeRelationKernelEquiv r))

/-- The relative comparison retains evaluation on the original coordinates. -/
theorem relativeFlatHomKernelEquiv_tmul (r : U →ₗ[R] V) (s : S)
    (f : ker (relativeRelationPrecomp (B := B) (M := M) r)) (v : V) :
    (relativeFlatHomKernelEquiv r (s ⊗ₜ[B] f)).val v = s ⊗ₜ[B] f.val v := by
  change (flatTensorHomKernelEquiv (r.baseChange B)
    (s ⊗ₜ[B] (relativeRelationKernelEquiv r).symm f)).val (1 ⊗ₜ[R] v) = _
  rw [flatTensorHomKernelEquiv_tmul]
  change s ⊗ₜ[B] scalarExtensionHomEquiv.symm f.val (1 ⊗ₜ[R] v) = _
  rw [scalarExtensionHomEquiv_symm_tmul, one_smul]

end LinearMap
