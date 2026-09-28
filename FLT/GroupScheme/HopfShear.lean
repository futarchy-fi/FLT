/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# The shear automorphism of a commutative Hopf algebra

The map `a ⊗ b ↦ (a ⊗ 1) Δ(b)` is invertible. Its inverse uses the
antipode on the first factor of `Δ(b)`. This is the ambient automorphism
used to construct the relative Hopf torsor isomorphism.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Algebra.TensorProduct WithConv

namespace HopfAlgebra

variable (R A : Type*) [CommSemiring R] [CommSemiring A] [HopfAlgebra R A]

/-- The shear map fixes the left factor and applies comultiplication to the right. -/
def shearHom : A ⊗[R] A →ₐ[R] A ⊗[R] A :=
  lift includeLeft (Bialgebra.comulAlgHom R A) (fun _ _ ↦ .all ..)

/-- The inverse shear fixes the left factor and applies the antipode to the
first output of comultiplication on the right factor. -/
def shearInvHom : A ⊗[R] A →ₐ[R] A ⊗[R] A :=
  lift includeLeft
    ((toConv (includeLeft : A →ₐ[R] A ⊗[R] A))⁻¹ * toConv includeRight).ofConv
    (fun _ _ ↦ .all ..)

variable {R A}

theorem comulAlgHom_eq_conv_include :
    Bialgebra.comulAlgHom R A =
      (toConv (includeLeft : A →ₐ[R] A ⊗[R] A) * toConv includeRight).ofConv := by
  ext a
  rw [AlgHom.convMul_apply]
  have h : lift (includeLeft : A →ₐ[R] A ⊗[R] A) includeRight
      (fun _ _ ↦ Commute.all _ _) = AlgHom.id R (A ⊗[R] A) := by
    ext <;> simp
  rw [h]
  rfl

@[simp]
theorem shearHom_comp_includeLeft :
    (shearHom R A).comp includeLeft = (includeLeft : A →ₐ[R] A ⊗[R] A) := by
  ext; simp [shearHom]

@[simp]
theorem shearHom_comp_includeRight :
    (shearHom R A).comp includeRight = Bialgebra.comulAlgHom R A := by
  ext; simp [shearHom]

@[simp]
theorem shearInvHom_comp_includeLeft :
    (shearInvHom R A).comp includeLeft = (includeLeft : A →ₐ[R] A ⊗[R] A) := by
  ext; simp [shearInvHom]

@[simp]
theorem shearInvHom_comp_includeRight :
    (shearInvHom R A).comp includeRight =
      ((toConv (includeLeft : A →ₐ[R] A ⊗[R] A))⁻¹ * toConv includeRight).ofConv := by
  ext; simp [shearInvHom]

theorem shearInvHom_comp_shearHom :
    (shearInvHom R A).comp (shearHom R A) = AlgHom.id R (A ⊗[R] A) := by
  apply Algebra.TensorProduct.ext
  · simp [AlgHom.comp_assoc]
  · change ((shearInvHom R A).comp (shearHom R A)).comp includeRight = _
    rw [AlgHom.comp_assoc, shearHom_comp_includeRight, comulAlgHom_eq_conv_include,
      AlgHom.comp_convMul_distrib]
    simp only [shearInvHom_comp_includeLeft, shearInvHom_comp_includeRight,
      toConv_ofConv, mul_inv_cancel_left]
    rfl

theorem shearHom_comp_shearInvHom :
    (shearHom R A).comp (shearInvHom R A) = AlgHom.id R (A ⊗[R] A) := by
  apply Algebra.TensorProduct.ext
  · simp [AlgHom.comp_assoc]
  · change ((shearHom R A).comp (shearInvHom R A)).comp includeRight = _
    rw [AlgHom.comp_assoc, shearInvHom_comp_includeRight, AlgHom.comp_convMul_distrib]
    have hi : (shearHom R A).comp
        (toConv (includeLeft : A →ₐ[R] A ⊗[R] A))⁻¹.ofConv =
        (toConv (includeLeft : A →ₐ[R] A ⊗[R] A))⁻¹.ofConv := by
      change (shearHom R A).comp (includeLeft.comp (antipodeAlgHom R A)) = _
      rw [← AlgHom.comp_assoc, shearHom_comp_includeLeft]
      rfl
    rw [hi, shearHom_comp_includeRight, comulAlgHom_eq_conv_include]
    simp only [toConv_ofConv, inv_mul_cancel_left]
    rfl

/-- The Hopf shear automorphism `a ⊗ b ↦ (a ⊗ 1) Δ(b)`. -/
def shearEquiv : A ⊗[R] A ≃ₐ[R] A ⊗[R] A :=
  AlgEquiv.ofAlgHom (shearHom R A) (shearInvHom R A)
    shearHom_comp_shearInvHom shearInvHom_comp_shearHom

@[simp]
theorem shearEquiv_tmul (a b : A) :
    shearEquiv (R := R) (A := A) (a ⊗ₜ[R] b) =
      (a ⊗ₜ[R] 1) * Coalgebra.comul b := by
  simp [shearEquiv, shearHom]

@[simp]
theorem shearEquiv_symm_tmul (a b : A) :
    (shearEquiv (R := R) (A := A)).symm (a ⊗ₜ[R] b) =
      (a ⊗ₜ[R] 1) *
        (Algebra.TensorProduct.map (antipodeAlgHom R A) (AlgHom.id R A))
          (Coalgebra.comul b) := by
  change shearInvHom R A (a ⊗ₜ[R] b) = _
  rw [shearInvHom, lift_tmul, AlgHom.convMul_apply]
  congr 1
  have h : lift (toConv (includeLeft : A →ₐ[R] A ⊗[R] A))⁻¹.ofConv includeRight
      (fun _ _ ↦ Commute.all _ _) =
      Algebra.TensorProduct.map (antipodeAlgHom R A) (AlgHom.id R A) := by
    ext <;> simp
    rfl
  exact congrArg (fun f : A ⊗[R] A →ₐ[R] A ⊗[R] A ↦ f (Coalgebra.comul b)) h

/-- The shear is an algebra automorphism over the left copy of `A`. -/
def shearEquivOverLeft : A ⊗[R] A ≃ₐ[A] A ⊗[R] A where
  __ := shearEquiv (R := R) (A := A)
  commutes' a := by
    change shearEquiv (R := R) (A := A) (a ⊗ₜ[R] 1) = a ⊗ₜ[R] 1
    simp

end HopfAlgebra
