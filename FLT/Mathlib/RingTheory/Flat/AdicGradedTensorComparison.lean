/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Tensor comparison for residue modules and adic graded pieces -/

@[expose] public noncomputable section

open TensorProduct

namespace Module.Flat

variable {R A N M V : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]
  [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]

/-- Injectivity after scalar extension to `A` implies injectivity after tensoring
with any flat `A`-module. In the adic application, `A` is the residue field. -/
theorem lTensor_injective_of_baseChange [Flat A V] (f : N →ₗ[R] M)
    (hf : Function.Injective (f.baseChange A)) : Function.Injective (f.lTensor V) := by
  let eN := AlgebraTensorModule.cancelBaseChange R A A V N
  let eM := AlgebraTensorModule.cancelBaseChange R A A V M
  have h := Flat.lTensor_preserves_injective_linearMap (M := V) (f.baseChange A) hf
  have he (x : V ⊗[A] (A ⊗[R] N)) :
      f.lTensor V (eN x) = eM (((f.baseChange A).lTensor V) x) := by
    induction x with
    | tmul v x =>
      induction x with
      | tmul a n => rfl
      | add x y hx hy => simp_all [tmul_add]
    | add x y hx hy => simp_all
  intro x y hxy
  apply eN.symm.injective
  apply h
  apply eM.injective
  simpa only [← he, LinearEquiv.apply_symm_apply] using hxy

end Module.Flat

namespace Ideal

variable {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)

/-- The degree `n` adic piece, with its canonical residue-ring module structure. -/
abbrev AdicGradedPiece :=
  (I ^ n : Ideal R) ⧸ (I • (⊤ : Submodule R (I ^ n : Ideal R)))

/-- Tensoring an adic graded piece with a module only uses the module's base
change to `R/I`. This is the comparison including its canonical quotient map. -/
def adicGradedTensorComparison (M : Type*) [AddCommGroup M] [Module R M] :
    AdicGradedPiece I n ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] M) ≃ₗ[R ⧸ I]
      AdicGradedPiece I n ⊗[R] M :=
  AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (R ⧸ I) (AdicGradedPiece I n) M

@[simp]
theorem adicGradedTensorComparison_tmul (M : Type*) [AddCommGroup M] [Module R M]
    (v : AdicGradedPiece I n) (m : M) :
    adicGradedTensorComparison I n M (v ⊗ₜ (1 ⊗ₜ m)) = v ⊗ₜ m := by
  simp [adicGradedTensorComparison]

/-- The same graded comparison with the residue tensor written as the actual
module quotient `M/IM`. -/
def adicGradedQuotientTensorComparison (M : Type*) [AddCommGroup M] [Module R M] :
    AdicGradedPiece I n ⊗[R ⧸ I] (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R ⧸ I]
      AdicGradedPiece I n ⊗[R] M :=
  ((quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective).symm.lTensor (AdicGradedPiece I n) ≪≫ₗ
      adicGradedTensorComparison I n M

@[simp]
theorem adicGradedQuotientTensorComparison_mk (M : Type*) [AddCommGroup M] [Module R M]
    (v : AdicGradedPiece I n) (m : M) :
    adicGradedQuotientTensorComparison I n M (v ⊗ₜ Submodule.Quotient.mk m) = v ⊗ₜ m := by
  change adicGradedTensorComparison I n M (v ⊗ₜ (1 ⊗ₜ m)) = _
  exact adicGradedTensorComparison_tmul I n M v m

end Ideal
