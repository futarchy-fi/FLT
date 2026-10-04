/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Flat scalar extension of finite compatibility kernels

Tensoring the kernel of a map between finite products with a flat algebra
is the kernel of the componentwise extended map. The comparison retains
its formula on pure tensors, for use with finite affine section covers.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FCurve
variable {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {M : ι → Type*} {N : κ → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]

/-- A map between finite products after extending the scalars of each component. -/
def finiteProductBaseChange (d : (∀ i, M i) →ₗ[R] ∀ j, N j) :
    (∀ i, S ⊗[R] M i) →ₗ[S] ∀ j, S ⊗[R] N j :=
  (piRight R S S N).toLinearMap.comp
    ((AlgebraTensorModule.lTensor S S d).comp (piRight R S S M).symm.toLinearMap)

/-- Componentwise scalar extension has the expected pure-tensor formula. -/
@[simp]
lemma finiteProductBaseChange_tmul (d : (∀ i, M i) →ₗ[R] ∀ j, N j)
    (a : S) (m : ∀ i, M i) (j : κ) :
    finiteProductBaseChange S d (fun i ↦ a ⊗ₜ[R] m i) j = a ⊗ₜ[R] d m j := by
  simp [finiteProductBaseChange, piRight_symm_apply, piRight_apply, piRightHom_tmul]

/-- The finite-product comparison identifies the two kernels, without flatness. -/
def finiteProductKernelEquiv (d : (∀ i, M i) →ₗ[R] ∀ j, N j) :
    (AlgebraTensorModule.lTensor S S d).ker ≃ₗ[S]
      (finiteProductBaseChange S d).ker where
  toFun x := ⟨piRight R S S M x, by
    change piRight R S S N ((AlgebraTensorModule.lTensor S S d)
      ((piRight R S S M).symm (piRight R S S M x))) = 0
    rw [LinearEquiv.symm_apply_apply, x.property, map_zero]⟩
  invFun x := ⟨(piRight R S S M).symm x, by
    apply (piRight R S S N).injective
    exact x.property.trans (map_zero _).symm⟩
  left_inv x := Subtype.ext ((piRight R S S M).symm_apply_apply x)
  right_inv x := Subtype.ext ((piRight R S S M).apply_symm_apply x)
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' a x := Subtype.ext (map_smul _ _ _)

/-- Flat scalar extension commutes with a finite compatibility kernel. -/
def flatFiniteKernelEquiv [Module.Flat R S]
    (d : (∀ i, M i) →ₗ[R] ∀ j, N j) :
    S ⊗[R] d.ker ≃ₗ[S] (finiteProductBaseChange S d).ker :=
  LinearMap.tensorKerEquiv S S d ≪≫ₗ finiteProductKernelEquiv S d

/-- The flat kernel comparison sends a pure tensor to its componentwise tensors. -/
@[simp]
lemma flatFiniteKernelEquiv_tmul [Module.Flat R S]
    (d : (∀ i, M i) →ₗ[R] ∀ j, N j) (a : S) (m : d.ker) (i : ι) :
    (flatFiniteKernelEquiv S d (a ⊗ₜ[R] m)).val i = a ⊗ₜ[R] m.val i := rfl

end FLT.Mazur.FCurve
