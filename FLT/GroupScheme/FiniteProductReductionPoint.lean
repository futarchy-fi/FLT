/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.TensorProduct.Pi

/-! # Assemble reduced chart points on the actual finite product cover -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace Algebra.TensorProduct
variable (B C : Type*) [CommRing B] [CommRing C] [Algebra B C]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (D : ι → Type*)
  [∀ i, CommRing (D i)] [∀ i, Algebra B (D i)]

/-- Reduction of a finite product is the product of the specified reductions. -/
def finiteProductReductionEquiv :
    ((∀ i, D i) ⊗[B] C) ≃ₐ[B] ∀ i, D i ⊗[B] C :=
  (Algebra.TensorProduct.comm B _ C).trans ((piRight B B C D).trans
    (AlgEquiv.piCongrRight fun i ↦ Algebra.TensorProduct.comm B C (D i)))

/-- The product comparison retains every tensor representative. -/
@[simp]
theorem finiteProductReductionEquiv_tmul (d : ∀ i, D i) (c : C) (i : ι) :
    finiteProductReductionEquiv B C D (d ⊗ₜ[B] c) i = d i ⊗ₜ[B] c := rfl

end Algebra.TensorProduct
namespace AlgHom
variable {R B C A H : Type*} [CommRing R] [CommRing B] [CommRing C]
  [CommRing A] [CommRing H] [Algebra R B] [Algebra R C] [Algebra B C]
  [IsScalarTower R B C] [Algebra R A] [Algebra R H]
  {ι : Type*} [Finite ι] (D : ι → Type*)
  [∀ i, CommRing (D i)] [∀ i, Algebra B (D i)] [∀ i, Algebra R (D i)]
  [∀ i, IsScalarTower R B (D i)]

/-- Coordinate-compatible division points on the reduced charts assemble on the actual
reduction of their product, retaining the same coordinate composite. -/
theorem exists_finiteProduct_reduction_point (f : A →ₐ[R] H) (x : A →ₐ[R] C)
    (z : ∀ i, H →ₐ[R] D i ⊗[B] C)
    (hz : ∀ i, (z i).comp f = (Algebra.TensorProduct.includeRight.restrictScalars R).comp x) :
    ∃ y : H →ₐ[R] (∀ i, D i) ⊗[B] C,
      y.comp f = (Algebra.TensorProduct.includeRight.restrictScalars R).comp x := by
  classical
  let := Fintype.ofFinite ι
  let e := (Algebra.TensorProduct.finiteProductReductionEquiv B C D).restrictScalars R
  refine ⟨e.symm.toAlgHom.comp (AlgHom.pi z), ?_⟩
  ext a
  apply e.injective
  change e (e.symm (fun i ↦ z i (f a))) = _
  rw [AlgEquiv.apply_symm_apply]
  funext i
  exact AlgHom.congr_fun (hz i) a

end AlgHom
