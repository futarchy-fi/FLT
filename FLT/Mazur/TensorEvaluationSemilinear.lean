/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Transport of tensor evaluation across semilinear coordinates

Changing the base ring, coefficients, and module by compatible equivalences
preserves injectivity of scalar-extended evaluation.
-/

@[expose] public noncomputable section

open TensorProduct
namespace FLT.Mazur.Approximation

variable {R S B C M N P Q : Type*} [CommRing R] [CommRing S]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module S C]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module S Q]
  {σ : R →+* S} {τ : S →+* R} [RingHomInvPair σ τ] [RingHomInvPair τ σ]
  (b : B ≃ₛₗ[σ] C) (m : M ≃ₛₗ[σ] N) (p : P ≃ₛₗ[σ] Q)
  (ε : M →ₗ[R] P) (δ : N →ₗ[S] Q) (h : ∀ x, p (ε x) = δ (m x))

include b h in
/-- A commuting evaluation square remains commuting after semilinear tensor transport. -/
theorem tensorEvaluation_semilinear (x : B ⊗[R] M) :
    TensorProduct.congr b p (ε.lTensor B x) =
      δ.lTensor C (TensorProduct.congr b m x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b x => simp only [LinearMap.lTensor_tmul, congr_tmul, h]

include b h in
/-- Injective tensor evaluation is invariant under compatible semilinear equivalences. -/
theorem tensorEvaluation_injective_iff_semilinear :
    Function.Injective (ε.lTensor B) ↔ Function.Injective (δ.lTensor C) := by
  let a := TensorProduct.congr b m
  let c := TensorProduct.congr b p
  have hc := tensorEvaluation_semilinear b m p ε δ h
  constructor
  · intro hi x y hxy
    apply a.symm.injective
    apply hi
    apply c.injective
    rw [hc, hc]
    change δ.lTensor C (a (a.symm x)) = δ.lTensor C (a (a.symm y))
    simpa only [LinearEquiv.apply_symm_apply] using hxy
  · intro hi x y hxy
    apply a.injective
    apply hi
    rw [← hc, ← hc, hxy]

end FLT.Mazur.Approximation
