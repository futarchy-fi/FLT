/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.KrullDimension.IntegralExtension
public import FLT.Mathlib.RingTheory.TensorProduct.IntegralMap
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Finite-type dimension is invariant under extension of the coefficient field -/

@[expose] public noncomputable section

open scoped TensorProduct

/-- An arbitrary field extension preserves the Krull dimension of a finite-type algebra.
Noether normalization remains injective by flatness and integral by tensor base change. -/
theorem ringKrullDim_tensorProduct_field (k K A : Type*) [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim (K ⊗[k] A) = ringKrullDim A := by
  nontriviality A
  obtain ⟨n, f, hf, hi⟩ := exists_integral_inj_algHom_of_fg k A
  let F : (K ⊗[k] MvPolynomial (Fin n) k) →ₐ[K] K ⊗[k] A :=
    Algebra.TensorProduct.lTensor K f
  have hF : Function.Injective F :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := K) f.toLinearMap hf
  have hI : F.IsIntegral := Algebra.TensorProduct.isIntegral_lTensor f hi
  have hdim : ringKrullDim A = ringKrullDim (MvPolynomial (Fin n) k) := by
    let := f.toRingHom.toAlgebra
    have : Algebra.IsIntegral (MvPolynomial (Fin n) k) A := ⟨hi⟩
    exact ringKrullDim_eq_of_integral_injective hf
  have hdim' : ringKrullDim (K ⊗[k] A) =
      ringKrullDim (K ⊗[k] MvPolynomial (Fin n) k) := by
    let := F.toRingHom.toAlgebra
    have : Algebra.IsIntegral (K ⊗[k] MvPolynomial (Fin n) k) (K ⊗[k] A) := ⟨hI⟩
    exact ringKrullDim_eq_of_integral_injective hF
  rw [hdim', hdim, ringKrullDim_eq_of_ringEquiv
    (MvPolynomial.algebraTensorAlgEquiv k K).toRingEquiv]
  simp [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field]

end
