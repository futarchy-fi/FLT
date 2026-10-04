/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Base change of a polynomial presentation over an arbitrary ring -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace MvPolynomial

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
  (K : Type*) [CommRing K] [Algebra k K] {n : ℕ}

/-- Extend the specified presentation, keeping its polynomial coordinates. -/
def baseChangePresentation (f : MvPolynomial (Fin n) k →ₐ[k] A) :
    MvPolynomial (Fin n) K →ₐ[K] K ⊗[k] A :=
  (Algebra.TensorProduct.map (AlgHom.id K K) f).comp
    (algebraTensorAlgEquiv k K).symm.toAlgHom

@[simp] theorem baseChangePresentation_map (f : MvPolynomial (Fin n) k →ₐ[k] A)
    (q : MvPolynomial (Fin n) k) :
    baseChangePresentation K f (map (algebraMap k K) q) = 1 ⊗ₜ f q := by
  simp [baseChangePresentation]

@[simp] theorem baseChangePresentation_X (f : MvPolynomial (Fin n) k →ₐ[k] A) (i : Fin n) :
    baseChangePresentation K f (X i) = 1 ⊗ₜ f (X i) := by
  simp [baseChangePresentation]

/-- Scalar extension preserves surjectivity of the given presentation. -/
theorem baseChangePresentation_surjective (f : MvPolynomial (Fin n) k →ₐ[k] A)
    (hf : Function.Surjective f) : Function.Surjective (baseChangePresentation K f) :=
  (Algebra.TensorProduct.map_surjective (AlgHom.id K K) f Function.surjective_id hf).comp
    (algebraTensorAlgEquiv k K).symm.surjective

/-- The base-changed kernel is exactly the coefficient extension of the original kernel. -/
theorem ker_baseChangePresentation (f : MvPolynomial (Fin n) k →ₐ[k] A)
    (hf : Function.Surjective f) :
    RingHom.ker (baseChangePresentation K f) =
      (RingHom.ker f).map (map (algebraMap k K)) := by
  let e := algebraTensorAlgEquiv (σ := Fin n) k K
  apply Ideal.comap_injective_of_surjective e.toRingHom e.surjective
  have hcomp : (baseChangePresentation K f).toRingHom.comp e.toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id k K) f).toRingHom := by
    apply RingHom.ext
    intro z
    change Algebra.TensorProduct.map (AlgHom.id K K) f (e.symm (e z)) = _
    rw [e.symm_apply_apply]
    rfl
  change (RingHom.ker (baseChangePresentation K f).toRingHom).comap _ = _
  rw [RingHom.comap_ker, hcomp]
  change RingHom.ker (Algebra.TensorProduct.map (AlgHom.id k K) f) = _
  rw [Algebra.TensorProduct.lTensor_ker f hf]
  have hm : map (σ := Fin n) (algebraMap k K) = e.toRingHom.comp
      (Algebra.TensorProduct.includeRight : MvPolynomial (Fin n) k →ₐ[k]
        K ⊗[k] MvPolynomial (Fin n) k).toRingHom := by
    apply RingHom.ext
    intro q
    simp [e]
  rw [hm, ← Ideal.map_map]
  exact (Ideal.comap_map_of_bijective e.toRingHom e.bijective).symm

end MvPolynomial
