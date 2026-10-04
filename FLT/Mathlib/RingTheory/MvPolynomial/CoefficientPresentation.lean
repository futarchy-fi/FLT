/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Coefficient extension of a specified polynomial presentation -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace MvPolynomial

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
  (K : Type*) [Field K] [Algebra k K] {n : ℕ}

/-- Extend the specified presentation, keeping its polynomial coordinates. -/
def coefficientPresentation (f : MvPolynomial (Fin n) k →ₐ[k] A) :
    MvPolynomial (Fin n) K →ₐ[K] K ⊗[k] A :=
  (Algebra.TensorProduct.map (AlgHom.id K K) f).comp
    (algebraTensorAlgEquiv k K).symm.toAlgHom

@[simp] theorem coefficientPresentation_map (f : MvPolynomial (Fin n) k →ₐ[k] A)
    (q : MvPolynomial (Fin n) k) :
    coefficientPresentation K f (map (algebraMap k K) q) = 1 ⊗ₜ f q := by
  simp [coefficientPresentation]

@[simp] theorem coefficientPresentation_X (f : MvPolynomial (Fin n) k →ₐ[k] A) (i : Fin n) :
    coefficientPresentation K f (X i) = 1 ⊗ₜ f (X i) := by
  simp [coefficientPresentation]

/-- Scalar extension preserves surjectivity of the given presentation. -/
theorem coefficientPresentation_surjective (f : MvPolynomial (Fin n) k →ₐ[k] A)
    (hf : Function.Surjective f) : Function.Surjective (coefficientPresentation K f) :=
  (Algebra.TensorProduct.map_surjective (AlgHom.id K K) f Function.surjective_id hf).comp
    (algebraTensorAlgEquiv k K).symm.surjective

/-- The geometric kernel is exactly the coefficient extension of the original kernel. -/
theorem ker_coefficientPresentation (f : MvPolynomial (Fin n) k →ₐ[k] A)
    (hf : Function.Surjective f) :
    RingHom.ker (coefficientPresentation K f) =
      (RingHom.ker f).map (map (algebraMap k K)) := by
  let e := algebraTensorAlgEquiv (σ := Fin n) k K
  apply Ideal.comap_injective_of_surjective e.toRingHom e.surjective
  have hcomp : (coefficientPresentation K f).toRingHom.comp e.toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id k K) f).toRingHom := by
    apply RingHom.ext
    intro z
    change Algebra.TensorProduct.map (AlgHom.id K K) f (e.symm (e z)) = _
    rw [e.symm_apply_apply]
    rfl
  change (RingHom.ker (coefficientPresentation K f).toRingHom).comap _ = _
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
