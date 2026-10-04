/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.OriginTensorEquiv
public import FLT.Mathlib.RingTheory.FaithfullyFlatPresentationDescent
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Coefficient base change of a specified rational local presentation -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace MvPolynomial

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
  (K : Type*) [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] {n : ℕ}

/-- Extend a specified local presentation by its coefficient field, retaining its coordinates. -/
def originPresentationBaseChange (f : OriginLocalization k n →ₐ[k] A) :
    OriginLocalization K n →ₐ[K] K ⊗[k] A :=
  (Algebra.TensorProduct.map (AlgHom.id K K) f).comp
    (originTensorEquiv k K n).symm.toAlgHom

/-- The constructed square commutes on every original fraction. -/
@[simp] theorem originPresentationBaseChange_map (f : OriginLocalization k n →ₐ[k] A)
    (x : OriginLocalization k n) :
    originPresentationBaseChange K f (originLocalizationMap k K n x) = 1 ⊗ₜ f x := by
  change Algebra.TensorProduct.map (AlgHom.id K K) f
    (originLocalizationToTensor k K n (originLocalizationMap k K n x)) = _
  rw [originLocalizationToTensor_map]
  rfl

/-- Coefficient extension preserves surjectivity of the specified local presentation. -/
theorem originPresentationBaseChange_surjective (f : OriginLocalization k n →ₐ[k] A)
    (hf : Function.Surjective f) : Function.Surjective (originPresentationBaseChange K f) :=
  (Algebra.TensorProduct.map_surjective (AlgHom.id K K) f Function.surjective_id hf).comp
    (originTensorEquiv k K n).symm.surjective

/-- The entire kernel, rather than just a list of vanishing equations, extends correctly. -/
theorem ker_originPresentationBaseChange (f : OriginLocalization k n →ₐ[k] A)
    (hf : Function.Surjective f) :
    RingHom.ker (originPresentationBaseChange K f) =
      (RingHom.ker f).map (originLocalizationMap k K n) := by
  apply (Ideal.comap_injective_of_surjective (originTensorEquiv k K n).toRingHom
    (originTensorEquiv k K n).surjective)
  have hcomp : ((originPresentationBaseChange K f).toRingHom.comp
      (originTensorEquiv k K n).toRingHom) =
        (Algebra.TensorProduct.map (AlgHom.id k K) f).toRingHom := by
    apply RingHom.ext
    intro z
    change Algebra.TensorProduct.map (AlgHom.id K K) f
      ((originTensorEquiv k K n).symm (originTensorEquiv k K n z)) = _
    simp only [AlgEquiv.symm_apply_apply]
    rfl
  change (RingHom.ker (originPresentationBaseChange K f).toRingHom).comap _ = _
  rw [RingHom.comap_ker, hcomp]
  change RingHom.ker (Algebra.TensorProduct.map (AlgHom.id k K) f) = _
  rw [Algebra.TensorProduct.lTensor_ker f hf]
  have hm : (originLocalizationMap k K n) = (originTensorEquiv k K n).toRingHom.comp
      (Algebra.TensorProduct.includeRight : OriginLocalization k n →ₐ[k]
        K ⊗[k] OriginLocalization k n).toRingHom := by
    ext x
    simp
  rw [hm, ← Ideal.map_map]
  exact (Ideal.comap_map_of_bijective (originTensorEquiv k K n).toRingHom
    (originTensorEquiv k K n).bijective).symm

/-- Regular relations for the constructed geometric presentation reflect to the
original presentation, with no independently assumed commuting square. -/
theorem regular_presentation_of_originBaseChange
    (f : OriginLocalization k n →ₐ[k] A) (hf : Function.Surjective f)
    (rs : List (OriginLocalization k n))
    (hker : RingHom.ker (originPresentationBaseChange K f) =
      Ideal.ofList (rs.map (originLocalizationMap k K n)))
    (hreg : RingTheory.Sequence.IsRegular (OriginLocalization K n)
      (rs.map (originLocalizationMap k K n))) :
    RingTheory.Sequence.IsRegular (OriginLocalization k n) rs ∧
      ∃ e : (OriginLocalization k n ⧸ Ideal.ofList rs) ≃ₐ[k] A,
        ∀ x, e (Ideal.Quotient.mk _ x) = f x := by
  let := (originLocalizationMap k K n).toAlgebra
  have : Module.Flat (OriginLocalization k n) (OriginLocalization K n) :=
    originLocalizationMap_flat k K n
  have : IsLocalHom (algebraMap (OriginLocalization k n) (OriginLocalization K n)) :=
    originLocalizationMap_isLocalHom k K n
  have : Module.FaithfullyFlat (OriginLocalization k n) (OriginLocalization K n) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact f.exists_regular_presentation_of_faithfullyFlat_square hf
    ((originPresentationBaseChange K f).restrictScalars k)
    Algebra.TensorProduct.includeRight
    (Module.FaithfullyFlat.tensorProduct_mk_injective (A := k) (B := K) A)
    (originPresentationBaseChange_map K f) rs hker hreg

end MvPolynomial
