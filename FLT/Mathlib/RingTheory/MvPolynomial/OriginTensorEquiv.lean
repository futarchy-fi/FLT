/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.OriginTensorMaps

/-! # Algebraic coefficient extension commutes with localization at the origin -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace MvPolynomial

variable (k K : Type*) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] (n : ℕ)

/-- Localizing after extending coefficients gives back every new local coordinate. -/
theorem originTensorToLocalization_comp_inverse :
    (originTensorToLocalization k K n).comp (originLocalizationToTensor k K n) =
      AlgHom.id K (OriginLocalization K n) := by
  apply IsLocalization.algHom_ext (rationalPointIdeal (fun _ : Fin n ↦ (0 : K))).primeCompl
  ext i
  change originTensorToLocalization k K n (originLocalizationToTensor k K n
    (algebraMap (MvPolynomial (Fin n) K) (OriginLocalization K n) (X i))) =
      algebraMap (MvPolynomial (Fin n) K) (OriginLocalization K n) (X i)
  simp [originTensorCoordinates]

/-- The inverse comparison retains the tensor's original local-ring factor. -/
theorem originLocalizationToTensor_map (x : OriginLocalization k n) :
    originLocalizationToTensor k K n (originLocalizationMap k K n x) = 1 ⊗ₜ x := by
  have h : ((originLocalizationToTensor k K n).restrictScalars k).comp
      (originLocalizationAlgHom k K n) =
        (Algebra.TensorProduct.includeRight : OriginLocalization k n →ₐ[k]
          K ⊗[k] OriginLocalization k n) := by
    apply IsLocalization.algHom_ext (rationalPointIdeal (fun _ : Fin n ↦ (0 : k))).primeCompl
    ext i
    change originLocalizationToTensor k K n (originLocalizationMap k K n
      (algebraMap (MvPolynomial (Fin n) k) (OriginLocalization k n) (X i))) =
      1 ⊗ₜ algebraMap (MvPolynomial (Fin n) k) (OriginLocalization k n) (X i)
    simp [originTensorCoordinates]
  exact DFunLike.congr_fun h x

/-- Both comparison maps are inverse on the coefficient tensor algebra. -/
theorem originLocalizationToTensor_comp_inverse :
    (originLocalizationToTensor k K n).comp (originTensorToLocalization k K n) =
      AlgHom.id K (K ⊗[k] OriginLocalization k n) := by
  ext x
  simp [originLocalizationToTensor_map]

/-- Extending an algebraic coefficient field commutes with the rational local ring. -/
def originTensorEquiv : K ⊗[k] OriginLocalization k n ≃ₐ[K] OriginLocalization K n :=
  AlgEquiv.ofAlgHom (originTensorToLocalization k K n) (originLocalizationToTensor k K n)
    (originTensorToLocalization_comp_inverse k K n) (originLocalizationToTensor_comp_inverse k K n)

/-- The comparison retains coefficients and every fraction in the original local ring. -/
@[simp] theorem originTensorEquiv_tmul (c : K) (x : OriginLocalization k n) :
    originTensorEquiv k K n (c ⊗ₜ x) =
      algebraMap K (OriginLocalization K n) c * originLocalizationMap k K n x := rfl

end MvPolynomial
