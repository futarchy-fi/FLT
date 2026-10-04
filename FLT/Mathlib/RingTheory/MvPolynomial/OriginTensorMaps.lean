/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.OriginResidue
public import Mathlib.RingTheory.Localization.Algebra

/-! # Maps comparing coefficient base change and localization at the origin -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace MvPolynomial

variable (k K : Type*) [Field k] [Field K] [Algebra k K] (n : ℕ)

/-- Extend scalars and then map the original local coordinates to the new local ring. -/
def originTensorToLocalization :
    K ⊗[k] OriginLocalization k n →ₐ[K] OriginLocalization K n :=
  Algebra.TensorProduct.lift (Algebra.ofId K (OriginLocalization K n))
    (originLocalizationAlgHom k K n) (fun _ _ ↦ Commute.all _ _)

@[simp] theorem originTensorToLocalization_tmul (c : K) (x : OriginLocalization k n) :
    originTensorToLocalization k K n (c ⊗ₜ x) =
      algebraMap K (OriginLocalization K n) c * originLocalizationMap k K n x := rfl

/-- Evaluate the tensor algebra at its rational origin. -/
def originTensorEvaluation : K ⊗[k] OriginLocalization k n →ₐ[K] K :=
  Algebra.TensorProduct.lift (AlgHom.id K K)
    ((Algebra.ofId k K).comp (originEvaluation k n)) (fun _ _ ↦ Commute.all _ _)

/-- The polynomial coordinates of the tensor algebra. -/
def originTensorCoordinates :
    MvPolynomial (Fin n) K →ₐ[K] K ⊗[k] OriginLocalization k n :=
  aeval fun i ↦ 1 ⊗ₜ algebraMap (MvPolynomial (Fin n) k) (OriginLocalization k n) (X i)

/-- The tensor algebra's augmentation evaluates all polynomial variables at zero. -/
theorem originTensorEvaluation_comp_coordinates :
    (originTensorEvaluation k K n).comp (originTensorCoordinates k K n) =
      aeval (fun _ : Fin n ↦ (0 : K)) := by
  ext i
  simp [originTensorCoordinates, originTensorEvaluation]

variable [Algebra.IsAlgebraic k K]

/-- Every polynomial denominator nonzero at the origin is invertible in the tensor algebra. -/
theorem originTensorCoordinates_isUnit
    (s : (rationalPointIdeal (fun _ : Fin n ↦ (0 : K))).primeCompl) :
    IsUnit (originTensorCoordinates k K n s) := by
  have : IsLocalRing (K ⊗[k] OriginLocalization k n) := originTensor_isLocalRing k K n
  have hker : RingHom.ker (originTensorEvaluation k K n) =
      IsLocalRing.maximalIdeal (K ⊗[k] OriginLocalization k n) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _
      (fun c ↦ ⟨algebraMap K _ c, (originTensorEvaluation k K n).commutes c⟩))
  apply IsLocalRing.notMem_maximalIdeal.mp
  rw [← hker]
  change originTensorEvaluation k K n (originTensorCoordinates k K n s) ≠ 0
  rw [← AlgHom.comp_apply, originTensorEvaluation_comp_coordinates]
  exact s.property

/-- Algebraicity makes all new denominators invertible, giving the inverse comparison map. -/
def originLocalizationToTensor :
    OriginLocalization K n →ₐ[K] K ⊗[k] OriginLocalization k n :=
  IsLocalization.liftAlgHom (f := originTensorCoordinates k K n)
    (originTensorCoordinates_isUnit k K n)

@[simp] theorem originLocalizationToTensor_algebraMap (f : MvPolynomial (Fin n) K) :
    originLocalizationToTensor k K n (algebraMap _ (OriginLocalization K n) f) =
      originTensorCoordinates k K n f := IsLocalization.lift_eq _ f

end MvPolynomial
