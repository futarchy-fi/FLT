/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.LocalRing.AlgebraicTensor
public import FLT.Mathlib.RingTheory.MvPolynomial.OriginLocalizationMap

/-! # The residue and augmentation maps at the polynomial origin -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace MvPolynomial

variable (k K : Type*) [Field k] [Field K] [Algebra k K] (n : ℕ)

/-- The residue field at the rational origin is the original coefficient field. -/
def originResidueEquiv :
    (OriginLocalization k n ⧸ IsLocalRing.maximalIdeal (OriginLocalization k n)) ≃ₐ[k] k := by
  let f : MvPolynomial (Fin n) k →ₐ[k] k := aeval (fun _ ↦ (0 : k))
  let e : (MvPolynomial (Fin n) k ⧸ rationalPointIdeal (fun _ ↦ (0 : k))) ≃ₐ[k] k :=
    Ideal.quotientKerAlgEquivOfSurjective (f := f) (fun c ↦ ⟨C c, by simp [f]⟩)
  exact ((IsLocalization.AtPrime.equivQuotMaximalIdeal
    (rationalPointIdeal (fun _ : Fin n ↦ (0 : k)))
    (OriginLocalization k n)).symm.restrictScalars k).trans e

/-- Evaluation at the origin extends to its local ring. -/
def originEvaluation : OriginLocalization k n →ₐ[k] k :=
  (originResidueEquiv k n).toAlgHom.comp (Ideal.Quotient.mkₐ k _)

@[simp] theorem originEvaluation_X (i : Fin n) :
    originEvaluation k n
      (algebraMap (MvPolynomial (Fin n) k) (OriginLocalization k n) (X i)) = 0 := by
  have h : algebraMap (MvPolynomial (Fin n) k) (OriginLocalization k n) (X i) ∈
      IsLocalRing.maximalIdeal (OriginLocalization k n) := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (OriginLocalization k n)
      (rationalPointIdeal (fun _ : Fin n ↦ (0 : k)))]
    simp [rationalPointIdeal]
  change originResidueEquiv k n (Ideal.Quotient.mk _ _) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

/-- Coefficient extension between local rings is compatible with the original field. -/
def originLocalizationAlgHom : OriginLocalization k n →ₐ[k] OriginLocalization K n where
  __ := originLocalizationMap k K n
  commutes' r := by
    change originLocalizationMap k K n (algebraMap k (OriginLocalization k n) r) = _
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin n) k) (OriginLocalization k n),
      originLocalizationMap_algebraMap]
    change algebraMap (MvPolynomial (Fin n) K) (OriginLocalization K n)
      (map (algebraMap k K) (C r)) = _
    rw [map_C]
    rfl

/-- The polynomial local ring stays local after algebraic coefficient extension. -/
theorem originTensor_isLocalRing [Algebra.IsAlgebraic k K] :
    IsLocalRing (K ⊗[k] OriginLocalization k n) := by
  have : IsLocalRing (OriginLocalization k n ⊗[k] K) :=
    IsLocalRing.tensor_isLocalRing (originResidueEquiv k n)
  exact (Algebra.TensorProduct.comm k (OriginLocalization k n) K).toRingEquiv.isLocalRing

end MvPolynomial
