/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Cancelling module localization against localized coefficients

If coefficients already carry the localization-ring action, a tensor with a
localized module is canonically the original-base tensor. The comparison keeps
the fraction formula and commutes with the original linear maps.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.LocalizedTensorCancellation

variable {R : Type} [CommRing R] (S : Submonoid R)
  (B : Type) [AddCommGroup B] [Module R B] [Module (Localization S) B]
  [IsScalarTower R (Localization S) B]
  (N : Type) [AddCommGroup N] [Module R N]

/-- Localized coefficients absorb the localization of the second tensor factor. -/
def tensorEquiv :
    B ⊗[Localization S] LocalizedModule S N ≃ₗ[Localization S] B ⊗[R] N :=
  (TensorProduct.congr (LinearEquiv.refl (Localization S) B)
    (LocalizedModule.equivTensorProduct S N)).trans
      (AlgebraTensorModule.cancelBaseChange R (Localization S) (Localization S) B N)

/-- A module fraction transfers its denominator to the coefficient. -/
lemma tensorEquiv_tmul_mk (b : B) (n : N) (s : S) :
    tensorEquiv S B N (b ⊗ₜ[Localization S] LocalizedModule.mk n s) =
      (Localization.mk 1 s • b) ⊗ₜ[R] n := by
  simp only [tensorEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, LocalizedModule.equivTensorProduct_apply_mk,
    AlgebraTensorModule.cancelBaseChange_tmul]

variable {N} {Q : Type} [AddCommGroup Q] [Module R Q]

/-- Cancelling localization commutes with every original differential. -/
lemma tensorEquiv_map (f : N →ₗ[R] Q)
    (x : B ⊗[Localization S] LocalizedModule S N) :
    tensorEquiv S B Q ((LocalizedModule.map S f).lTensor B x) =
      f.lTensor B (tensorEquiv S B N x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b n =>
    induction n using LocalizedModule.induction_on with
    | h n s =>
      simp only [LinearMap.lTensor_tmul, LocalizedModule.map_mk, tensorEquiv_tmul_mk]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The localized tensor kernel is the original tensor kernel with localized coefficients. -/
def kernelEquiv (f : N →ₗ[R] Q) :
    ((LocalizedModule.map S f).lTensor B).ker ≃ₗ[Localization S]
      (AlgebraTensorModule.lTensor (Localization S) B f).ker := by
  let e := tensorEquiv S B N
  refine (e.submoduleMap ((LocalizedModule.map S f).lTensor B).ker).trans
    (LinearEquiv.ofEq _ _ ?_)
  rw [Submodule.map_equiv_eq_comap_symm]
  ext y
  change (LocalizedModule.map S f).lTensor B (e.symm y) = 0 ↔ _
  rw [← (tensorEquiv S B Q).map_eq_zero_iff, tensorEquiv_map]
  change f.lTensor B (e (e.symm y)) = 0 ↔ _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- On cycles the kernel equivalence is the same fraction-preserving tensor comparison. -/
lemma kernelEquiv_val (f : N →ₗ[R] Q) (x : ((LocalizedModule.map S f).lTensor B).ker) :
    (kernelEquiv S B f x).val = tensorEquiv S B N x.val := rfl

end FLT.Mazur.LocalizedTensorCancellation
