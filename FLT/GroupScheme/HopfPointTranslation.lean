/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfShear

/-! # Translation by a rational point, with its original comultiplication formula -/

@[expose] public noncomputable section

open scoped TensorProduct
open Algebra.TensorProduct

namespace HopfAlgebra

variable {k A : Type*} [Field k] [CommRing A] [HopfAlgebra k A]

/-- Translation is the shear automorphism specialized at the chosen point. -/
def pointTranslation (χ : A →ₐ[k] k) : A ≃ₐ[k] A := by
  let : Algebra A k := χ.toRingHom.toAlgebra
  let : IsScalarTower k A k := IsScalarTower.of_algHom χ
  let e := (cancelBaseChange k A k k A).trans (Algebra.TensorProduct.lid k A)
  exact e.symm.trans ((congr (AlgEquiv.refl : k ≃ₐ[k] k)
    (shearEquivOverLeft (R := k) (A := A))).trans e)

/-- Translation evaluates the left tensor factor of the original comultiplication. -/
theorem pointTranslation_apply (χ : A →ₐ[k] k) (a : A) :
    pointTranslation χ a = Algebra.TensorProduct.lid k A
      (Algebra.TensorProduct.map χ (AlgHom.id k A) (Coalgebra.comul (R := k) a)) := by
  let : Algebra A k := χ.toRingHom.toAlgebra
  let : IsScalarTower k A k := IsScalarTower.of_algHom χ
  change Algebra.TensorProduct.lid k A (cancelBaseChange k A k k A
    ((congr (AlgEquiv.refl : k ≃ₐ[k] k) (shearEquivOverLeft (R := k) (A := A)))
      ((cancelBaseChange k A k k A).symm ((Algebra.TensorProduct.lid k A).symm a)))) = _
  simp only [lid_symm_apply, cancelBaseChange_symm_tmul, congr_apply, map_tmul,
    AlgEquiv.refl_toAlgHom, AlgHom.id_apply]
  change Algebra.TensorProduct.lid k A (cancelBaseChange k A k k A
    (1 ⊗ₜ[A] shearEquiv (R := k) (A := A) (1 ⊗ₜ[k] a))) = _
  rw [shearEquiv_tmul]
  simp only [← Algebra.TensorProduct.one_def, one_mul]
  induction Coalgebra.comul (R := k) a using TensorProduct.inductionOn with
  | tmul b c =>
    simpa only [cancelBaseChange_tmul, map_tmul, AlgHom.id_apply, lid_tmul,
      Algebra.smul_def, mul_one] using
      congrArg (fun z : k ↦ algebraMap k A z * c) (show algebraMap A k b = χ b from rfl)
  | add b c hb hc => simp only [TensorProduct.tmul_add, map_add, hb, hc]

/-- Evaluating a translated function at the identity gives the chosen point. -/
theorem counit_comp_pointTranslation (χ : A →ₐ[k] k) :
    (Bialgebra.counitAlgHom k A).comp (pointTranslation χ).toAlgHom = χ := by
  let ε := Bialgebra.counitAlgHom k A
  have h : ε.comp ((Algebra.TensorProduct.lid k A).toAlgHom.comp
      (Algebra.TensorProduct.map χ (AlgHom.id k A))) =
      χ.comp ((Algebra.TensorProduct.rid k k A).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id k A) ε)) := by
    apply AlgHom.toLinearMap_injective
    ext a b
    simp [ε, Algebra.smul_def, mul_comm]
  ext a
  change ε (pointTranslation χ a) = χ a
  rw [pointTranslation_apply]
  have hh := AlgHom.congr_fun h (Coalgebra.comul (R := k) a)
  change ε (Algebra.TensorProduct.lid k A (Algebra.TensorProduct.map χ (AlgHom.id k A)
    (Coalgebra.comul a))) = _ at hh
  rw [hh]
  change χ (TensorProduct.rid k A
    ((Coalgebra.counit (R := k)).lTensor A (Coalgebra.comul a))) = _
  rw [Coalgebra.lTensor_counit_comul]
  simp

end HopfAlgebra
