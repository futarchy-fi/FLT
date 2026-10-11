/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletionScalars

/-!
# Changing the scalar ring of a module completion

The filtrations induced by an ideal and its extension agree on every module.
Their inverse limits therefore agree, compatibly with the completed scalar action.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicModuleScalarChange

open AdicCompletion

set_option backward.isDefEq.respectTransparency false

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (I : Ideal R)

/-- Change the scalar ring in each quotient of the adic filtration. -/
def quotient (n : ℕ) :
    (M ⧸ (I ^ n • ⊤ : Submodule R M)) ≃ₗ[R]
      (M ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S M)) :=
  (Submodule.Quotient.equiv _ _ (.refl R M) (by
    rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq]
    simp)).trans (Submodule.Quotient.restrictScalarsEquiv R _)

/-- The quotient comparison retains original representatives. -/
@[simp] theorem quotient_mk (n : ℕ) (m : M) :
    quotient (S := S) I n (Submodule.Quotient.mk m) = Submodule.Quotient.mk m := rfl

/-- Scalar change respects the transition maps of the inverse system. -/
theorem compatible {m n : ℕ} (h : m ≤ n)
    (x : M ⧸ (I ^ n • ⊤ : Submodule R M)) :
    transitionMap (I.map (algebraMap R S)) M h (quotient (S := S) I n x) =
      quotient (S := S) I m (transitionMap I M h x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/-- The two scalar descriptions give the same completed module. -/
def equiv : AdicCompletion I M ≃ₗ[R] AdicCompletion (I.map (algebraMap R S)) M where
  toFun x := ⟨fun n ↦ quotient (S := S) I n (x.val n), fun h ↦ by
    rw [compatible, x.prop h]⟩
  invFun x := ⟨fun n ↦ (quotient (S := S) I n).symm (x.val n), fun h ↦ by
    apply (quotient (S := S) I _).injective
    rw [← compatible, LinearEquiv.apply_symm_apply, x.prop h,
      LinearEquiv.apply_symm_apply]⟩
  left_inv x := by ext n; exact (quotient (S := S) I n).symm_apply_apply _
  right_inv x := by ext n; exact (quotient (S := S) I n).apply_symm_apply _
  map_add' x y := by ext n; exact map_add _ _ _
  map_smul' r x := by ext n; exact (quotient (S := S) I n).map_smul r (x.val n)

/-- Original module elements are unchanged by scalar change. -/
@[simp] theorem equiv_of (m : M) :
    equiv (S := S) I (of I M m) = of (I.map (algebraMap R S)) M m := by
  ext n
  rfl

/-- Scalar change preserves multiplication by completed base scalars. -/
theorem equiv_smul (r : AdicCompletion I R) (x : AdicCompletion I M) :
    equiv (S := S) I (r • x) =
      AdicCompletionScalars.algebraMapCompletion (S := S) I r • equiv (S := S) I x := by
  ext n
  change quotient (S := S) I n (r.val n • x.val n) =
    AdicCompletionScalars.quotient I n
      ((map I (Algebra.linearMap R S) r).val n) • quotient (S := S) I n (x.val n)
  rw [map_val_apply]
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (r.val n)
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
  rw [← ha, ← hm]
  change Submodule.Quotient.mk (a • m) =
    Submodule.Quotient.mk (algebraMap R S a • m)
  rw [algebraMap_smul]

end FLT.Mazur.AdicModuleScalarChange
