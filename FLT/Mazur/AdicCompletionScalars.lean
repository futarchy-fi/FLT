/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.AdicCompletion.Exactness

/-!
# Scalar change for adic completion

Completing an algebra as a module over its base ring gives the same inverse
limit as completing at the extended ideal. This comparison supplies the
algebra map on completions, including preservation of surjectivity.
-/

open AdicCompletion
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.AdicCompletionScalars
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (I : Ideal R)

/-- The quotient at each ideal power, independent of the scalar ring. -/
def quotient (n : ℕ) :
    (S ⧸ (I ^ n • ⊤ : Submodule R S)) ≃ₗ[R]
      (S ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Ideal S)) :=
  (Submodule.Quotient.equiv _ _ (.refl R S) (by
    rw [Ideal.smul_top_eq_map, Ideal.map_pow]
    simp)).trans (Submodule.Quotient.restrictScalarsEquiv R _)

theorem quotient_mk (n : ℕ) (s : S) :
    quotient I n (Submodule.Quotient.mk s) = Submodule.Quotient.mk s := rfl

theorem compatible {m n : ℕ} (h : m ≤ n)
    (x : S ⧸ (I ^ n • ⊤ : Submodule R S)) :
    transitionMap (I.map (algebraMap R S)) S h (quotient I n x) =
      quotient I m (transitionMap I S h x) := by
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/-- Pass from completion as a base module to completion at the extended ideal. -/
def forward : AdicCompletion I S →ₗ[R]
    AdicCompletion (I.map (algebraMap R S)) S :=
  { toFun := fun x ↦ ⟨fun n ↦ quotient I n (x.val n), fun h ↦ by
      rw [compatible, x.prop h]⟩
    map_add' := fun x y ↦ by ext n; exact map_add _ _ _
    map_smul' := fun r x ↦ by ext n; exact (quotient I n).map_smul r (x.val n) }

/-- View completion at the extended ideal as completion of the base module. -/
def backward : AdicCompletion (I.map (algebraMap R S)) S →ₗ[R]
    AdicCompletion I S :=
  { toFun := fun x ↦ ⟨fun n ↦ (quotient I n).symm (x.val n), fun h ↦ by
      apply (quotient I _).injective
      rw [← compatible, LinearEquiv.apply_symm_apply, x.prop h,
        LinearEquiv.apply_symm_apply]⟩
    map_add' := fun x y ↦ by ext n; exact map_add _ _ _
    map_smul' := fun r x ↦ by ext n; exact (quotient I n).symm.map_smul r (x.val n) }

/-- Restriction of scalars identifies the two inverse limits. -/
def equivalence : AdicCompletion I S ≃ₗ[R]
    AdicCompletion (I.map (algebraMap R S)) S :=
  { forward I with
    invFun := backward I
    left_inv := fun x ↦ by ext n; exact (quotient I n).symm_apply_apply _
    right_inv := fun x ↦ by ext n; exact (quotient I n).apply_symm_apply _ }

@[simp] theorem equivalence_of (s : S) :
    equivalence I (of I S s) = of (I.map (algebraMap R S)) S s := by
  ext n
  rfl

/-- The completed algebra map, viewed through restriction of scalars. -/
def algebraMapCompletion : AdicCompletion I R →ₐ[R]
    AdicCompletion (I.map (algebraMap R S)) S where
  toFun x := equivalence I (map I (Algebra.linearMap R S) x)
  map_zero' := by simp
  map_add' := by intros; simp
  map_one' := by
    change equivalence I (map I (Algebra.linearMap R S) (of I R 1)) = 1
    rw [map_of, Algebra.linearMap_apply, map_one, equivalence_of]
    rfl
  map_mul' x y := by
    ext n
    change quotient I n ((map I (Algebra.linearMap R S) (x * y)).val n) =
      quotient I n ((map I (Algebra.linearMap R S) x).val n) *
        quotient I n ((map I (Algebra.linearMap R S) y).val n)
    simp only [map_val_apply, val_mul]
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x.val n)
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (y.val n)
    rw [← ha, ← hb]
    change Submodule.Quotient.mk (algebraMap R S (a * b)) =
      Submodule.Quotient.mk (algebraMap R S a * algebraMap R S b)
    rw [map_mul]
  commutes' r := by
    change equivalence I (map I (Algebra.linearMap R S) (of I R r)) = _
    rw [map_of, equivalence_of]
    rfl

@[simp] theorem algebraMapCompletion_of (r : R) :
    algebraMapCompletion (S := S) I (of I R r) =
      of (I.map (algebraMap R S)) S (algebraMap R S r) := by
  change equivalence I (map I (Algebra.linearMap R S) (of I R r)) = _
  rw [map_of, equivalence_of]
  rfl

theorem algebraMapCompletion_surjective
    (h : Function.Surjective (algebraMap R S)) :
    Function.Surjective (algebraMapCompletion (S := S) I) :=
  (equivalence I).surjective.comp (map_surjective I h)
end FLT.Mazur.AdicCompletionScalars
