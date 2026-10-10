/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Tensor base change of the original principal localization

The localization of the tensor algebra is the tensor product of the original
localization. Named maps retain restriction of every original function.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.PrincipalOpenTensor
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S]
  [Algebra R S] {A : Type*} [CommRing A] [Algebra R A] (x : A)

/-- The actual principal localization commutes with coefficient extension. -/
def equiv : S ⊗[R] Localization.Away x ≃ₐ[S]
    Localization.Away ((1 : S) ⊗ₜ[R] x) :=
  IsLocalization.Away.tensorProductEquivTMulRight R S x (Localization.Away x)

/-- Restriction of all original functions commutes with the tensor comparison. -/
@[simp] theorem equiv_tmul_base (s : S) (a : A) :
    equiv (R := R) S x (s ⊗ₜ[R] algebraMap A (Localization.Away x) a) =
      algebraMap (S ⊗[R] A) _ (s ⊗ₜ[R] a) :=
  IsLocalization.Away.tensorProductEquivTMulRight_tmul A x (Localization.Away x) s a

/-- The original localized algebra maps into the actual tensor principal open. -/
def coefficient : Localization.Away x →ₐ[R] Localization.Away ((1 : S) ⊗ₜ[R] x) :=
  ((equiv (R := R) S x).toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight

/-- The original restriction square survives on every element, not only on generators. -/
@[simp] theorem coefficient_base (a : A) :
    coefficient (R := R) S x (algebraMap A (Localization.Away x) a) =
      algebraMap (S ⊗[R] A) _ ((1 : S) ⊗ₜ[R] a) :=
  equiv_tmul_base S x 1 a

/-- Pure tensors of original localized functions keep their scalar multiples. -/
theorem equiv_tmul (s : S) (a : Localization.Away x) :
    equiv (R := R) S x (s ⊗ₜ[R] a) = s • coefficient (R := R) S x a := by
  change equiv (R := R) S x (s ⊗ₜ[R] a) = s • equiv (R := R) S x ((1 : S) ⊗ₜ[R] a)
  rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end FLT.Mazur.PrincipalOpenTensor
