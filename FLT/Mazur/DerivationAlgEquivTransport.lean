/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivations under an algebra equivalence with transported module actions

Precomposition preserves the original base ring and the specified target
module. Compatibility is only the equality of the two scalar actions.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.DerivationAlgEquivTransport

variable {R A B N : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [AddCommGroup N]
  [Module R N] [Module A N] [Module B N]

/-- Pull back a derivation through an algebra map compatible with the target action. -/
def pullback (f : A →ₐ[R] B) (hf : ∀ a (x : N), f a • x = a • x)
    (d : Derivation R B N) : Derivation R A N where
  toLinearMap := d.toLinearMap.comp f.toLinearMap
  map_one_eq_zero' := by simp
  leibniz' a b := by
    change d (f (a * b)) = a • d (f b) + b • d (f a)
    rw [map_mul, d.leibniz, hf, hf]

/-- Pullback evaluates by the original algebra map. -/
@[simp] theorem pullback_apply (f : A →ₐ[R] B) (hf : ∀ a (x : N), f a • x = a • x)
    (d : Derivation R B N) (a : A) : pullback f hf d a = d (f a) := rfl

/-- An algebra equivalence gives an equivalence of derivations with the same target. -/
def equiv (e : A ≃ₐ[R] B) (he : ∀ a (x : N), e a • x = a • x) :
    Derivation R B N ≃ Derivation R A N where
  toFun := pullback e.toAlgHom he
  invFun := pullback e.symm.toAlgHom (fun b x ↦ by
    change e.symm b • x = b • x
    simpa only [e.apply_symm_apply] using (he (e.symm b) x).symm)
  left_inv d := by ext b : 1; exact congrArg d (e.apply_symm_apply b)
  right_inv d := by ext a : 1; exact congrArg d (e.symm_apply_apply a)

/-- The derivation equivalence is precomposition on every section. -/
@[simp] theorem equiv_apply (e : A ≃ₐ[R] B) (he : ∀ a (x : N), e a • x = a • x)
    (d : Derivation R B N) (a : A) : equiv e he d a = d (e a) := rfl

end FLT.Mazur.DerivationAlgEquivTransport
