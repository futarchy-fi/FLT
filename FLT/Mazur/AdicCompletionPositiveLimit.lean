/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletionAlgEquiv

/-!
# Completion as the limit of the positive-power quotients

Infinitesimal stages are numbered from the first power of the ideal.
The omitted zeroth quotient is redundant; the compatible positive-power
sections reconstruct the completion with their prescribed evaluations.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicCompletionPositiveLimit

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- Compatible sections on all positive-power thickenings. -/
def sections : Subring (∀ n : ℕ, A ⧸ I ^ (n + 1)) where
  carrier := {x | ∀ {m n : ℕ} (hmn : m ≤ n),
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1)) (x n) = x m}
  zero_mem' := by intro m n hmn; exact map_zero _
  one_mem' := by intro m n hmn; exact map_one _
  add_mem' := by intro x y hx hy m n hmn; simp only [Pi.add_apply, map_add, hx hmn, hy hmn]
  mul_mem' := by intro x y hx hy m n hmn; simp only [Pi.mul_apply, map_mul, hx hmn, hy hmn]
  neg_mem' := by intro x hx m n hmn; simp only [Pi.neg_apply, map_neg, hx hmn]

/-- Evaluation on a positive-power thickening. -/
def projection (n : ℕ) : sections I →+* A ⧸ I ^ (n + 1) where
  toFun x := x.val n
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A formal element gives its actual compatible quotient sections. -/
def toSections : AdicCompletion I A →+* sections I where
  toFun x := ⟨fun n ↦ AdicCompletion.evalₐ I (n + 1) x,
    fun hmn ↦ AdicCompletionAlgEquiv.eval_compatible (K := A) I
      (Nat.add_le_add_right hmn 1) x⟩
  map_one' := Subtype.ext (funext fun n ↦ map_one (AdicCompletion.evalₐ I (n + 1)))
  map_mul' x y := Subtype.ext (funext fun n ↦ map_mul (AdicCompletion.evalₐ I (n + 1)) x y)
  map_zero' := Subtype.ext (funext fun n ↦ map_zero (AdicCompletion.evalₐ I (n + 1)))
  map_add' x y := Subtype.ext (funext fun n ↦ map_add (AdicCompletion.evalₐ I (n + 1)) x y)

/-- Recover the n-th quotient from the next positive-power quotient. -/
def atPower (n : ℕ) : sections I →+* A ⧸ I ^ n :=
  (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n))).comp (projection I n)

/-- The recovered quotients are compatible, including the zeroth quotient. -/
theorem atPower_compatible {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow I hmn).comp (atPower I n) = atPower I m := by
  ext x
  change Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n)) (x.val n)) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ m)) (x.val m)
  rw [← x.property hmn, Ideal.Quotient.factor_comp_apply, Ideal.Quotient.factor_comp_apply]

/-- Reconstruct a formal element from its positive-power sections. -/
def fromSections : sections I →+* AdicCompletion I A :=
  AdicCompletion.liftRingHom I (atPower I) (atPower_compatible I)

/-- The reconstructed element retains every prescribed positive-power section. -/
@[simp] theorem eval_fromSections (n : ℕ) (x : sections I) :
    AdicCompletion.evalₐ I (n + 1) (fromSections I x) = x.val n := by
  rw [fromSections, AdicCompletion.evalₐ_liftRingHom]
  exact x.property (Nat.le_succ n)

/-- The positive-power sections determine the entire adic completion. -/
def equivalence : AdicCompletion I A ≃+* sections I :=
  { toSections I with
    invFun := fromSections I
    left_inv := fun x ↦ by
      apply AdicCompletion.ext_evalₐ
      intro n
      rw [fromSections, AdicCompletion.evalₐ_liftRingHom]
      exact AdicCompletionAlgEquiv.eval_compatible (K := A) I (Nat.le_succ n) x
    right_inv := fun x ↦ by
      apply Subtype.ext
      funext n
      exact eval_fromSections I n x }

end FLT.Mazur.AdicCompletionPositiveLimit
