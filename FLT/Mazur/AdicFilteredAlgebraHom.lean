/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Extending a filtered algebra map through source completion

A map from the original algebra to a completed algebra extends when it
respects every ideal-power filtration. The extension is constructed from
quotient maps and retains the original map on every original element.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicFilteredAlgebraHom

open AdicCompletion

set_option backward.isDefEq.respectTransparency false

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- Evaluation of a completed algebra respects the quotient transition maps. -/
theorem factor_eval (I : Ideal A) {m n : ℕ} (h : m ≤ n) (x : AdicCompletion I A) :
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h) (evalₐ I n x) = evalₐ I m x := by
  apply AdicCompletion.induction_on I A x
  intro a
  simpa only [evalₐ_mk, Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk]
    using AdicCompletion.Ideal.mk_eq_mk I h a

variable (I : Ideal A) (J : Ideal B) (f : A →ₐ[R] AdicCompletion J B)
  (hf : ∀ n, I ^ n ≤ RingHom.ker (((evalₐ J n).restrictScalars R).comp f).toRingHom)

/-- The filtration-preserving map descends to each original quotient. -/
def quotient (n : ℕ) : A ⧸ I ^ n →ₐ[R] B ⧸ J ^ n :=
  Ideal.Quotient.liftₐ (I ^ n) (((evalₐ J n).restrictScalars R).comp f)
    (fun _ hx ↦ hf n hx)

/-- Quotient descent retains original representatives. -/
@[simp] theorem quotient_mk (n : ℕ) (a : A) :
    quotient I J f hf n (Ideal.Quotient.mk (I ^ n) a) = evalₐ J n (f a) := rfl

/-- The quotient maps agree along the two adic inverse systems. -/
theorem compatible {m n : ℕ} (h : m ≤ n) (x : A ⧸ I ^ n) :
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h) (quotient I J f hf n x) =
      quotient I J f hf m (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h) x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact factor_eval (R := R) J h (f a)

/-- The extended algebra map, constructed by the inverse-limit universal property. -/
def extend : AdicCompletion I A →ₐ[R] AdicCompletion J B :=
  AdicCompletion.liftAlgHom J
    (fun n ↦ (quotient I J f hf n).comp ((evalₐ I n).restrictScalars R))
    (fun {m n} h ↦ by
      ext x
      change Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h)
        (quotient I J f hf n (evalₐ I n x)) = quotient I J f hf m (evalₐ I m x)
      rw [compatible I J f hf h, factor_eval I h])

/-- Each finite-order component of the extension is the constructed quotient map. -/
theorem eval_extend (n : ℕ) (x : AdicCompletion I A) :
    evalₐ J n (extend I J f hf x) = quotient I J f hf n (evalₐ I n x) :=
  AdicCompletion.evalₐ_liftAlgHom _ _ _ _ _

/-- The continuous extension recovers the prescribed map on the original algebra. -/
@[simp] theorem extend_of (a : A) :
    extend I J f hf (AdicCompletion.of I A a) = f a := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [eval_extend]
  rfl

end FLT.Mazur.AdicFilteredAlgebraHom
